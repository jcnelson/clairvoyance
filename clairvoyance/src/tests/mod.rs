// Copyright (C) 2026 Trust Machines
// 
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
// 
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use std::collections::HashMap;
use std::collections::HashSet;

use clarity::vm::contexts::ExecutionState;
use clarity::vm::contexts::InvocationContext;
use clarity::vm::contexts::LocalContext;
use clarity::vm::contexts::OwnedEnvironment;
use clarity::vm::database::MemoryBackingStore;
use clarity::vm::types::QualifiedContractIdentifier;
use clarity::vm::SymbolicExpression;
use clarity::vm::ClarityVersion;
use clarity::vm::ValueRef;
use clarity::vm::ExecutionResult;
use clarity::vm::ContractContext;
use clarity::vm::ast;
use clarity::vm::eval_all;
use clarity::vm::errors::ClarityEvalError;
use clarity_types::types::StandardPrincipalData;
use clarity_types::types::PrincipalData;
use clarity_types::ClarityName;
use clarity_types::types::TupleData;
use clarity_types::types::signatures::{TypeSignature as TS, ListTypeData, TupleTypeSignature};
use clarity_types::types::SequenceSubtype;
use clarity_types::types::StringSubtype;

use stacks_common::consts::CHAIN_ID_MAINNET;
use stacks_common::types::StacksEpochId;
use stacks_common::address::C32_ADDRESS_VERSION_MAINNET_SINGLESIG;

use clarity::vm::EvalHook;
use clarity_types::Value;

use serde_json;

use crate::sym::{Sym, SymOp, Symbex, SymId, Predicate, Continuation, FullName, Callgraph};
use crate::core::Error;
use crate::core::DEFAULT_STACKS_EPOCH;
use crate::core::ProofFailures;
use crate::sym::command::Halt;

pub mod command;

fn default_contract_id() -> QualifiedContractIdentifier {
    make_contract_id("contract")
}

fn make_contract_id(name: &str) -> QualifiedContractIdentifier {
    QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), name.try_into().unwrap())
}

fn f() -> Box<SymOp> { Box::new(SymOp::False()) }
fn t() -> Box<SymOp> { Box::new(SymOp::True()) }
fn valu(x: u128) -> Value { Value::UInt(x) }
fn vali(x: i128) -> Value { Value::Int(x) }
fn valb(x: bool) -> Value { Value::Bool(x) }
fn vall(x: Vec<Value>) -> Value { Value::cons_list(x, &DEFAULT_STACKS_EPOCH).unwrap() }

fn ci(x: i128) -> Box<SymOp> { Box::new(SymOp::Constant(Value::Int(x))) }
fn cu(x: u128) -> Box<SymOp> { Box::new(SymOp::Constant(Value::UInt(x))) }
fn cb(x: bool) -> Box<SymOp> { Box::new(SymOp::Constant(Value::Bool(x))) }
fn cp(x: PrincipalData) -> Box<SymOp> { Box::new(SymOp::Constant(Value::Principal(x))) }
fn ct(fields: Vec<(&str, Value)>) -> Box<SymOp> {
    let consts : Vec<(ClarityName, Value)> = fields
        .into_iter()
        .map(|(name, v)| {
            (name.try_into().unwrap(), v)
        })
    .collect();

    Box::new(SymOp::Constant(Value::Tuple(TupleData::from_data(consts).unwrap())))
}
fn cl(fields: Vec<Value>) -> Box<SymOp> { Box::new(SymOp::Constant(vall(fields))) }
fn co(val: Value) -> Box<SymOp> { Box::new(SymOp::Constant(Value::some(val).unwrap())) }
fn cok(val: Value) -> Box<SymOp> { Box::new(SymOp::Constant(Value::okay(val).unwrap())) }
fn cerr(val: Value) -> Box<SymOp> { Box::new(SymOp::Constant(Value::error(val).unwrap())) }
fn csb(val: Vec<u8>) -> Box<SymOp> { Box::new(SymOp::Constant(Value::buff_from(val).unwrap())) }
fn cssa(val: &str) -> Box<SymOp> { Box::new(SymOp::Constant(Value::string_ascii_from_bytes(val.as_bytes().to_vec()).unwrap())) }
fn cssu(val: &str) -> Box<SymOp> { Box::new(SymOp::Constant(Value::string_utf8_from_string_utf8_literal(val.to_string()).unwrap())) }

fn si(name: &str) -> Sym { Sym::Int(name.into()) }
fn su(name: &str) -> Sym { Sym::UInt(name.into()) }
fn sb(name: &str) -> Sym { Sym::Bool(name.into()) }
fn sl(name: &str, ts: TS, len: u32) -> Sym { Sym::Sequence(name.into(), SequenceSubtype::ListType(ListTypeData::new_list(ts, len).unwrap())) }
fn so(name: &str, ts: TS) -> Sym { Sym::Optional(name.into(), ts) }
fn sr(name: &str, ok_ts: TS, err_ts: TS) -> Sym { Sym::Response(name.into(), ok_ts, err_ts) }

fn vi(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Int(name.into()))) }
fn vu(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::UInt(name.into()))) }
fn vb(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Bool(name.into()))) }
fn vo(name: &str, ts: TS) -> Box<SymOp> { Box::new(SymOp::Variable(so(name, ts))) }
fn vr(name: &str, ts_ok: TS, ts_err: TS) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Response(name.into(), ts_ok, ts_err))) }
fn vt(name: &str, field_ts: Vec<(&str, TS)>) -> Box<SymOp> {
    let fields : Vec<(ClarityName, TS)> = field_ts
        .into_iter()
        .map(|(name, ts)| {
            (name.try_into().unwrap(), ts)
        })
    .collect();

    Box::new(SymOp::Variable(Sym::Tuple(name.into(), fields.try_into().unwrap())))
}
fn vl(name: &str, ts: TS, len: u32) -> Box<SymOp> { Box::new(SymOp::Variable(sl(name, ts, len))) }
fn vp(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Principal(name.into()))) }
fn vsb(name: &str, len: u32) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Sequence(name.into(), SequenceSubtype::BufferType(len.try_into().unwrap())))) }
fn vssa(name: &str, len: u32) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Sequence(name.into(), SequenceSubtype::StringType(StringSubtype::ASCII(len.try_into().unwrap()))))) }

fn add(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Add(ops)) }
fn add2(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { add(vec![op1, op2]) }
fn sub(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Subtract(ops)) }
fn sub2(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { sub(vec![op1, op2]) }
fn mul(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Multiply(ops)) }
fn mul2(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { mul(vec![op1, op2]) }
fn div(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Divide(ops)) }
fn rem(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Modulo(op1, op2)) }
fn pow(base: Box<SymOp>, exp: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Power(base, exp)) }
fn log2(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Log2(op)) }
fn concat(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Concat(ops)) }
fn and(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::And(ops)) }
fn or(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Or(ops)) }
fn not(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Not(op)) }
fn gt(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Greater(op1, op2)) }
fn geq(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Geq(op1, op2)) }
fn lt(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Less(op1, op2)) }
fn leq(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Leq(op1, op2)) }
fn eq(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Equals(vec![op1, op2])) }
fn eqs(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Equals(ops)) }
fn tcons(fields: Vec<(&str, Box<SymOp>)>) -> Box<SymOp> { Box::new(SymOp::TupleCons(fields.into_iter().map(|(name, op)| (name.try_into().unwrap(), op)).collect())) }
fn tget(name: &str, op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::TupleGet(name.try_into().unwrap(), op)) }
fn tmerge(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::TupleMerge(op1, op2)) }
fn ok(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::ConsOkay(op)) }
fn err(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::ConsError(op)) }
fn some(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::ConsSome(op)) }
fn none() -> Box<SymOp> { Box::new(SymOp::none()) }
fn is_ok(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::IsOkay(op)) }
fn is_err(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::IsErr(op)) }
fn is_some(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::IsSome(op)) }
fn is_none(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::IsNone(op)) }
fn unwrap_panic(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::UnwrapPanic(op)) }
fn unwrap_err_panic(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::UnwrapErrPanic(op)) }
fn panic() -> Box<SymOp> { Box::new(SymOp::Panic) }
fn lcons(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::ListCons(items)) }
fn llen(item: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Len(item)) }
fn elat(seq: Box<SymOp>, index: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::ElementAt(seq, index)) }
fn bitand(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::BitwiseAnd(items)) }
fn bitor(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::BitwiseOr(items)) }
fn bitxor(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::BitwiseXor(items)) }
fn var_get(s: Sym) -> Box<SymOp> { lv(s.clone().id(), Box::new(SymOp::Variable(s))) }
fn fq_var_get(c: &QualifiedContractIdentifier, s: Sym) -> Box<SymOp> { fqlv(c, s.clone().id(), Box::new(SymOp::Variable(s))) }
fn lv(n: &str, s: Box<SymOp>) -> Box<SymOp> { fqlv(&default_contract_id(), n, s) }
fn fqlv(c: &QualifiedContractIdentifier, n: &str, s: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::LoadedDataVariable(FullName::try_from(format!("{}.{n}", c)).unwrap(), s)) }
fn lm(n: &str, key: Box<SymOp>, value: Box<SymOp>) -> Box<SymOp> { fqlm(&default_contract_id(), n, key, value) }
fn fqlm(c: &QualifiedContractIdentifier, n: &str, key: Box<SymOp>, value: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::LoadedMapEntry(FullName::try_from(format!("{}.{n}", c)).unwrap(), key, Some(value))) }
fn map_get(n: &str, key: Box<SymOp>) -> Box<SymOp> { fq_map_get(&default_contract_id(), n, key) }
fn fq_map_get(c: &QualifiedContractIdentifier, n: &str, key: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::LoadedMapEntry(FullName::try_from(format!("{}.{n}", c)).unwrap(), key, None)) }
fn secp256k1_recover(mh: Box<SymOp>, sig: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Secp256k1Recover(mh, sig)) }
fn fcall(name: &str, args: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::FunctionCall(name.try_into().unwrap(), args)) }

fn pt() -> Box<Predicate> { Box::new(Predicate::True) }
fn pf() -> Box<Predicate> { Box::new(Predicate::False) }
fn pi(s: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::Identity(*s)) }
fn pand(ps: Vec<Box<Predicate>>) -> Box<Predicate> { Box::new(Predicate::And(ps)) }
fn por(ps: Vec<Box<Predicate>>) -> Box<Predicate> { Box::new(Predicate::Or(ps)) }
fn pnot(p: Box<Predicate>) -> Box<Predicate> { Box::new(Predicate::Not(p)) }
fn peqs(ps: Vec<Box<SymOp>>) -> Box<Predicate> { Box::new(Predicate::Equals(ps.into_iter().map(|s| *s).collect())) }
fn peq(s1: Box<SymOp>, s2: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::Equals(vec![*s1, *s2])) }
fn pgeq(s1: Box<SymOp>, s2: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::Geq(*s1, *s2)) }
fn pgreater(s1: Box<SymOp>, s2: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::Greater(*s1, *s2)) }
fn pleq(s1: Box<SymOp>, s2: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::Leq(*s1, *s2)) }
fn plesser(s1: Box<SymOp>, s2: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::Less(*s1, *s2)) }
fn pis_some(s: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::IsSome(*s)) }
fn pis_none(s: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::IsNone(*s)) }
fn pis_ok(s: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::IsOkay(*s)) }
fn pis_err(s: Box<SymOp>) -> Box<Predicate> { Box::new(Predicate::IsErr(*s)) }

impl Halt {
    pub fn new_test() -> Self {
        Self {
            predicate: pf(),
            formula: cb(false),
            condition: None,
            vars: HashMap::new(),
            map_state: HashMap::new(),
            map_tombstones: HashMap::new(),
            early_return: false,
            panicking: false,
            reachable_map_reads: HashSet::new(),
            reachable_map_writes: HashSet::new(),
            reachable_var_reads: HashSet::new(),
            reachable_var_writes: HashSet::new(),
            analyze_write_reachability: true,
        }
    }

    pub fn pred(mut self, p: Box<Predicate>) -> Self {
        self.predicate = p;
        self
    }

    pub fn formula(mut self, f: Box<SymOp>) -> Self {
        self.formula = f;
        self
    }

    pub fn var(mut self, contract_id: QualifiedContractIdentifier, var_name: &str, var_value: Box<SymOp>) -> Self {
        let var_name = FullName(contract_id, ClarityName::try_from(var_name).unwrap());
        self.vars.insert(var_name, *var_value);
        self
    }

    pub fn map(mut self, contract_id: QualifiedContractIdentifier, map_basename: &str, key_sym: Box<SymOp>, value_sym: Box<SymOp>) -> Self {
        let map_name = FullName(contract_id.clone(), ClarityName::try_from(map_basename).unwrap());
        if let Some(state) = self.map_state.get_mut(&map_name) {
            state.insert(*key_sym, *value_sym);
        }
        else {
            let mut state = HashMap::new();
            state.insert(*key_sym, *value_sym);
            self.map_state.insert(map_name.clone(), state);
        }
        self
    }

    pub fn mapd(mut self, contract_id: QualifiedContractIdentifier, map_basename: &str, key_sym: Box<SymOp>) -> Self {
        let map_name = FullName(contract_id.clone(), ClarityName::try_from(map_basename).unwrap());
        if let Some(state) = self.map_tombstones.get_mut(&map_name) {
            state.insert(*key_sym);
        }
        else {
            let mut state = HashSet::new();
            state.insert(*key_sym);
            self.map_tombstones.insert(map_name.clone(), state);
        }
        self
    }

    pub fn reachable_map_read(mut self, contract_id: QualifiedContractIdentifier, map_name: &str) -> Self {
        let map_name = FullName(contract_id, ClarityName::try_from(map_name).unwrap());
        self.reachable_map_reads.insert(map_name);
        self
    }

    pub fn reachable_var_read(mut self, contract_id: QualifiedContractIdentifier, var_name: &str) -> Self {
        let var_name = ClarityName::try_from(var_name).unwrap();
        let var_full_name = FullName(contract_id, var_name);
        self.reachable_var_reads.insert(var_full_name);
        self
    }

    pub fn reachable_map_write(mut self, contract_id: QualifiedContractIdentifier, map_name: &str) -> Self {
        let map_name = FullName(contract_id, ClarityName::try_from(map_name).unwrap());
        self.reachable_map_writes.insert(map_name);
        self
    }

    pub fn reachable_var_write(mut self, contract_id: QualifiedContractIdentifier, var_name: &str) -> Self {
        let var_name = ClarityName::try_from(var_name).unwrap();
        let var_full_name = FullName(contract_id, var_name);
        self.reachable_var_writes.insert(var_full_name);
        self
    }

    pub fn panic(mut self) -> Self {
        self.panicking = true;
        self
    }

    pub fn early_return(mut self) -> Self {
        self.early_return = true;
        self
    }
}

fn assert_halts(conts: Vec<Continuation>, halts: Vec<Halt>) {
    let failures = ProofFailures::from_continuations_and_halts(conts, halts).unwrap();
    if !failures.is_empty() {
        error!("assert_halts() failed, Proof failures:\n{failures}\n");
        panic!()
    }
}

#[test]
fn test_consolidate_add() {
    let symop = add(vec![cu(1), cu(2)]);
    assert_eq!(symop.simplify(), Ok(*cu(3)));

    let symop = add(vec![ci(1), ci(2)]);
    assert_eq!(symop.simplify(), Ok(*ci(3)));

    let symop = add(vec![cu(u128::MAX), cu(1)]);
    let Err(Error::Arithmetic(_s)) = symop.simplify() else { panic!(); };

    let symop = add(vec![ci(i128::MAX), ci(1)]);
    let Err(Error::Arithmetic(_s)) = symop.simplify() else { panic!(); };

    let symop = add(vec![add(vec![add(vec![cu(1), cu(2)]), cu(3)]), cu(4)]);
    assert_eq!(symop.simplify(), Ok(*cu(1 + 2 + 3 + 4)));

    let symop = add(vec![cu(1), add(vec![cu(2), add(vec![cu(3), cu(4)])])]);
    assert_eq!(symop.simplify(), Ok(*cu(1 + 2 + 3 + 4)));

    let symop = add(vec![vu("x"), cu(0)]);
    assert_eq!(symop.simplify(), Ok(*vu("x")));

    let symop = add(vec![cu(0), vu("x")]);
    assert_eq!(symop.simplify(), Ok(*vu("x")));

    let symop = add(vec![cu(0), vu("x"), cu(0), vu("y")]);
    assert_eq!(symop.simplify(), Ok(*add(vec![vu("x"), vu("y")])));
}

#[test]
fn test_consolidate_multiply() {
    let symop = mul(vec![cu(1), cu(2)]);
    assert_eq!(symop.simplify(), Ok(*cu(2)));

    let symop = mul(vec![ci(1), ci(2)]);
    assert_eq!(symop.simplify(), Ok(*ci(2)));

    let symop = mul(vec![cu(u128::MAX), cu(2)]);
    let Err(Error::Arithmetic(_s)) = symop.simplify() else { panic!(); };

    let symop = mul(vec![ci(i128::MAX), ci(2)]);
    let Err(Error::Arithmetic(_s)) = symop.simplify() else { panic!(); };

    let symop = mul(vec![mul(vec![mul(vec![cu(1), cu(2)]), cu(3)]), cu(4)]);
    assert_eq!(symop.simplify(), Ok(*cu(1 * 2 * 3 * 4)));

    let symop = mul(vec![cu(1), mul(vec![cu(2), mul(vec![cu(3), cu(4)])])]);
    assert_eq!(symop.simplify(), Ok(*cu(1 * 2 * 3 * 4)));

    let symop = mul(vec![cu(1), vu("x")]);
    assert_eq!(symop.simplify(), Ok(*vu("x")));

    let symop = mul(vec![vu("x"), cu(1)]);
    assert_eq!(symop.simplify(), Ok(*vu("x")));

    let symop = mul(vec![vu("x"), cu(0)]);
    assert_eq!(symop.simplify(), Ok(*cu(0)));

    let symop = mul(vec![cu(0), vu("x")]);
    assert_eq!(symop.simplify(), Ok(*cu(0)));

    // (x - 1) * (x - 2) == ((pow x u2) + 2) - (x * 3)
    let symop = mul(vec![sub2(vu("x"), cu(1)), sub2(vu("x"), cu(2))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *sub2(add2(pow(vu("x"), cu(2)), cu(2)), mul2(vu("x"), cu(3))));

    // (x - 1) * (x - 2) * (x - 3)
    // (x*x - 3*x + 2) * (x - 3)
    // (x*x*x - 3*x*x + 2*x - 3*x*x + 9*x - 6)
    // (x*x*x + 11*x) - (6*x*x + 6)
    // ((pow x u3) + (* u11 x)) - (+ (* u6 (pow x u2)) u6)
    let symop = mul(vec![sub2(vu("x"), cu(1)), sub2(vu("x"), cu(2)), sub2(vu("x"), cu(3))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *sub2(add2(pow(vu("x"), cu(3)), mul2(vu("x"), cu(11))), add2(mul(vec![cu(6), pow(vu("x"), cu(2))]), cu(6))));

    // (pow u2 x) * (pow u2 y) * z * (pow u3 w) = (pow u2 (+ x y)) * (pow u3 w) * z
    let symop = mul(vec![pow(cu(2), vu("x")), pow(cu(2), vu("y")), vu("z"), pow(cu(3), vu("w"))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *mul(vec![pow(cu(2), add2(vu("x"), vu("y"))), pow(cu(3), vu("w")), vu("z")]));
}

#[test]
fn test_consolidate_pow() {
    // (pow (pox x y) z) == (pow x (* y z))
    let symop = pow(pow(vu("x"), vu("y")), vu("z"));
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *pow(vu("x"), mul2(vu("y"), vu("z"))));

    // (pow u2 (log2 x)) = x
    let symop = pow(cu(2), log2(vu("x"))); 
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *vu("x"));
}

#[test]
fn test_consolidate_subtract() {
    // u3 - u2 == Ok(u1)
    let symop = sub(vec![cu(3), cu(2)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(1)));

    // 3 - 2 == Ok(1)
    let symop = sub(vec![ci(3), ci(2)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(1)));
    
    // u2 - u3 == Error::Arithmetic
    let symop = sub(vec![cu(2), cu(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    let Err(Error::Arithmetic(_s)) = &simplified else { panic!("{:?}", simplified) };
    
    // 2 - 3 == -1
    let symop = sub(vec![ci(2), ci(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(-1)));

    // 1 - (2 - 3) == Ok(2)
    let symop = sub(vec![ci(1), sub(vec![ci(2), ci(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(2)));
   
    // NOTE: this should actually panic:
    // u1 - (u2 - u3) == Err:Arithmetic
    // HOWEVER, the symbolic executor first tries to rearrange terms,
    // and will instead compute:
    // (- u1 (- u2 u3))     -->
    // (- (+ u1 u3) u2)     -->
    // (- u4 u2)            -->
    // u2

    let symop = sub(vec![cu(1), sub(vec![cu(2), cu(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    // let Err(Error::Arithmetic(_s)) = &simplified else { panic!("{:?}", simplified) };
    assert_eq!(simplified, Ok(*cu(2)));
    
    // u1 - (u3 - u2) == Ok(u0)
    let symop = sub(vec![cu(1), sub(vec![cu(3), cu(2)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(0)));
    
    // (2 - 3) - 4 == Ok(-5)
    let symop = sub(vec![sub(vec![ci(2), ci(3)]), ci(4)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(-5)));
    
    // (u3 - u2) = u1 == Ok(u0)
    let symop = sub(vec![sub(vec![cu(3), cu(2)]), cu(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(0)));
   
    // 1 - (foo - 3) == Ok(4 - foo)
    let symop = sub(vec![ci(1), sub(vec![vi("foo"), ci(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![ci(4), vi("foo")])));

    // u1 - (foo - u3) == Ok(u4 - foo)
    let symop = sub(vec![cu(1), sub(vec![vu("foo"), cu(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![cu(4), vu("foo")])));
    
    // 1 - (foo + 3) == Ok(-2 - foo)
    let symop = sub(vec![ci(1), add(vec![vi("foo"), ci(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![ci(-2), vi("foo")])));

    // u1 - (foo + u3) == Ok(u1 - (foo + u3))
    // (doesn't simplify)
    let symop = sub(vec![cu(1), add(vec![vu("foo"), cu(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // (foo - 3) - 1 == Ok(foo - 4)
    let symop = sub(vec![sub(vec![vi("foo"), ci(3)]), ci(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![vi("foo"), ci(4)])));
    
    // (foo - u3) - u1 == Ok(foo - u4)
    let symop = sub(vec![sub(vec![vu("foo"), cu(3)]), cu(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![vu("foo"), cu(4)])));
    
    // (foo + 3) - 1 == Ok(foo + 2)
    let symop = sub(vec![add(vec![vi("foo"), ci(3)]), ci(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*add(vec![vi("foo"), ci(2)])));
    
    // (foo + u3) - u1 == Ok(foo + u2)
    let symop = sub(vec![add(vec![vu("foo"), cu(3)]), cu(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*add(vec![vu("foo"), cu(2)])));
    
    // (foo + 1) - 3 == Ok(foo - 2)
    let symop = sub(vec![add(vec![vi("foo"), ci(1)]), ci(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![vi("foo"), ci(2)])));
    
    // (foo + u1) - u3 == Ok(foo - u2)
    let symop = sub(vec![add(vec![vu("foo"), cu(1)]), cu(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![vu("foo"), cu(2)])));

    // (1 - foo - 3) == Ok(-2 - foo))
    let symop = sub(vec![ci(1), vi("foo"), ci(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![ci(-2), vi("foo")])));
    
    // (foo - 1 - 3) == Ok(foo - 4))
    let symop = sub(vec![vi("foo"), ci(1), ci(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![vi("foo"), ci(4)])));
    
    // (foo - (bar - 10) - 1) == Ok(foo - bar + 9)
    let symop = sub(vec![sub(vec![vu("foo"), sub(vec![vu("bar"), cu(10)])]), cu(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![add2(vu("foo"), cu(9)), vu("bar")])));

    // (foo - (foo - 10) - 1) == Ok(9)
    let symop = sub(vec![sub(vec![vu("foo"), sub(vec![vu("foo"), cu(10)])]), cu(1)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(9)));

    // foo - 0 == Ok(foo)
    let symop = sub(vec![vi("foo"), ci(0)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vi("foo")));

    // 0 - foo == Ok(0 - foo)
    let symop = sub(vec![cu(0), vu("foo")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));
    
    // foo - 0 - 0 == Ok(foo)
    let symop = sub(vec![vi("foo"), ci(0), ci(0)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vi("foo")));
    
    // 0 - 0 - foo == Ok(0 - foo)
    let symop = sub(vec![cu(0), cu(0), vu("foo")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![cu(0), vu("foo")])));
    
    // 0 - foo - 0 == Ok(0 - foo)
    let symop = sub(vec![cu(0), vu("foo"), cu(0)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![cu(0), vu("foo")])));
    
    // 0 - 0 - foo - 0 - 0 == Ok(0 - foo)
    let symop = sub(vec![cu(0), cu(0), vu("foo"), cu(0), cu(0)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub(vec![cu(0), vu("foo")])));
}

#[test]
fn test_consolidate_divide() {
    // u3 / u2 == Ok(u1)
    let symop = div(vec![cu(3), cu(2)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(1)));

    // 3 / 2 == Ok(1)
    let symop = div(vec![ci(3), ci(2)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(1)));
    
    // (u13 / u2 / u3) == ((u13 / u2) / u3 == (u6 / u3) == u2
    let symop = div(vec![cu(13), cu(2), cu(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(2)));

    // (13 / 2 / 3) == ((13 / 2) / 3 == (6 / 3) == 2
    let symop = div(vec![ci(13), ci(2), ci(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(2)));

    // basic factoring
    // (u6 * foo / u3) == u2 * foo
    let symop = div(vec![mul(vec![vu("foo"), cu(6)]), cu(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*mul(vec![vu("foo"), cu(2)])));
    
    // (6 * foo / 3) == 2 * foo
    let symop = div(vec![mul(vec![vi("foo"), ci(6)]), ci(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*mul(vec![vi("foo"), ci(2)])));

    // (u2 * foo / u6) == foo / u3
    let symop = div(vec![mul(vec![vu("foo"), cu(2)]), cu(6)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![vu("foo"), cu(3)])));
    
    // (2 * foo / 6) == foo / 3
    let symop = div(vec![mul(vec![vi("foo"), ci(2)]), ci(6)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![vi("foo"), ci(3)])));
    
    // (u6 / (u3 * foo)) = u2 / foo
    let symop = div(vec![cu(6), mul(vec![vu("foo"), cu(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![cu(2), vu("foo")])));
    
    // (6 / (3 * foo)) = 2 / foo
    let symop = div(vec![ci(6), mul(vec![vi("foo"), ci(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![ci(2), vi("foo")])));
    
    // (u6 / (u30 * foo)) = u1 / (u5 * foo)
    let symop = div(vec![cu(6), mul(vec![vu("foo"), cu(30)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![cu(1), mul(vec![cu(5), vu("foo")])])));
    
    // (6 / (30 * foo)) = 1 / (5 * foo)
    let symop = div(vec![ci(6), mul(vec![vi("foo"), ci(30)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![ci(1), mul(vec![ci(5), vi("foo")])])));
    
    // (u12 / (u30 * foo)) = u2 / (u5 * foo)
    let symop = div(vec![cu(12), mul(vec![vu("foo"), cu(30)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![cu(2), mul(vec![cu(5), vu("foo")])])));
    
    // (12 / (30 * foo)) = 2 / (5 * foo)
    let symop = div(vec![ci(12), mul(vec![vi("foo"), ci(30)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![ci(2), mul(vec![ci(5), vi("foo")])])));
    
    // (u12 * foo / u30) == 2 * foo / u5
    let symop = div(vec![mul(vec![vu("foo"), cu(12)]), cu(30)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![mul(vec![cu(2), vu("foo")]), cu(5)])));
    
    // (12 * foo / 30) == 2 * foo / 5
    let symop = div(vec![mul(vec![vi("foo"), ci(12)]), ci(30)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*div(vec![mul(vec![ci(2), vi("foo")]), ci(5)])));

}

#[test]
fn test_consolidate_modulus() {
    // u5 % u3 == Ok(u2)
    let symop = rem(cu(5), cu(3));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(2)));

    // u5 % u3 == Ok(u2)
    let symop = rem(ci(5), ci(3));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(2)));

    // (u10 * foo) % u5 == Ok(u0)
    let symop = rem(mul(vec![cu(10), vu("foo")]), cu(5));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(0)));
     
    // (u10 * foo) % u5 == Ok(0)
    let symop = rem(mul(vec![ci(10), vi("foo")]), ci(5));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ci(0)));
    
    // (u11 * foo) % u5 doesn't reduce
    let symop = rem(mul(vec![cu(11), vu("foo")]), cu(5));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));
     
    // (u11 * foo) % u5 doesn't reduce
    let symop = rem(mul(vec![ci(11), vi("foo")]), ci(5));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));
}

#[test]
fn test_consolidate_concat() {
    // (concat 0x01 0x02) == 0x0102
    let symop = concat(vec![csb(vec![1]), csb(vec![2])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*csb(vec![1, 2])));
    
    // (concat 0x01 0x02 0x03 0x04) == 0x01020304
    let symop = concat(vec![csb(vec![1]), csb(vec![2]), csb(vec![3]), csb(vec![4])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*csb(vec![1, 2, 3, 4])));

    // (concat 0x01 (concat 0x02 0x03) 0x04) = 0x01020304
    let symop = concat(vec![csb(vec![1]), concat(vec![csb(vec![2]), csb(vec![3])]), csb(vec![4])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*csb(vec![1, 2, 3, 4])));

    // (cocnat 0x01 x 0x02) = (concat 0x01 x 0x02)
    let symop = concat(vec![csb(vec![1]), vsb("x", 1), csb(vec![2])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // (concat 0x01 (concat 0x02 x 0x03) 0x04) = (concat 0x0102 x 0x0304)
    let symop = concat(vec![csb(vec![1]), concat(vec![csb(vec![2]), vsb("x", 1), csb(vec![3])]), csb(vec![4])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*concat(vec![csb(vec![1, 2]), vsb("x", 1), csb(vec![3, 4])])));
}

#[test]
fn test_consolidate_and() {
    // true && true == Ok(true)
    let symop = and(vec![cb(true), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // true && false == Ok(false)
    let symop = and(vec![cb(true), cb(false)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // false && true == Ok(false)
    let symop = and(vec![cb(false), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // false && false == Ok(false)
    let symop = and(vec![cb(false), cb(false)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));

    // (true && true) && true == Ok(true)
    let symop = and(vec![and(vec![cb(true), cb(true)]), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // (false && true) && true == Ok(false)
    let symop = and(vec![and(vec![cb(false), cb(true)]), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));

    // (true && true) && false == Ok(false)
    let symop = and(vec![and(vec![cb(true), cb(true)]), cb(false)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // true && (true && true) == Ok(true)
    let symop = and(vec![cb(true), and(vec![cb(true), cb(true)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // true && (true && false) == Ok(false)
    let symop = and(vec![cb(true), and(vec![cb(true), cb(false)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // false && (true && true) == Ok(true)
    let symop = and(vec![cb(false), and(vec![cb(true), cb(true)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));

    // true && foo == Ok(foo)
    let symop = and(vec![cb(true), vb("foo")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vb("foo")));

    // (foo == 1 && foo == 2) == Ok(false)
    let symop = and(vec![eq(vu("foo"), cu(1)), eq(vu("foo"), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // ((mod foo u2) == 1 && (mod foo u2) == 2) === Ok(false)
    let symop = and(vec![eq(rem(vu("foo"), cu(2)), cu(1)), eq(rem(vu("foo"), cu(2)), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // ((mod foo u2) == 1 && (mod foo u3) == 2) does not reduce
    let symop = and(vec![eq(rem(vu("foo"), cu(2)), cu(1)), eq(rem(vu("foo"), cu(3)), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));
    
    // ((mod foo u2) == 2 && (mod foo u3) == 2) === ((mod foo u2) == (mod foo u3) == u2)
    let symop = and(vec![eq(rem(vu("foo"), cu(2)), cu(2)), eq(rem(vu("foo"), cu(3)), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eqs(vec![rem(vu("foo"), cu(2)), rem(vu("foo"), cu(3)), cu(2)])));

    // (and (is-eq foo u0) (not (is-eq (foo u1)))) === (is-eq foo u0)
    let symop = and(vec![eq(vu("foo"), cu(0)), not(eq(vu("foo"), cu(1)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vu("foo"), cu(0))));

    // (and (is-eq (mod foo u2) (mod foo u3)) (is-eq (mod foo u3) (mod foo u3)))
    // === (is-eq (mod foo u2) (mod foo u3))
    let symop = and(vec![eq(rem(vu("foo"), cu(2)), rem(vu("foo"), cu(3))), eq(rem(vu("foo"), cu(3)), rem(vu("foo"), cu(3)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eqs(vec![rem(vu("foo"), cu(2)), rem(vu("foo"), cu(3))])));

    // (and (is-eq foo u1) (not (is-eq foo u1))) === Ok(false)
    let symop = and(vec![eq(vu("foo"), cu(1)), not(eq(vu("foo"), cu(1)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));

    // (and (not (is-eq foo baz)) (not (is-eq baz foo))) === Ok((not (is-eq foo baz)))
    assert_eq!(eq(vu("foo"), vu("baz")), eq(vu("baz"), vu("foo")));
    assert_eq!(not(eq(vu("foo"), vu("baz"))), not(eq(vu("baz"), vu("foo"))));

    let symop = and(vec![not(eq(vu("foo"), vu("baz"))), not(eq(vu("baz"), vu("foo")))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*not(eq(vu("foo"), vu("baz")))));

    // (and (is-eq foo bar) (not (is-eq foo baz))) does not reduce
    let symop = and(vec![eq(vu("foo"), vu("bar")), not(eq(vu("foo"), vu("baz")))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));
    
    // (and (is-eq foo bar) (is-eq foo baz)) == Ok((and (is-eq foo bar baz)))
    let symop = and(vec![eq(vu("foo"), vu("bar")), eq(vu("foo"), vu("baz"))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eqs(vec![vu("foo"), vu("bar"), vu("baz")])));

    // (and (var-get x) (not (var-get y))) does not reduce
    let symop = and(vec![var_get(sb("x")), not(var_get(sb("y")))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // (and (x >= 0) (x < 0)) is False
    let symop = and(vec![geq(vi("x"), ci(0)), lt(vi("x"), ci(0))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x > 0) (x <= 0)) is False
    let symop = and(vec![gt(vi("x"), ci(0)), leq(vi("x"), ci(0))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x > 0) (x < 0)) is False
    let symop = and(vec![gt(vi("x"), ci(0)), lt(vi("x"), ci(0))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));

    // (and (x < 0) (x == 0)) is False
    let symop = and(vec![eq(vi("x"), ci(0)), lt(vi("x"), ci(0))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x > 0) (x == 0)) is False
    let symop = and(vec![eq(vi("x"), ci(0)), gt(vi("x"), ci(0))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));

    // (and (x >= 100) (x < 99)) is False
    let symop = and(vec![geq(vi("x"), ci(100)), lt(vi("x"), ci(99))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x > 100) (x <= 99)) is False
    let symop = and(vec![gt(vi("x"), ci(100)), leq(vi("x"), ci(99))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x >= 100) (x <= 99)) is False
    let symop = and(vec![geq(vi("x"), ci(100)), leq(vi("x"), ci(99))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x > 100) (x < 99)) is False
    let symop = and(vec![gt(vi("x"), ci(100)), lt(vi("x"), ci(99))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x >= 100) (x < 110)) does not reduce
    let symop = and(vec![geq(vi("x"), ci(100)), lt(vi("x"), ci(110))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // (and (>= u0 x) (not (is-eq x u0))) is a contradiction
    let symop = and(vec![geq(cu(0), vu("x")), not(eq(vu("x"), cu(0)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (>= i128::MIN x) (not (is-eq x i128::MIN))) is a contradiction
    let symop = and(vec![geq(ci(i128::MIN), vi("x")), not(eq(vi("x"), ci(i128::MIN)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (<= u128::MAX x) (not (is-eq x u128::MAX))) is a contradiction
    let symop = and(vec![leq(cu(u128::MAX), vu("x")), not(eq(vu("x"), cu(u128::MAX)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (<= i128::MAX x) (not (is-eq x i128::MAX))) is a contradiction
    let symop = and(vec![leq(ci(i128::MAX), vi("x")), not(eq(vi("x"), ci(i128::MAX)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));

    // (and (<= x u10) (is-eq x u10)) == Ok((is-eq x u10))
    let symop = and(vec![leq(vu("x"), cu(10)), eq(vu("x"), cu(10))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vu("x"), cu(10))));
    
    // (and (>= x u10) (is-eq x u10)) == Ok((is-eq x u10))
    let symop = and(vec![geq(vu("x"), cu(10)), eq(vu("x"), cu(10))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vu("x"), cu(10))));
    
    // (and (<= x 10) (is-eq x 10)) == Ok((is-eq x 10))
    let symop = and(vec![leq(vi("x"), ci(10)), eq(vi("x"), ci(10))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vi("x"), ci(10))));
    
    // (and (>= x 10) (is-eq x 10)) == Ok((is-eq x 10))
    let symop = and(vec![geq(vi("x"), ci(10)), eq(vi("x"), ci(10))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vi("x"), ci(10))));

    // (and (x < u100) (x < u50)) === Ok(x < u50)
    let symop = and(vec![lt(vu("x"), cu(100)), lt(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*lt(vu("x"), cu(50))));
    
    // (and (x < 100) (x < 50)) === Ok(x < 50)
    let symop = and(vec![lt(vi("x"), ci(100)), lt(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*lt(vi("x"), ci(50))));
    
    // (and (x <= u100) (x <= u50)) === Ok(x <= u50)
    let symop = and(vec![leq(vu("x"), cu(100)), leq(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*leq(vu("x"), cu(50))));
    
    // (and (x <= 100) (x <= 50)) === Ok(x <= 50)
    let symop = and(vec![leq(vi("x"), ci(100)), leq(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*leq(vi("x"), ci(50))));
    
    // (and (x < u100) (x <= u50)) === Ok(x <= u50)
    let symop = and(vec![lt(vu("x"), cu(100)), leq(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*leq(vu("x"), cu(50))));
    
    // (and (x < 100) (x <= 50)) === Ok(x <= u50)
    let symop = and(vec![lt(vi("x"), ci(100)), leq(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*leq(vi("x"), ci(50))));
    
    // (and (x <= u100) (x < u50)) === Ok(x < u50)
    let symop = and(vec![leq(vu("x"), cu(100)), lt(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*lt(vu("x"), cu(50))));
    
    // (and (x <= 100) (x < 50)) === Ok(x < 50)
    let symop = and(vec![leq(vi("x"), ci(100)), lt(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*lt(vi("x"), ci(50))));
    
    // (and (x > u100) (x > u50)) === Ok(x > u100)
    let symop = and(vec![gt(vu("x"), cu(100)), gt(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*gt(vu("x"), cu(100))));
    
    // (and (x > 100) (x > 50)) === Ok(x > 100)
    let symop = and(vec![gt(vi("x"), ci(100)), gt(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*gt(vi("x"), ci(100))));
    
    // (and (x >= u100) (x >= u50)) === Ok(x >= u100)
    let symop = and(vec![geq(vu("x"), cu(100)), geq(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*geq(vu("x"), cu(100))));
    
    // (and (x >= 100) (x >= 50)) === Ok(x >= 100)
    let symop = and(vec![geq(vi("x"), ci(100)), geq(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*geq(vi("x"), ci(100))));
    
    // (and (x > u100) (x >= u50)) === Ok(x > u100)
    let symop = and(vec![gt(vu("x"), cu(100)), geq(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*gt(vu("x"), cu(100))));
    
    // (and (x > 100) (x >= 50)) === Ok(x > u100)
    let symop = and(vec![gt(vi("x"), ci(100)), geq(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*gt(vi("x"), ci(100))));
    
    // (and (x >= u100) (x > u50)) === Ok(x >= u100)
    let symop = and(vec![geq(vu("x"), cu(100)), gt(vu("x"), cu(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*geq(vu("x"), cu(100))));
    
    // (and (x >= 100) (x > 50)) === Ok(x >= 100)
    let symop = and(vec![geq(vi("x"), ci(100)), gt(vi("x"), ci(50))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*geq(vi("x"), ci(100))));

    // (and (x > u0) (not (is-eq x u1)) (x < u2)) is a contradiction
    let symop = and(vec![gt(vu("x"), cu(0)), not(eq(vu("x"), cu(1))), lt(vu("x"), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (x > u0) (not (is-eq x u2)) (not (is-eq x u1)) (x < u3)) is a contradiction
    let symop = and(vec![gt(vu("x"), cu(0)), not(eq(vu("x"), cu(1))), lt(vu("x"), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));

    // (and (x > u10) (is-eq x u11)) === Ok((is-eq x u11))
    let symop = and(vec![gt(vu("x"), cu(10)), eq(vu("x"), cu(11))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vu("x"), cu(11))));

    // (and (is-eq (len (list u0 u1 u2 u3) u4)) (not (is-eq x u0)) (not (is-eq x u1))) 
    // reduces to (and (not (is-eq x u0)) (not (is-eq x u1)))
    let symop = and(vec![eq(llen(lcons(vec![cu(0), cu(1), cu(2), cu(3)])), cu(4)), not(eq(vu("x"), cu(0))), not(eq(vu("x"), cu(1)))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*and(vec![not(eq(vu("x"), cu(0))), not(eq(vu("x"), cu(1)))])));
    
    // (and (is-eq (len (list u0 u1 u2 u3) u4)) (not (is-eq x u0)) (not (is-eq x u1))) 
    // reduces to (and (not (is-eq x u0)) (not (is-eq x u1)))
    let symop = and(vec![not(eq(cu(0), lv("x", vu("x")))), not(eq(cu(1), lv("x", vu("x")))), eq(cu(4), llen(lcons(vec![cu(0), cu(1), cu(2), cu(3)])))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*and(vec![not(eq(lv("x", vu("x")), cu(0))), not(eq(lv("x", vu("x")), cu(1)))])));
   
    // TODO:
    // (and
    //      (>=
    //          (burn-block-height uint)
    //          (unwrap-panic
    //              (get until-burn-ht
    //                  (unwrap-panic
    //                      (map-entry allowance-contract-callers
    //                          (tuple
    //                              (contract-caller S1G2081040G2081040G2081040G208105NK8PE5)
    //                              (sender S1G2081040G2081040G2081040G208105NK8PE5)))))))
    //
    //      (is-some
    //          (get until-burn-ht
    //              (unwrap-panic
    //                  (map-entry allowance-contract-callers
    //                      (tuple
    //                          (contract-caller S1G2081040G2081040G2081040G208105NK8PE5)
    //                          (sender S1G2081040G2081040G2081040G208105NK8PE5))))))
    //                          
    //      (is-some
    //          (map-entry allowance-contract-callers
    //              (tuple
    //                  (contract-caller S1G2081040G2081040G2081040G208105NK8PE5)
    //                  (sender S1G2081040G2081040G2081040G208105NK8PE5)))))
    //
    // reduces to
    //  (>=
    //      (burn-block-height uint)
    //      (unwrap-panic
    //          (get until-burn-ht
    //              (unwrap-panic
    //                  (map-entry allowance-contract-callers
    //                      (tuple
    //                          (contract-caller S1G2081040G2081040G2081040G208105NK8PE5)
    //                          (sender S1G2081040G2081040G2081040G208105NK8PE5)))))))
    //
    //  since the two `is-some` checks are redundant.  `unwrap-panic` implies `is-some`
    let symop = and(vec![
        geq(vu("burn-block-height"), unwrap_panic(tget("until-burn-ht", unwrap_panic(map_get("allowance-contract-callers", tcons(vec![("contract-caller", vu("cc")), ("sender", vu("s"))])))))),
        is_some(tget("until-burn-ht", unwrap_panic(map_get("allowance-contract-callers", tcons(vec![("contract-caller", vu("cc")), ("sender", vu("s"))]))))),
        is_some(map_get("allowance-contract-callers", tcons(vec![("contract-caller", vu("cc")), ("sender", vu("s"))])))
    ]);
   
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // (and (is-some x) (is-none x)) is a contradiction
    let symop = and(vec![is_some(vo("x", TS::UIntType)), is_none(vo("x", TS::UIntType))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
    
    // (and (is-okay x) (is-err x)) is a contradiction
    let symop = and(vec![is_ok(vo("x", TS::UIntType)), is_err(vo("x", TS::UIntType))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));

    // (and (is-some (map-get? m y)) (is-none (get x (map-get? m y)))) is a contradiction
    let symop = and(vec![is_some(map_get("map", vu("y"))), is_none(tget("x", map_get("map", vu("y"))))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));

    // (and (is-none (map-get? m y)) (is-some (get x (map-get? m y)))) is a contradiction
    let symop = and(vec![is_none(map_get("map", vu("y"))), is_some(tget("x", map_get("map", vu("y"))))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*f()));
}

#[test]
fn test_consolidate_or() {
    // true || true == Ok(true)
    let symop = or(vec![cb(true), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // true || false == Ok(true)
    let symop = or(vec![cb(true), cb(false)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // false || true == Ok(true)
    let symop = or(vec![cb(false), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // false || false == Ok(false)
    let symop = or(vec![cb(false), cb(false)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));

    // (true || true) || true == Ok(true)
    let symop = or(vec![or(vec![cb(true), cb(true)]), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // (false || true) || true == Ok(true)
    let symop = or(vec![or(vec![cb(false), cb(true)]), cb(true)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));

    // (true || true) || false == Ok(true)
    let symop = or(vec![or(vec![cb(true), cb(true)]), cb(false)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // true || (true || true) == Ok(true)
    let symop = or(vec![cb(true), or(vec![cb(true), cb(true)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // true || (true || false) == Ok(true)
    let symop = or(vec![cb(true), or(vec![cb(true), cb(false)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // false || (true || true) == Ok(true)
    let symop = or(vec![cb(false), or(vec![cb(true), cb(true)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));

    // true || foo == Ok(true)
    let symop = or(vec![cb(true), vb("foo")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));

    // doesn't reduce (already in SoP form)
    // (a && b) || c 
    let symop = or(vec![and(vec![vb("a"), vb("b")]), vb("c")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // distributes
    // (a || b) && c == (a && c) || (b && c)
    let symop = and(vec![or(vec![vb("a"), vb("b")]), vb("c")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*or(vec![and(vec![vb("a"), vb("c")]), and(vec![vb("b"), vb("c")])])));

    // or lifted out
    // (a && b) || ((c && d) || e) ==> (a && b) || (c && d) || e
    let symop = or(vec![and(vec![vb("a"), vb("b")]), or(vec![and(vec![vb("c"), vb("d")]), vb("e")])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*or(vec![and(vec![vb("a"), vb("b")]), and(vec![vb("c"), vb("d")]), vb("e")])));

    // doesn't reduce
    // (a == 0) || (a == 1) || (a == 2)
    let symop = or(vec![eq(vu("a"), cu(0)), eq(vu("a"), cu(1)), eq(vu("a"), cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // redundant term elimination
    // (a == 0) || (a == 1) || (a == 0) ==> (a == 0) || (a == 1)
    let symop = or(vec![eq(vu("a"), cu(0)), eq(vu("a"), cu(1)), eq(vu("a"), cu(0))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*or(vec![eq(vu("a"), cu(0)), eq(vu("a"), cu(1))])));
    
    // or gets lifted
    // (a == 0 || (a == 1 || a == 2)) == (a == 0) || (a == 1) || (a == 2)
    let symop = or(vec![eq(vu("a"), cu(0)), or(vec![eq(vu("a"), cu(1)), eq(vu("a"), cu(2))])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*or(vec![eq(vu("a"), cu(0)), eq(vu("a"), cu(1)), eq(vu("a"), cu(2))])));
   
    // doesn't reduce
    // (is-eq (len a) u10) || (is-eq (len a) u9)
    let symop = or(vec![eq(llen(vl("a", TS::UIntType, 10)), cu(10)), eq(llen(vl("a", TS::UIntType, 10)), cu(9))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));

    // and-absorption
    // (a == 0 || a == 1) && (a == 0 || a == 2) ==> a == 0 
    let symop = and(vec![or(vec![eq(vu("a"), cu(0)), eq(vu("a"), cu(1))]), or(vec![eq(vu("a"), cu(0)), eq(vu("a"), cu(2))])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vu("a"), cu(0))));

    // or-absorption
    // A || (A && B) == A
    let symop = or(vec![vb("a"), and(vec![vb("a"), vb("b")])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vb("a")));

    // consensus 
    // (!A && B) || (A && C) || (B && C) == (!A && B) || (A && C)
    let symop = or(vec![and(vec![not(vb("a")), vb("b")]), and(vec![vb("a"), vb("c")]), and(vec![vb("b"), vb("c")])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*or(vec![and(vec![not(vb("a")), vb("b")]), and(vec![vb("a"), vb("c")])])));
}

#[test]
fn test_consolidate_not() {
    // !true == Ok(false)
    let symop = not(cb(true));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // !false == Ok(true)
    let symop = not(cb(false));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));

    // !!x == Ok(x)
    let symop = not(not(vb("foo")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vb("foo")));

    // !(x > y) == Ok(x <= y)
    let symop = not(gt(vu("x"), vu("y")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*leq(vu("x"), vu("y"))));
    
    // !(x >= y) == Ok(x < y)
    let symop = not(geq(vu("x"), vu("y")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*lt(vu("x"), vu("y"))));
    
    // !(x < y) == Ok(x >= y)
    let symop = not(lt(vu("x"), vu("y")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*geq(vu("x"), vu("y"))));
    
    // !(x <= y) == Ok(x > y)
    let symop = not(leq(vu("x"), vu("y")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*gt(vu("x"), vu("y"))));

    // !(x == y && y == z) = Ok(x != y || y != z)
    let symop = not(eqs(vec![vu("x"), vu("y"), vu("z")]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*or(vec![not(eq(vu("x"), vu("y"))), not(eq(vu("y"), vu("z")))])));
}

#[test]
fn test_consolidate_equals() {
    // (is-eq x y y) == Ok(is-eq x y)
    let symop = eqs(vec![vu("x"), vu("y"), vu("y")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*eq(vu("x"), vu("y"))));

    // (is-eq x x) == Ok(true)
    let symop = eq(vu("x"), vu("x"));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));

    // (is-eq x 3 4) == Ok(false)
    let symop = eqs(vec![vu("x"), cu(3), cu(4)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
}

#[test]
fn test_consolidate_tuple_cons() {
    // { x: u1, y: u1 } == Ok({x: u1, y: u1})
    let symop = tcons(vec![("x", cu(1)), ("y", cu(2))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ct(vec![("x", valu(1)), ("y", valu(2))])));
    
    // { x: (+ a u1), y: (+ b u2 u3) } == Ok({x: (+ a u1), y: (+ b u5)})
    let symop = tcons(vec![("x", add(vec![vu("a"), cu(1)])), ("y", add(vec![vu("b"), cu(2), cu(3)]))]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*tcons(vec![("x", add(vec![vu("a"), cu(1)])), ("y", add(vec![vu("b"), cu(5)]))])));
}

#[test]
fn test_consolidate_tuple_get() {
    // (get x { x : u1 }) == Ok(u1)
    let symop = tget("x", ct(vec![("x", valu(1))]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(1)));

    // (get x { x : y }) == Ok(y)
    let symop = tget("x", tcons(vec![("x", vu("y"))]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));

    // (get x (loaded-var z { x : y })) == Ok(y)
    let symop = tget("x", lv("z", tcons(vec![("x", vu("y"))])));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));
    
    // (get x (loaded-var z (some { x : y }))) == Ok((some y))
    let symop = tget("x", lv("z", some(tcons(vec![("x", vu("y"))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*some(vu("y"))));
    
    // (get x (loaded-var z (some { x : u1 }))) == Ok((some u1))
    let symop = tget("x", lv("z", some(tcons(vec![("x", cu(1))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*co(valu(1))));
    
    // (get x (some (loaded-var z { x : y }))) == Ok((some y))
    let symop = tget("x", some(lv("z", tcons(vec![("x", vu("y"))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*some(vu("y"))));
    
    // (get x (some (loaded-var z { x :u1y }))) == Ok((some u1))
    let symop = tget("x", some(lv("z", tcons(vec![("x", cu(1))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*co(valu(1))));

    // (get x (map-get? m z (some { x : y }))) == Ok((some y))
    let symop = tget("x", lm("m", vu("z"), tcons(vec![("x", vu("y"))]))); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*some(vu("y"))));
    
    // (get x (map-get? m z (some { x : u1 }))) == Ok((some u1))
    let symop = tget("x", lm("m", vu("z"), tcons(vec![("x", cu(1))]))); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*co(valu(1))));
    
    // (get x (map-get? m z)) does not reduce
    let symop = tget("x", map_get("m", vu("z")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*symop));
    
    // (get x (merge { y : u2 } { x : u1 })) == Ok(u1)
    let symop = tget("x", tmerge(ct(vec![("y", valu(2))]), ct(vec![("x", valu(1))])));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(1)));

    // (get x (merge { z : w } { x : y }) == Ok(y)
    let symop = tget("x", tmerge(tcons(vec![("z", vu("w"))]), tcons(vec![("x", vu("y"))])));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));

    // (get x (merge { z : w } (loaded-var z { x : y }))) == Ok(y)
    let symop = tget("x", tmerge(tcons(vec![("z", vu("w"))]), lv("z", tcons(vec![("x", vu("y"))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));
    
    // (get x (merge { z : w } (loaded-var z (some { x : y })))) == Ok((some y))
    let symop = tget("x", tmerge(tcons(vec![("z", vu("w"))]), lv("z", some(tcons(vec![("x", vu("y"))])))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*some(vu("y"))));
    
    // (get x (merge { z : w } (loaded-var z (some { x : u1 })))) == Ok((some u1))
    let symop = tget("x", tmerge(tcons(vec![("z", vu("w"))]), lv("z", some(tcons(vec![("x", cu(1))])))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*co(valu(1))));
    
    // (get x (some (merge { z : w } (loaded-var z { x : y })))) == Ok((some y))
    let symop = tget("x", some(tmerge(tcons(vec![("z", vu("w"))]), lv("z", tcons(vec![("x", vu("y"))])))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*some(vu("y"))));
    
    // (get x (some (merge { z : w } (loaded-var z { x : u1 })))) == Ok((some u1))
    let symop = tget("x", some(tmerge(tcons(vec![("z", vu("w"))]), lv("z", tcons(vec![("x", cu(1))])))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*co(valu(1))));
}

#[test]
fn test_consolidate_tuple_merge() {
    // (merge { x : u1 } { y : u2 }) == Ok({ x : u1, y : u2 })
    let symop = tmerge(ct(vec![("x", valu(1))]), ct(vec![("y", valu(2))]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*ct(vec![("x", valu(1)), ("y", valu(2))])));

    // (merge { x : u1 } { y : z }) == Ok({ x : u1, y : z })
    let symop = tmerge(ct(vec![("x", valu(1))]), tcons(vec![("y", vu("z"))]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*tcons(vec![("x", cu(1)), ("y", vu("z"))])));

    // (merge { x : z } { y : u2 }) == Ok( { x : z, y : u2 })
    let symop = tmerge(tcons(vec![("x", vu("z"))]), ct(vec![("y", valu(2))]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*tcons(vec![("x", vu("z")), ("y", cu(2))])));

    // (merge { x : z } { y : w }) == Ok( { x : z, y : w })
    let symop = tmerge(tcons(vec![("x", vu("z"))]), tcons(vec![("y", vu("w"))]));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*tcons(vec![("x", vu("z")), ("y", vu("w"))])));
}

#[test]
fn test_consolidate_is_ok() {
    // (is-ok (ok x)) == Ok(true)
    let symop = is_ok(ok(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // (is-ok (err x)) == Ok(false)
    let symop = is_ok(err(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
}

#[test]
fn test_consolidate_is_err() {
    // (is-err (ok x)) == Ok(false)
    let symop = is_err(ok(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // (is-err (err x)) == Ok(true)
    let symop = is_err(err(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
}

#[test]
fn test_consolidate_is_some() {
    // (is-some (some x)) == Ok(true)
    let symop = is_some(some(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
    
    // (is-some none) == Ok(false)
    let symop = is_some(none());
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
}

#[test]
fn test_consolidate_is_none() {
    // (is-none (some x)) == Ok(false)
    let symop = is_none(some(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(false)));
    
    // (is-some none) == Ok(false)
    let symop = is_none(none());
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cb(true)));
}

#[test]
fn test_consolidate_unwrap_panic() {
    // (unwrap-panic (ok x)) == Ok(x)
    let symop = unwrap_panic(ok(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("x")));

    // (unwrap-panic (some x)) == Ok(x)
    let symop = unwrap_panic(some(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("x")));

    // (unwrap-panic (err x)) == Ok(panic)
    let symop = unwrap_panic(err(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*panic()));
    
    // (unwrap-panic none) == Ok(panic)
    let symop = unwrap_panic(none());
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*panic()));
}

#[test]
fn test_consolidate_unwrap_err_panic() {
    // (unwrap-err-panic (ok x)) == Ok(panic)
    let symop = unwrap_err_panic(ok(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*panic()));

    // (unwrap-err-panic (err x)) == Ok(x)
    let symop = unwrap_err_panic(err(vu("x")));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("x")));
}

#[test]
fn test_consolidate_list_cons() {
    // (list u1 u2 u3) == Ok((u1 u2 u3))
    let symop = lcons(vec![cu(1), cu(2), cu(3)]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cl(vec![valu(1), valu(2), valu(3)])));
    
    // (list u1 u2 x) == Ok((list u1 u2 x))
    let symop = lcons(vec![cu(1), cu(2), vu("x")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*lcons(vec![cu(1), cu(2), vu("x")])));
}

#[test]
fn test_consolidate_bitwise_and() {
    // (bit-and u1 u3 u7) == Ok(u1)
    let symop = bitand(vec![cu(1), cu(3), cu(7)]); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(1)));

    // (bit-and u1 x) == Ok((bit-and u1 x))
    let symop = bitand(vec![cu(1), vu("x")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*bitand(vec![cu(1), vu("x")])));
}

#[test]
fn test_consolidate_bitwise_or() {
    // (bit-or u1 u3 u7) == Ok(u7)
    let symop = bitor(vec![cu(1), cu(3), cu(7)]); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(7)));

    // (bit-or u1 x) == Ok((bit-or u1 x))
    let symop = bitor(vec![cu(1), vu("x")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*bitor(vec![cu(1), vu("x")])));
}

#[test]
fn test_consolidate_bitwise_xor() {
    // (bit-xor u1 u3 u7) == Ok(u5)
    let symop = bitxor(vec![cu(1), cu(3), cu(7)]); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*cu(5)));

    // (bit-xor u1 x) == Ok((bit-xor u1 x))
    let symop = bitxor(vec![cu(1), vu("x")]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*bitxor(vec![cu(1), vu("x")])));
}

#[test]
fn test_flatten_multiply() {
    // x * (x + 1) == x*x + 1*x
    let symop = mul2(vu("x"), add2(vu("x"), cu(1)));
    let SymOp::Multiply(inner) = *symop.clone() else { panic!() };
    let simplified = SymOp::flatten_multiply(inner);
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*add2(mul2(vu("x"), vu("x")), mul2(cu(1), vu("x")))));

    // ((x * x) + (1 * 2)) * x = ((x * x) * x) + ((1 * 2) * x)
    let symop = mul2(add2(mul2(vu("x"), vu("x")), mul2(cu(1), cu(2))), vu("x"));
    let SymOp::Multiply(inner) = *symop.clone() else { panic!() };
    let simplified = SymOp::flatten_multiply(inner);
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*add2(mul2(mul2(vu("x"), vu("x")), vu("x")), mul2(mul2(cu(1), cu(2)), vu("x")))));

    // ((x * x) * x) * (y * (y * (y * y))) == (x * x * x * y * y * y * y)
    let symop = mul2(mul2(mul2(vu("x"), vu("x")), vu("x")), mul2(vu("y"), mul2(vu("y"), mul2(vu("y"), vu("y")))));
    let SymOp::Multiply(inner) = *symop.clone() else { panic!() };
    let simplified = SymOp::flatten_multiply(inner);
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*mul(vec![vu("x"), vu("x"), vu("x"), vu("y"), vu("y"), vu("y"), vu("y")])));

    // (x + 1) * (x + 2) == x*x + 2*x + 1*x + 2*1
    let symop = mul2(add2(vu("x"), cu(1)), add2(vu("x"), cu(2)));
    let SymOp::Multiply(inner) = *symop.clone() else { panic!() };
    let simplified = SymOp::flatten_multiply(inner);
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*add(vec![mul2(vu("x"), vu("x")), mul2(cu(2), vu("x")), mul2(cu(1), vu("x")), mul2(cu(2), cu(1))])));
    
    // (x + 1 + y) * (x + 2) == x*x + 2*x + 1*x + 2*1 + y*x + y*2
    let symop = mul2(add(vec![vu("x"), cu(1), vu("y")]), add2(vu("x"), cu(2)));
    let SymOp::Multiply(inner) = *symop.clone() else { panic!() };
    let simplified = SymOp::flatten_multiply(inner);
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*add(vec![
        mul2(vu("x"), vu("x")),
        mul2(cu(2), vu("x")),
        mul2(cu(1), vu("x")),
        mul2(cu(2), cu(1)),
        mul2(vu("y"), vu("x")),
        mul2(vu("y"), cu(2))
    ])));

    // (x - 1) * (x - 2) == x*x - 1*x - 3*x + 2 == (x*x + 1*2) - (1*x + 2*x)
    let symop = mul2(sub2(vu("x"), cu(1)), sub2(vu("x"), cu(2)));
    let SymOp::Multiply(inner) = *symop.clone() else { panic!() };
    let simplified = SymOp::flatten_multiply(inner);
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*sub2(add2(mul2(vu("x"), vu("x")), mul2(cu(1), cu(2))), add2(mul2(cu(1), vu("x")), mul2(cu(2), vu("x"))))));
}


#[test]
fn test_commutative_cmp() {
    let p1 = pand(vec![peq(cu(1), cu(1)), peq(cu(2), cu(3))]);
    let p2 = pand(vec![peq(cu(2), cu(3)), peq(cu(1), cu(1))]);
    assert_eq!(p1, p2);

    let p1 = por(vec![peq(cu(1), cu(1)), peq(cu(2), cu(3))]);
    let p2 = por(vec![peq(cu(2), cu(3)), peq(cu(1), cu(1))]);
    assert_eq!(p1, p2);

    let p1 = por(vec![
        pand(vec![
            peq(cu(1), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
            pleq(cu(1), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
        ]),
        pand(vec![
            pleq(cu(1), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
            peq(cu(1), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
        ]),
    ]);
    
    let p2 = por(vec![
        pand(vec![
            pleq(cu(1), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
            peq(cu(1), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
        ]),
        pand(vec![
            peq(cu(1), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
            pleq(cu(1), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
        ]),
    ]);

    assert_eq!(p1, p2);
}

#[test]
fn test_bind_symbol() {
    // (to-int (x uint)), x <-- u3
    // ---------------------------
    //             3
    let symop = SymOp::ToInt(vu("x"));
    let simplified = symop
        .clone()
        .bind_symbol("x".try_into().unwrap(), *cu(3))
        .simplify()
        .unwrap();

    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *ci(3));

    // (to-int (x uint)), x <-- y + u3
    // -------------------------------
    //    (to-int (+ (y uint) u3))
    let symop = SymOp::ToInt(vu("x"));
    let simplified = symop
        .clone()
        .bind_symbol("x".try_into().unwrap(), *add2(vu("y"), cu(3)))
        .simplify()
        .unwrap();

    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, SymOp::ToInt(add2(vu("y"), cu(3))));

    // (+ x y u3), x <-- u1, y <-- u2
    // ------------------------------
    //           u6
    let symop = add(vec![vu("x"), vu("y"), cu(3)]);
    let simplified = symop
        .clone()
        .bind_symbol("x".try_into().unwrap(), *cu(1))
        .bind_symbol("y".try_into().unwrap(), *cu(2))
        .simplify()
        .unwrap();

    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *cu(6));

    // (map-entry foo (+ x u3) (+ y u6)), y <-- u5
    // -------------------------------------------
    //                u11
    let symop = lm("foo", add2(vu("x"), cu(3)), add2(vu("y"), cu(6)));
    let simplified = symop
        .clone()
        .bind_symbol("y".try_into().unwrap(), *cu(5))
        .simplify()
        .unwrap();


    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *co(valu(11)));
}


#[test]
fn test_halt_if_sym() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (if (var-get x)
            u2
            u3)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    // two halting states
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(cu(2)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cu(3)),
    ]);
}

#[test]
fn test_halt_as_max_len_sym_shrink() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (list 3 bool) (list true))
        ;; shrinking
        (as-max-len? (var-get x) u2)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    // two halting states -- one where the shrink works, and one where it doesn't
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pleq(llen(var_get(sl("x", TS::BoolType, 3))), cu(2)))
            .formula(some(var_get(sl("x", TS::BoolType, 3)))),
        
        // TODO: propagate new length
        Halt::new_test()
            .pred(pgreater(llen(var_get(sl("x", TS::BoolType, 3))), cu(2)))
            .formula(none())
    ]);
}

#[test]
fn test_halt_as_max_len_sym_grow() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (list 3 bool) (list true))
        ;; shrinking
        (as-max-len? (var-get x) u4)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    // one halting state, since the new length exceeds the type's max length
    assert_halts(termination_states, vec![
        // TODO: propagate new length
        Halt::new_test()
            .pred(pleq(llen(var_get(sl("x", TS::BoolType, 3))), cu(4)))
            .formula(some(var_get(sl("x", TS::BoolType, 3)))),
    ]);
}

#[test]
fn test_halt_tuple_cons() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (define-data-var y uint u0)
        (define-data-var z (list 4 uint) (list ))

        { x: (var-get x), y: (if (var-get x) (var-get y) (+ u1 (var-get y))), z: (var-get z) }
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", var_get(su("y"))),
                ("z", var_get(sl("z", TS::UIntType, 4)))
            ])),

        Halt::new_test()
            .pred(pi(not(var_get(sb("x")))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", add2(cu(1), var_get(su("y")))),
                ("z", var_get(sl("z", TS::UIntType, 4)))
            ]))
    ]);
}

#[test]
fn test_halt_tuple_get() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (get y (if (var-get x) { y: u1 } { y: u2 }))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(cu(1)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_tuple_merge() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (merge { x: (var-get x) } (if (var-get x) { y: u1 } { y: u2 }))
        "#,
    ).unwrap();
    
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", cu(1))
            ])),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", cu(2))
            ]))
    ]);
}

#[test]
fn test_halt_begin() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (define-data-var y bool true)
        (begin
            (if (var-get x)
                (var-set x false)
                true)

            (if (var-get y)
                (var-set y false)
                true))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pand(vec![
                pi(var_get(sb("x"))),
                pi(var_get(sb("y")))
            ]))
            .formula(cb(true))
            .var(contract_id.clone(), "x", cb(false))
            .var(contract_id.clone(), "y", cb(false)),

        Halt::new_test()
            .pred(pand(vec![
                pnot(pi(var_get(sb("x")))),
                pi(var_get(sb("y")))
            ]))
            .formula(cb(true))
            .var(contract_id.clone(), "y", cb(false)),

        Halt::new_test()
            .pred(pand(vec![
                pi(var_get(sb("x"))),
                pnot(pi(var_get(sb("y"))))
            ]))
            .formula(cb(true))
            .var(contract_id.clone(), "x", cb(false)),

        Halt::new_test()
            .pred(pand(vec![
                pnot(pi(var_get(sb("x")))),
                pnot(pi(var_get(sb("y"))))
            ]))
            .formula(cb(true))
    ]);
}

#[test]
fn test_halt_default_to() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (optional bool) none)
        (default-to false (var-get x))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_some(var_get(so("x", TS::BoolType)))))
            .formula(unwrap_panic(var_get(so("x", TS::BoolType)))),

        Halt::new_test()
            .pred(pi(is_none(var_get(so("x", TS::BoolType)))))
            .formula(cb(false))
    ]);
}

#[test]
fn test_halt_asserts() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (asserts! (var-get x) (err u0))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(cb(true)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_opt() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (optional bool) (some true))
        (unwrap! (var-get x) (err u0))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_some(var_get(so("x", TS::BoolType)))))
            .formula(unwrap_panic(var_get(so("x", TS::BoolType)))),

        Halt::new_test()
            .pred(pi(is_none(var_get(so("x", TS::BoolType)))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_res() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (response bool uint) (ok true))
        (unwrap! (var-get x) (err u0))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new_test()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_err() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (response bool uint) (err u1))
        (unwrap-err! (var-get x) (err u0))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_err_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new_test()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_panic_opt() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (optional bool) (some true))
        (unwrap-panic (var-get x))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_some(var_get(so("x", TS::BoolType)))))
            .formula(unwrap_panic(var_get(so("x", TS::BoolType)))),

        Halt::new_test()
            .pred(pi(is_none(var_get(so("x", TS::BoolType)))))
            .formula(panic())
            .early_return()
            .panic()

    ]);
}

#[test]
fn test_halt_unwrap_panic_res() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (response bool uint) (ok true))
        (unwrap-panic (var-get x))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new_test()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(panic())
            .early_return()
            .panic()

    ]);
}

#[test]
fn test_halt_unwrap_err_panic() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (response bool uint) (err u0))
        (unwrap-err-panic (var-get x))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_err_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new_test()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(panic())
            .early_return()
            .panic()

    ]);
}

#[test]
fn test_halt_match_opt() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (optional uint) (some u10))
        (match (var-get x)
            y (+ y u1)
            u2)
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_some(var_get(so("x", TS::UIntType)))))
            .formula(add2(cu(1), unwrap_panic(var_get(so("x", TS::UIntType))))),

        Halt::new_test()
            .pred(pi(is_none(var_get(so("x", TS::UIntType)))))
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_match_res() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (response uint uint) (ok u10))
        (match (var-get x)
            ok-y (+ ok-y u1)
            err-y (- err-y u1))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_ok(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(add2(cu(1), unwrap_panic(var_get(sr("x", TS::UIntType, TS::UIntType))))),

        Halt::new_test()
            .pred(pi(is_err(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(sub2(unwrap_err_panic(var_get(sr("x", TS::UIntType, TS::UIntType))), cu(1)))
    ]);
}

#[test]
fn test_halt_try_opt() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (optional uint) (some u10))
        (try! (var-get x))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_some(var_get(so("x", TS::UIntType)))))
            .formula(unwrap_panic(var_get(so("x", TS::UIntType)))),

        Halt::new_test()
            .pred(pi(is_none(var_get(so("x", TS::UIntType)))))
            .formula(none())
            .early_return()
    ]);
}

#[test]
fn test_halt_try_res() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x (response uint uint) (ok u10))
        (try! (var-get x))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(is_ok(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(unwrap_panic(var_get(sr("x", TS::UIntType, TS::UIntType)))),

        Halt::new_test()
            .pred(pi(is_err(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(var_get(sr("x", TS::UIntType, TS::UIntType)))
            .early_return()
    ]);
}

#[test]
fn test_halt_symop_add() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(+ u1 (+ u2 u3 u4) u5)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(1 + 2 + 3 + 4 + 5))
    ]);
}

#[test]
fn test_halt_symop_if_constant() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(if true u2 u3)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(2)),
    ]);
}

#[test]
fn test_halt_symop_if_sym_constant() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(define-constant x true) (if x u2 u3)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    // unreachable continuation was eliminated
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_symop_if_sym_var() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(define-data-var x bool true) (if (var-get x) u2 u3)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(cu(2)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cu(3))
    ]);
}

#[test]
fn test_halt_symop_var_set_if_sym_var() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(),
        "(define-data-var x bool true) (define-data-var y uint u0) (if (var-get x) (var-set y u2) (var-set y u3))",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(cb(true))
            .var(contract_id.clone(), "y", cu(2)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cb(true))
            .var(contract_id.clone(), "y", cu(3)),
    ]);
}

#[test]
fn test_halt_symop_multiple_var_set_if_sym_var() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x bool true)
        (define-data-var y uint u0)
        (define-data-var z uint u0)
        (if (var-get x)
            (begin
                (var-set y u2)
                (var-set z u20))
            (begin
                (var-set y u3)
                (var-set z u30)))
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("x"))))
            .formula(cb(true))
            .var(contract_id.clone(), "y", cu(2))
            .var(contract_id.clone(), "z", cu(20)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cb(true))
            .var(contract_id.clone(), "y", cu(3))
            .var(contract_id.clone(), "z", cu(30))
    ]);
}

#[test]
fn test_halt_add_from_identical_ifs() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var a bool true)

        (+
            (if (var-get a) u0 u10)
            (if (var-get a) u1 u11)
            (if (var-get a) u2 u12)
            (if (var-get a) u3 u13))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("a"))))
            .formula(cu(0 + 1 + 2 + 3)),

        Halt::new_test()
            .pred(pnot(pi(var_get(sb("a")))))
            .formula(cu(10 + 11 + 12 + 13))
    ]);
}

#[test]
fn test_halt_add_from_unrelated_ifs() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var a bool true)
        (define-data-var b bool true)
        (define-data-var c bool true)
        (define-data-var d bool true)

        (+
            (if (var-get a) u0 u10)
            (if (var-get b) u1 u11)
            (if (var-get c) u2 u12)
            (if (var-get d) u3 u13))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cu(6)),
        
        Halt::new_test()
            .pred(por(vec![
                pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]),
                pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]),
                pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]),
            ]))
            .formula(cu(26)),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]),
                pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]),
                pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]),
            ]))
            .formula(cu(16)),
        
        Halt::new_test()
            .pred(por(vec![
                pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]),
                pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]),
            ]))
            .formula(cu(36)),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(10 + 11 + 12 + 13))
    ])
}

#[test]
fn test_halt_list_cons_from_same_if() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var a bool true)

        (list
            (if (var-get a) u0 u10)
            (if (var-get a) u1 u11)
            (if (var-get a) u2 u12)
            (if (var-get a) u3 u13))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pi(var_get(sb("a"))))
            .formula(cl(vec![valu(0), valu(1), valu(2), valu(3)])),
        
        Halt::new_test()
            .pred(pnot(pi(var_get(sb("a")))))
            .formula(cl(vec![valu(10), valu(11), valu(12), valu(13)]))
    ]);
}

#[test]
fn test_halt_list_cons_from_unrelated_ifs() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var a bool true)
        (define-data-var b bool true)
        (define-data-var c bool true)
        (define-data-var d bool true)

        (list
            (if (var-get a) u0 u10)
            (if (var-get b) u1 u11)
            (if (var-get c) u2 u12)
            (if (var-get d) u3 u13))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(1), valu(2), valu(3)])),

        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(1), valu(2), valu(13)])),

        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(1), valu(12), valu(3)])),
        
        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(1), valu(12), valu(13)])),

        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(11), valu(2), valu(3)])),
        
        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(11), valu(2), valu(13)])),
        
        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(11), valu(12), valu(3)])),
        
        Halt::new_test()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(11), valu(12), valu(13)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(1), valu(2), valu(3)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(1), valu(2), valu(13)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(1), valu(12), valu(3)])),
         
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(1), valu(12), valu(13)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(11), valu(2), valu(3)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(11), valu(2), valu(13)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(11), valu(12), valu(3)])),
        
        Halt::new_test()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(11), valu(12), valu(13)]))
    ])
}

#[test]
fn test_halt_function_call() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-private (foo (x uint))
            (+ u1 x))

        (foo u0)
        "#,
    ).unwrap()
    .skip_pure(false)
    .skip_causally_independent(false);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(1))
    ]);
}

#[test]
fn test_halt_mod() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(mod u2 u3)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(2 % 3))
    ]);
}

#[test]
fn test_halt_is_eq() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(is-eq u2 u3 u4)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cb(false))
    ]);
}

#[test]
fn test_halt_if_is_eq() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id,
        "(if (is-eq u2 u3 u4) u1 u2)",
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_function_call_if_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-private (foo (x uint))
            (if (is-eq (mod x u2) u0)
                (+ u1 x)
                (+ u3 x)))

        (foo u0)
        "#,
    ).unwrap()
    .skip_pure(false)
    .skip_causally_independent(false);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cu(1))
    ]);
}

#[test]
fn test_halt_function_call_if_branch_pre_post_vars() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-private (foo (x uint))
            (if (is-eq (mod x u2) u0)
                (var-set v (+ u1 x))
                (var-set v (+ u3 x))))

        (foo (var-get v))
        "#,
    ).unwrap()
    .skip_pure(false)
    .skip_causally_independent(false);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(cb(true))
            .var(contract_id.clone(), "v", add(vec![cu(1), var_get(su("v"))])),

        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cb(true))
            .var(contract_id.clone(), "v", add(vec![cu(3), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_var_get_set_tower() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var w uint u1)
        (var-set v
            (+ u1 (begin
                (var-set w
                    (+ u2 (begin
                        (var-set v
                            (+ u3 (var-get w)))
                        (var-get v))))
                (var-get w))))
        
        (var-get v)
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(add(vec![cu(6), var_get(su("w"))]))
            .var(contract_id.clone(), "w", add(vec![cu(5), var_get(su("w"))]))
            .var(contract_id.clone(), "v", add(vec![cu(6), var_get(su("w"))]))
    ]);
}

#[test]
fn test_halt_var_get_set_if_tree() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var w uint u1)

        (if (is-eq (mod (var-get v) u2) u0)
            (if (is-eq (mod (var-get w) u2) u0)
                (begin
                    (var-set v u101)
                    (var-set w u101))
                (begin
                    (var-set v u201)
                    (var-set w u200)))
            (if (is-eq (mod (var-get w) u2) u0)
                (begin
                    (var-set v u300)
                    (var-set w u301))
                (begin
                    (var-set v u400)
                    (var-set w u400))))

        (list (var-get v) (var-get w))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peqs(vec![
                rem(var_get(su("v")), cu(2)),
                rem(var_get(su("w")), cu(2)),
                cu(0)
            ]))
            .formula(cl(vec![valu(101), valu(101)]))
            .var(contract_id.clone(), "v", cu(101))
            .var(contract_id.clone(), "w", cu(101)),

        Halt::new_test()
            .pred(pand(vec![peq(rem(var_get(su("v")), cu(2)), cu(0)), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(cl(vec![valu(201), valu(200)]))
            .var(contract_id.clone(), "v", cu(201))
            .var(contract_id.clone(), "w", cu(200)),

        Halt::new_test()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), peq(rem(var_get(su("w")), cu(2)), cu(0))]))
            .formula(cl(vec![valu(300), valu(301)]))
            .var(contract_id.clone(), "v", cu(300))
            .var(contract_id.clone(), "w", cu(301)),
            
        Halt::new_test()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(cl(vec![valu(400), valu(400)]))
            .var(contract_id.clone(), "v", cu(400))
            .var(contract_id.clone(), "w", cu(400))
    ]);
}

#[test]
fn test_halt_var_get_set_tower_if_tree() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var w uint u1)
        (var-set v
            (+ (if (is-eq (mod (var-get v) u2) u0) u1 u10) (begin
                (var-set w
                    (+ (if (is-eq (mod (var-get w) u2) u0) u2 u20) (begin
                        (var-set v
                            (+ (if (is-eq (mod (var-get v) u2) u0) u3 u30) (var-get w)))
                        (var-get v))))
                (var-get w))))
        
        (var-get v)
        "#,
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peqs(vec![
                rem(var_get(su("v")), cu(2)),
                rem(var_get(su("w")), cu(2)),
                cu(0)
            ]))
            .formula(add(vec![cu(6), var_get(su("w"))]))
            .var(contract_id.clone(), "v", add(vec![cu(6), var_get(su("w"))]))
            .var(contract_id.clone(), "w", add(vec![cu(5), var_get(su("w"))])),

        Halt::new_test()
            .pred(pand(vec![peq(rem(var_get(su("v")), cu(2)), cu(0)), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(add(vec![cu(24), var_get(su("w"))]))
            .var(contract_id.clone(), "v", add(vec![cu(24), var_get(su("w"))]))
            .var(contract_id.clone(), "w", add(vec![cu(23), var_get(su("w"))])),

        Halt::new_test()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), peq(rem(var_get(su("w")), cu(2)), cu(0))]))
            .formula(add(vec![cu(42), var_get(su("w"))]))
            .var(contract_id.clone(), "v", add(vec![cu(42), var_get(su("w"))]))
            .var(contract_id.clone(), "w", add(vec![cu(32), var_get(su("w"))])),

        Halt::new_test()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(add(vec![cu(60), var_get(su("w"))]))
            .var(contract_id.clone(), "v", add(vec![cu(60), var_get(su("w"))]))
            .var(contract_id.clone(), "w", add(vec![cu(50), var_get(su("w"))]))
    ]);
}

#[test]
fn test_halt_var_get_set_if_sequence() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var w uint u1)

        (if (is-eq (mod (var-get v) u2) u0)
            (var-set w u20)
            (var-set v u4))

        (if (is-eq (mod (var-get v) u3) u0)
            (var-set w u30)
            (var-set v u5))

        (if (is-eq (mod (var-get v) u5) u0)
            (var-set w u40)
            (var-set v u6))

        (list (var-get v) (var-get w))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peqs(vec![
                rem(var_get(su("v")), cu(2)),
                rem(var_get(su("v")), cu(3)),
                rem(var_get(su("v")), cu(5)),
                cu(0)
            ]))
            .formula(lcons(vec![var_get(su("v")), cu(40)]))
            .var(contract_id.clone(), "w", cu(40)),

        Halt::new_test()
            .pred(pand(vec![
                peqs(vec![
                    rem(var_get(su("v")), cu(2)),
                    rem(var_get(su("v")), cu(3)),
                    cu(0)
                ]),
                pnot(peq(rem(var_get(su("v")), cu(5)), cu(0)))
            ]))
            .formula(cl(vec![valu(6), valu(30)]))
            .var(contract_id.clone(), "v", cu(6))
            .var(contract_id.clone(), "w", cu(30)),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(rem(var_get(su("v")), cu(2)), cu(0)),
                    pnot(peq(rem(var_get(su("v")), cu(3)), cu(0)))
                ]),
                pnot(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            ]))
            .formula(cl(vec![valu(5), valu(40)]))
            .var(contract_id.clone(), "v", cu(5))
            .var(contract_id.clone(), "w", cu(40)),
    ])
}

#[test]
fn test_halt_simplify_var_get_const() {
    let contract_id = default_contract_id();
    let var_name = FullName(contract_id, "foo".try_into().unwrap());
    let symop = SymOp::LoadedDataVariable(var_name, Box::new(SymOp::Constant(Value::UInt(3))));
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *cu(3));

    let symop = SymOp::Modulo(Box::new(symop.clone()), Box::new(SymOp::Constant(Value::UInt(3))));
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *cu(0));
    
    let symop = SymOp::Equals(vec![Box::new(symop.clone()), Box::new(SymOp::Constant(Value::UInt(0)))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *cb(true));
}

#[test]
fn test_halt_let_bind() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (let (
            (a (var-get v))
            (b (+ u1 a))
            (c (+ u2 b))
        )
        (var-set v c))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(cb(true))
            .var(contract_id.clone(), "v", add(vec![cu(3), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_if_let_bind() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (let (
            (a (var-get v))
            (b (if (is-eq (mod a u2) u0) (+ u1 a) (+ u2 a)))
        )
        (var-set v b))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(cb(true))
            .var(contract_id.clone(), "v", add(vec![cu(1), var_get(su("v"))])),
        
        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cb(true))
            .var(contract_id.clone(), "v", add(vec![cu(2), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_if_let_var_set_bind() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (let (
            (a (var-get v))
            (b (if (is-eq (mod a u2) u0) false (var-set v (+ u2 a))))
            (c (if b (var-get v) u10))
        )
        (var-set v c))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(cb(true))
            .var(contract_id.clone(), "v", cu(10)),

        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cb(true))
            .var(contract_id.clone(), "v", add(vec![cu(2), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_map_user_func() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (x uint))
           (+ (var-get v) x))

        (map fetch-add (list u0 u1 u2 u3))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(lcons(vec![var_get(su("v")), add2(cu(1), var_get(su("v"))), add2(cu(2), var_get(su("v"))), add2(cu(3), var_get(su("v")))]))
    ]);
}

#[test]
fn test_halt_map_user_func_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (fetch-add-sub (x uint))
           (if (is-eq (mod (var-get v) u2) u0)
              (+ (var-get v) x)
              (- (var-get v) x)))

        (map fetch-add-sub (list u0 u1 u2 u3))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(lcons(vec![var_get(su("v")), add2(cu(1), var_get(su("v"))), add2(cu(2), var_get(su("v"))), add2(cu(3), var_get(su("v")))])),
        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(lcons(vec![var_get(su("v")), sub2(var_get(su("v")), cu(1)), sub2(var_get(su("v")), cu(2)), sub2(var_get(su("v")), cu(3))]))
    ])
}

#[test]
fn test_alt_map_sequence_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (x uint))
           (+ (var-get v) x))

        (map fetch-add (if (is-eq (mod (var-get v) u2) u0) (list u0 u1 u2 u3) (list u10 u11 u12 u13)))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(lcons(vec![var_get(su("v")), add2(cu(1), var_get(su("v"))), add2(cu(2), var_get(su("v"))), add2(cu(3), var_get(su("v")))])),
        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(lcons(vec![add2(cu(10), var_get(su("v"))), add2(cu(11), var_get(su("v"))), add2(cu(12), var_get(su("v"))), add2(cu(13), var_get(su("v")))]))
    ])
}

#[test]
fn test_halt_map_symbolic_list() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var list-v (list 4 uint) (list u0 u1 u2 u3))

        (define-private (fetch-add (x uint))
           (+ (var-get v) x))

        (map fetch-add (var-get list-v))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(cu(0), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(cl(vec![])),

        Halt::new_test()
            .pred(peq(cu(1), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0))))
            ])),

        Halt::new_test()
            .pred(peq(cu(2), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(1))))
            ])),
        
        Halt::new_test()
            .pred(peq(cu(3), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(1)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(2))))
            ])),
        
        Halt::new_test()
            .pred(peq(cu(4), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(1)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(2)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(3))))
            ]))
    ]);
}

#[test]
fn test_halt_map_symbolic_lists() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var list-v1 (list 4 uint) (list u0 u1 u10 u11))
        (define-data-var list-v2 (list 4 uint) (list u2 u3 u12 u13))
        (define-data-var list-v3 (list 4 uint) (list u4 u5 u14 u15))

        (define-private (fetch-add (x uint) (y uint) (z uint))
           (+ (var-get v) x y z))

        (map fetch-add (var-get list-v1) (var-get list-v2) (var-get list-v3))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(por(vec![
                peq(cu(0), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
                peq(cu(0), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
                peq(cu(0), llen(var_get(sl("list-v3", TS::UIntType, 4))))
            ]))
            .formula(cl(vec![])),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(cu(1), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(1)),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(1))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(1)),
                    peq(cu(1), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(1))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(1)),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(1)),
                    peq(cu(1), llen(var_get(sl("list-v3", TS::UIntType, 4))))
                ]),
            ]))
            .formula(lcons(vec![
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(0))),
                ])
            ])),
        
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(cu(2), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(2)),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(2))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(2)),
                    peq(cu(2), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(2))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(2)),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(2)),
                    peq(cu(2), llen(var_get(sl("list-v3", TS::UIntType, 4))))
                ]),
            ]))
            .formula(lcons(vec![
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(0))),
                ]),
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(1))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(1))),
                ])
            ])),
        
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(cu(3), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(3)),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(3))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(3)),
                    peq(cu(3), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(3))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(3)),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(3)),
                    peq(cu(3), llen(var_get(sl("list-v3", TS::UIntType, 4))))
                ]),
            ]))
            .formula(lcons(vec![
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(0))),
                ]),
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(1))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(1))),
                ]),
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(2))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(2))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(2))),
                ])
            ])),
        
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(cu(4), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(4)),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(4))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(4)),
                    peq(cu(4), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
                    pgeq(llen(var_get(sl("list-v3", TS::UIntType, 4))), cu(4))
                ]),
                pand(vec![
                    pgeq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(4)),
                    pgeq(llen(var_get(sl("list-v2", TS::UIntType, 4))), cu(4)),
                    peq(cu(4), llen(var_get(sl("list-v3", TS::UIntType, 4))))
                ]),
            ]))
            .formula(lcons(vec![
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(0))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(0))),
                ]),
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(1))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(1))),
                ]),
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(2))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(2))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(2))),
                ]),
                add(vec![
                    var_get(su("v")),
                    unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(3))),
                    unwrap_panic(elat(var_get(sl("list-v2", TS::UIntType, 4)), cu(3))),
                    unwrap_panic(elat(var_get(sl("list-v3", TS::UIntType, 4)), cu(3))),
                ])
            ])),
    ]);
}

#[test]
fn test_halt_fold_user_func() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (idx uint) (value uint))
           (+ (var-get v) idx value))

        (fold fetch-add (list u0 u1 u2 u3) u10)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(add(vec![
                mul2(cu(4), var_get(su("v"))),
                cu(16)
            ]))
        
    ]);
}

#[test]
fn test_halt_fold_user_func_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (fetch-add-sub (x uint) (value uint))
           (if (is-eq (mod (var-get v) u2) u0)
              (+ (var-get v) x value)
              (- (var-get v) x value)))

        ;; If v is odd, then this `fold` evaluates to:
        ;; ((var-get v) - u0 - u10)                     --> ((var-get v) - u10)
        ;; ((var-get v) - u1 - ((var-get v) - u10))     --> u9
        ;; ((var-get v) - u2 - u9)                      --> ((var-get v) - u11)
        ;; ((var-get v) - u3 - ((var-get v) - u11))     --> u8
        (fold fetch-add-sub (list u0 u1 u2 u3) u10)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(add(vec![
                mul2(cu(4), var_get(su("v"))),
                cu(16)
            ])),

        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cu(8))
    ]);
}

#[test]
fn test_halt_fold_sequence_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (x uint) (value uint))
           (+ (var-get v) x value))

        (fold fetch-add (if (is-eq (mod (var-get v) u2) u0) (list u0 u1 u2 u3) (list u10 u11 u12 u13)) u10)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(add2(mul2(var_get(su("v")), cu(4)), cu(16))),

        Halt::new_test()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(add2(mul2(var_get(su("v")), cu(4)), cu(56))),
    ]);
}

#[test]
fn test_halt_fold_symbolic_lists() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)
        (define-data-var list-v1 (list 4 uint) (list u0 u1 u10 u11))

        (define-private (fetch-add (x uint) (value uint))
           (+ (var-get v) x value))

        (fold fetch-add (var-get list-v1) u10)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(0)))
            .formula(cu(10)),

        Halt::new_test()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(1)))
            .formula(add(vec![
                var_get(su("v")),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                cu(10)
            ])),

        Halt::new_test()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(2)))
            .formula(add(vec![
                mul2(cu(2), var_get(su("v"))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                cu(10)
            ])),

        Halt::new_test()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(3)))
            .formula(add(vec![
                mul2(cu(3), var_get(su("v"))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(2))),
                cu(10)
            ])),

        Halt::new_test()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(4)))
            .formula(add(vec![
                mul2(cu(4), var_get(su("v"))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(2))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(3))),
                cu(10)
            ]))
    ]);
}

#[test]
fn test_halt_filter_list_user_func() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u1)

        (define-private (parity (x uint))
            (is-eq (mod x u2) (var-get v)))

        (filter parity (list u0 u1 u2 u3))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(var_get(su("v")), cu(0)))
            .formula(cl(vec![valu(0), valu(2)])),

        Halt::new_test()
            .pred(peq(var_get(su("v")), cu(1)))
            .formula(cl(vec![valu(1), valu(3)])),

        Halt::new_test()
            .pred(pand(vec![pnot(peq(var_get(su("v")), cu(0))), pnot(peq(var_get(su("v")), cu(1)))]))
            .formula(cl(vec![]))
    ]);
}

#[test]
fn test_halt_filter_user_func_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u0)

        (define-private (parity-is-three (x uint))
           (if (is-eq (mod x u2) u0)
              (is-eq (var-get v) u3)
              (is-eq x u3)))

        (filter parity-is-three (list u0 u1 u2 u3))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(var_get(su("v")), cu(3)))
            .formula(cl(vec![valu(0), valu(2), valu(3)])),

        Halt::new_test()
            .pred(pnot(peq(var_get(su("v")), cu(3))))
            .formula(cl(vec![valu(3)]))
    ]);
}

#[test]
fn test_halt_filter_sequence_branch() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u1)

        (define-private (parity (x uint))
            (is-eq (mod x u2) (var-get v)))

        (filter parity (if (is-eq (var-get v) u1) (list u0 u1 u2 u3) (list u5 u10 u15 u20)))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(var_get(su("v")), cu(1)))
            .formula(cl(vec![valu(1), valu(3)])),

        Halt::new_test()
            .pred(peq(var_get(su("v")), cu(0)))
            .formula(cl(vec![valu(10), valu(20)])),

        Halt::new_test()
            .pred(pand(vec![pnot(peq(var_get(su("v")), cu(0))), pnot(peq(var_get(su("v")), cu(1)))]))
            .formula(cl(vec![]))
    ]);
}

#[test]
fn test_halt_filter_symbolic_lists() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var v uint u1)
        (define-data-var l (list 3 uint) (list u0 u1 u2))

        (define-private (parity (x uint))
            (is-eq (mod x u2) (var-get v)))

        (filter parity (var-get l))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(1)),
                    peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))
                ]),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                    peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2))),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
                ]),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                    peqs(vec![
                        var_get(su("v")),
                        rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2))
                    ]),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
                ])
            ]))
            .formula(lcons(vec![unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0)))])),
        
        Halt::new_test()
            .pred(por(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(0)),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(1)),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2))))
                ]),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
                ]),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
                ])
            ]))
            .formula(cl(vec![])),
           
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                    peqs(vec![
                        var_get(su("v")),
                        rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)),
                        rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)),
                    ])
                ]),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                    peqs(vec![
                        var_get(su("v")),
                        rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)),
                        rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)),
                    ]),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
                ]),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1)))
            ])),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                    peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2))),
                ]),
                pand(vec![
                    peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                    peqs(vec![
                        var_get(su("v")),
                        rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2))
                    ]),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                    pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
                ]),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))),
            ])),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2))
                ])
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2)))
            ])),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2))
                ]),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))),
            ])),
        
        Halt::new_test()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2))
                ]),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))),
            ])),
        
        Halt::new_test()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2))
                ]),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))),
            ])),
    ]);
}

#[test]
fn test_halt_map_get() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (define-private (add-or-square (x uint))
            (match (map-get? squares x)
                y (* y y)
                (+ x x)))

        (add-or-square u3)
        "#,
    ).unwrap()
    .skip_pure(false)
    .skip_causally_independent(false);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        let t = t.clone().rollup();
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t);
        assert!(t.map_accesses.iter().find(|ma| {
            ma.name.name().as_str() == "squares" 
            && ma.key == *vu("x")
        }).is_some());
        assert!(t.pre_map_state.get(&FullName(contract_id.clone(), ClarityName::try_from("squares").unwrap())).unwrap().get(&cu(3)).is_some());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pis_some(map_get("squares", cu(3))))
            .formula(pow(unwrap_panic(map_get("squares", cu(3))), cu(2))),
        
        Halt::new_test()
            .pred(pis_none(map_get("squares", cu(3))))
            .formula(cu(6))
    ]);
}

#[test]
fn test_halt_map_set() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (define-private (add-and-square (x uint))
            (match (map-get? squares x)
                y (map-set squares y (* y y))
                (map-set squares x (+ x x))))

        (add-and-square u3)
        "#,
    ).unwrap()
    .skip_pure(false)
    .skip_causally_independent(false);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pis_some(map_get("squares", cu(3))))
            .formula(cb(true))
            .map(contract_id.clone(), "squares", unwrap_panic(map_get("squares", cu(3))), pow(unwrap_panic(map_get("squares", cu(3))), cu(2))),

        Halt::new_test()
            .pred(pis_none(map_get("squares", cu(3))))
            .formula(cb(true))
            .map(contract_id.clone(), "squares", cu(3), cu(6))
    ]);
}

#[test]
fn test_halt_multiple_map_set() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (begin
            (map-set squares u1 u1)
            (map-set squares u1 u2)
            (map-set squares u1 u3))

        (map-get? squares u1)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(co(valu(3)))
            .map(contract_id.clone(), "squares", cu(1), cu(3))
    ]);
}

#[test]
fn test_halt_multiple_sym_map_set() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var x uint u1)
        (define-map squares uint uint)

        (begin
            (map-set squares (var-get x) (var-get x))
            (map-set squares (var-get x) (+ u1 (var-get x)))
            (map-set squares (var-get x) (+ u2 (var-get x))))

        (map-get? squares (var-get x))
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(some(add2(cu(2), var_get(su("x")))))
            .map(contract_id.clone(), "squares", var_get(su("x")), add2(cu(2), var_get(su("x"))))
    ]);
}

#[test]
fn test_halt_multiple_map_get_none() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (begin
            (map-set squares u1 u1)
            (map-set squares u1 u2)
            (map-set squares u1 u3))

        (map-get? squares u2)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(map_get("squares", cu(2)))
            .map(contract_id.clone(), "squares", cu(1), cu(3))
    ]);
}

#[test]
fn test_halt_map_set_delete() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (begin
            (map-set squares u1 u1)
            (map-set squares u1 u2)
            (map-set squares u1 u3)
            (map-delete squares u1))

        (map-get? squares u1)
        "#,
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(none())
            .mapd(contract_id.clone(), "squares", cu(1))
    ]);
}

#[test]
fn test_halt_limit_function_exploration() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (define-private (ignored-function (x uint) (y uint))
            (map-set squares x (* y y)))

        (define-private (store-squares (x uint) (y uint))
            (begin
                (ignored-function x y)
                (ignored-function y x)))

        (store-squares u2 u3)
        "#,
    )
    .unwrap()
    .with_skipped_function_call(FullName::try_from(format!("{contract_id}.ignored-function")).unwrap());

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pt())
            .formula(fcall(&format!("{contract_id}.ignored-function"), vec![cu(3), cu(2)]))
            .reachable_map_write(contract_id.clone(), "squares")
    ]);
}

#[test]
fn test_halt_eager_function_evaluation() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)

        (define-private (evaled-function (x uint) (y uint))
            (begin
                (map-set squares x (* y y))
                y))

        (define-private (store-squares (x uint) (y uint))
            (begin
                (fold evaled-function (list x y) y)
                (asserts! (is-eq x u2) (err u1))
                (ok true)))

        (store-squares u2 u3)
        "#,
    )
    .unwrap()
    .with_function_call_exploration(true);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_rollup_early_return() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-public (early-return-if-mod-6 (x uint))
            (begin
                (asserts! (is-eq (mod x u3) u0) (err u1))
                (asserts! (is-eq (mod x u2) u0) (err u2))
                (ok (* x x x))))

        (define-data-var input uint u12)
        (early-return-if-mod-6 (var-get input))
        "#,
    )
    .unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pnot(peq(rem(lv("input", vu("input")), cu(3)), cu(0))))
            .formula(cerr(valu(1)))
            .early_return(),
        
        Halt::new_test()
            .pred(pand(vec![peq(rem(lv("input", vu("input")), cu(3)), cu(0)), pnot(peq(rem(lv("input", vu("input")), cu(2)), cu(0)))]))
            .formula(cerr(valu(2)))
            .early_return(),

        Halt::new_test()
            .pred(peqs(vec![rem(lv("input", vu("input")), cu(2)), rem(lv("input", vu("input")), cu(3)), cu(0)]))
            .formula(ok(pow(lv("input", vu("input")), cu(3))))
    ]);
}

#[test]
fn test_halt_contract_call() {
    let library_contract_id = make_contract_id("library");
    let client_contract_id = make_contract_id("client");

    let mut symbex = Symbex::from_contracts(vec![
            (
                library_contract_id.clone(),
                r#"
                (define-map squares uint uint)
                (define-map cubes uint uint)
                (define-map quads uint uint)

                (define-read-only (get-square (x uint))
                    (default-to u0 (map-get? squares x)))

                (define-read-only (get-cube (x uint))
                    (default-to (* x (get-square x)) (map-get? cubes x)))

                (define-public (insert-cube (x uint))
                    (if true
                        (ok (map-insert cubes x (* x x x)))
                        (err u0)))

                (define-public (compute (x uint))
                    (if (is-eq u0 (mod x u3))
                        (let (
                            (y (get-square x))
                        )
                        (ok (map-insert quads x (* y y))))
                        (let (
                            (y (get-cube x))
                        )
                        (insert-cube y))))

                "#.to_string(),
                None
            ),
            (
                client_contract_id.clone(),
                r#"
                (define-map squares uint uint)
                (define-map quints uint uint)

                (define-read-only (get-square (x uint))
                    (default-to (contract-call? .library get-square x) (map-get? squares x)))

                (define-read-only (compute-quint (x uint))
                    (* (contract-call? .library get-cube x) (get-square x)))

                (define-public (insert-quint (x uint) (x_5 uint))
                    (if true
                        (ok (map-insert quints x x_5))
                        (err u0)))

                (define-public (compute (x uint))
                    (if (is-eq u0 (mod x u3))
                        (contract-call? .library compute x)
                        (insert-quint x (compute-quint x))))

                ;; NOTE: can't call this `x` since it seems to trigger a Clarity bug
                ;; whereby the `x` in `get-square` will seem to be already used.
                (define-data-var xx uint u10)
                (compute (var-get xx))
                "#.to_string(),
                None
            )
        ],
        1
    )
    .unwrap()
    .skip_causally_independent(false);

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pand(vec![
                peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0)),
                pis_none(fq_map_get(&library_contract_id, "quads", fq_var_get(&client_contract_id, su("xx")))),
                pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
            ]))
            .formula(cok(valb(true)))
            .map(library_contract_id.clone(), "quads", fq_var_get(&client_contract_id, su("xx")), pow(unwrap_panic(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))), cu(2)))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),

        Halt::new_test()
            .pred(pand(vec![
                peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0)),
                pis_none(fq_map_get(&library_contract_id, "quads", fq_var_get(&client_contract_id, su("xx")))),
                pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
            ]))
            .formula(cok(valb(true)))
            .map(library_contract_id.clone(), "quads", fq_var_get(&client_contract_id, su("xx")), cu(0))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),

        Halt::new_test()
            .pred(pand(vec![
                pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
            ]))
            .formula(cok(valb(true)))
            .map(client_contract_id.clone(), "quints", fq_var_get(&client_contract_id, su("xx")), mul(vec![
                unwrap_panic(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                unwrap_panic(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
            ]))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
                ]),
            ]))
            .formula(cok(valb(true)))
            .map(client_contract_id.clone(), "quints", fq_var_get(&client_contract_id, su("xx")), mul(vec![
                unwrap_panic(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                unwrap_panic(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
            ]))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),
       
        Halt::new_test()
            .pred(pand(vec![
                pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
            ]))
            .formula(cok(valb(true)))
            .map(client_contract_id.clone(), "quints", fq_var_get(&client_contract_id, su("xx")), mul(vec![
                unwrap_panic(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                unwrap_panic(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                fq_var_get(&client_contract_id, su("xx"))
            ]))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),

        Halt::new_test()
            .pred(pand(vec![
                pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
            ]))
            .formula(cok(valb(true)))
            .map(client_contract_id.clone(), "quints", fq_var_get(&client_contract_id, su("xx")), mul(vec![
                fq_var_get(&client_contract_id, su("xx")),
                pow(unwrap_panic(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))), cu(2))
            ]))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_none(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx"))))
                ]),
            ]))
            .formula(cok(valb(true)))
            .map(client_contract_id.clone(), "quints", fq_var_get(&client_contract_id, su("xx")), cu(0))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0)),
                    pis_some(fq_map_get(&library_contract_id, "quads", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0)),
                    pis_some(fq_map_get(&library_contract_id, "quads", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_none(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ]),
                pand(vec![
                    pnot(peq(rem(fq_var_get(&client_contract_id, su("xx")), cu(3)), cu(0))),
                    pis_some(fq_map_get(&client_contract_id, "quints", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&client_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "cubes", fq_var_get(&client_contract_id, su("xx")))),
                    pis_some(fq_map_get(&library_contract_id, "squares", fq_var_get(&client_contract_id, su("xx")))),
                ])
            ]))
            .formula(cok(valb(false)))
            .reachable_map_write(library_contract_id.clone(), "cubes")
            .reachable_map_write(library_contract_id.clone(), "quads")
            .reachable_map_write(client_contract_id.clone(), "quints"),
    ]);
}

#[test]
fn test_halt_trait_contract_call() {
    let trait_contract_id = make_contract_id("library-trait");
    let library_contract_id = make_contract_id("library");
    let client_contract_id = make_contract_id("client");

    let mut symbex = Symbex::from_contracts(vec![
            (
                trait_contract_id.clone(),
                r#"
                (define-trait calc
                    (
                        (add (uint uint) (response uint uint))
                    )
                )
                "#.to_string(),
                None
            ),
            (
                library_contract_id.clone(),
                r#"
                (impl-trait .library-trait.calc)

                (define-public (add (x uint) (y uint))
                    (ok (+ x y)))
                "#.to_string(),
                None
            ),
            (
                client_contract_id.clone(),
                r#"
                (use-trait calc-trait .library-trait.calc)

                (define-constant OP_ADD u0)

                (define-constant ERR_NO_SUCH_OP u2000)

                (define-public (compute (calc <calc-trait>) (op uint) (a uint) (b uint))
                    (if (is-eq op OP_ADD)
                        (contract-call? calc add a b)
                        (err ERR_NO_SUCH_OP)))

                "#.to_string(),
                None
            )
        ],
        2
    )
    .unwrap()
    .skip_causally_independent(false)
    .skip_pure(false) 
    .concretize_trait(FullName(client_contract_id.clone(), "compute".try_into().unwrap()), "calc".try_into().unwrap(), library_contract_id.clone())
    .init()
    .unwrap();

    let termination_states = symbex.eval_user_function("compute").unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(vu("op"), cu(0)))
            .formula(ok(add2(vu("a"), vu("b")))),
        
        Halt::new_test()
            .pred(pnot(peq(vu("op"), cu(0))))
            .formula(cerr(valu(2000)))
    ]);
}


#[test]
fn test_callgraph_reachability_trait_contract_call() {
    let trait_contract_id = make_contract_id("library-trait");
    let library_contract_id = make_contract_id("library");
    let client_contract_id = make_contract_id("client");

    let symbex = Symbex::from_contracts(vec![
            (
                trait_contract_id.clone(),
                r#"
                (define-trait calc
                    (
                        (add (uint uint) (response uint uint))
                        (sub (uint uint) (response uint uint))
                        (mul (uint uint) (response uint uint))
                        (div (uint uint) (response uint uint))
                    )
                )
                "#.to_string(),
                None
            ),
            (
                library_contract_id.clone(),
                r#"
                (impl-trait .library-trait.calc)

                (define-constant OP_ADD u0)
                (define-constant OP_SUB u1)
                (define-constant OP_MUL u2)
                (define-constant OP_DIV u3)

                (define-constant ERR_DUPLICATE_LOG u100)

                (define-data-var op-log-len uint u0)
                (define-map op-log uint { op: uint, args: (list 2 uint), res: (response uint uint) })

                (define-private (do-op-and-log (op uint) (x uint) (y uint) (val uint))
                    (let (
                        (log-len (var-get op-log-len))
                    )
                    (asserts! (map-insert op-log log-len { op: op, args: (list x y), res: (ok val) }) (err ERR_DUPLICATE_LOG))
                    (ok val)))

                (define-public (add (x uint) (y uint))
                    (do-op-and-log OP_ADD x y (+ x y)))

                (define-public (sub (x uint) (y uint))
                    (do-op-and-log OP_SUB x y (- x y)))

                (define-public (mul (x uint) (y uint))
                    (do-op-and-log OP_MUL x y (* x y)))

                (define-public (div (x uint) (y uint))
                    (do-op-and-log OP_DIV x y (/ x y)))
                    
                "#.to_string(),
                None
            ),
            (
                client_contract_id.clone(),
                r#"
                (use-trait calc-trait .library-trait.calc)

                (define-constant OP_ADD u0)
                (define-constant OP_SUB u1)
                (define-constant OP_MUL u2)
                (define-constant OP_DIV u3)

                (define-constant ERR_NO_SUCH_OP u2000)

                (define-public (compute (calc <calc-trait>) (op uint) (x uint) (y uint))
                    (if (is-eq op OP_ADD)
                        (contract-call? calc add x y)
                    (if (is-eq op OP_SUB)
                        (contract-call? calc sub x y)
                    (if (is-eq op OP_MUL)
                        (contract-call? calc mul x y)
                    (if (is-eq op OP_DIV)
                        (contract-call? calc div x y)
                    (err ERR_NO_SUCH_OP))))))

                "#.to_string(),
                None
            )
        ],
        2
    )
    .unwrap()
    .skip_causally_independent(false)
    .concretize_trait(FullName(client_contract_id.clone(), "compute".try_into().unwrap()), "calc".try_into().unwrap(), library_contract_id.clone())
    .init()
    .unwrap();

    let fq_name = FullName(client_contract_id.clone(), "compute".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap();
    info!("reachable from 'compute': {:?}", &reachable);

    assert_eq!(reachable, vec![
        FullName(library_contract_id.clone(), "do-op-and-log".try_into().unwrap()),
        FullName(library_contract_id.clone(), "div".try_into().unwrap()),
        FullName(library_contract_id.clone(), "mul".try_into().unwrap()),
        FullName(library_contract_id.clone(), "sub".try_into().unwrap()),
        FullName(library_contract_id.clone(), "add".try_into().unwrap())
    ]);
}

        
#[test]
fn test_callgraph_reachability_functions() {
    let contract_id = default_contract_id();
    let symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-private (mul (x uint) (y uint))
            (* x y))

        (define-read-only (add (x uint) (y uint))
            (+ x y))

        (define-private (div (x uint) (y uint))
            (/ x y))

        (define-private (summer (addand uint) (total uint))
            (+ addand total))

        (define-public (compute (x uint) (y uint))
            (let (
                (quot (div x y))
                (mul-add (add (mul x quot) y))
                (sum (fold summer (list quot mul-add x) u0))
            )
            (ok (mul u2 sum))))

        (compute u20 u4)
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(contract_id.clone(), "compute".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap();
    info!("reachable from 'compute': {:?}", &reachable);

    // call order is preserved, and no duplicates
    assert_eq!(reachable, vec![
        FullName(contract_id.clone(), "summer".try_into().unwrap()),
        FullName(contract_id.clone(), "mul".try_into().unwrap()),
        FullName(contract_id.clone(), "add".try_into().unwrap()),
        FullName(contract_id.clone(), "div".try_into().unwrap()),
    ]);

    let fq_name = FullName(contract_id.clone(), "div".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap();
    assert_eq!(reachable, vec![]);

    let fq_name = FullName(contract_id.clone(), "nope".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap_err();
    assert_eq!(reachable, Error::NotFound(format!("{fq_name}")));
}
    
#[test]
fn test_callgraph_reachability_contract_functions() {
    let library_contract_id = make_contract_id("library");
    let client_contract_id = make_contract_id("client");

    let symbex = Symbex::from_contracts(vec![
            (
                library_contract_id.clone(),
                r#"
                (define-private (mul (x uint) (y uint))
                    (* x y))

                (define-read-only (add (x uint) (y uint))
                    (+ x y))

                (define-public (div (x uint) (y uint))
                    (if true
                        (ok (/ x y))
                        (err u0)))

                (define-private (summer (addand uint) (total uint))
                    (+ addand total))

                (define-public (lib-compute (x uint) (y uint))
                    (let (
                        (quot (try! (div x y)))
                        (mul-add (add (mul x quot) y))
                        (sum (fold summer (list quot mul-add x) u0))
                    )
                    (ok (mul u2 sum))))

                "#.to_string(),
                None
            ),
            (
                client_contract_id.clone(),
                r#"
                (define-private (double (x uint) (y uint))
                    (+
                        (contract-call? .library add x y)
                        (contract-call? .library add x y)
                    ))

                (define-public (add-div (x uint) (y uint))
                    (contract-call? .library div (+ x y) y))

                (define-public (compute (x uint) (y uint))
                    (let (
                        (quot (try! (add-div (double x y) y)))
                        (dd (double (double x quot) y))
                    )
                    (ok (+ quot dd))))
                "#.to_string(),
                None
            )
        ],
        1
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(client_contract_id.clone(), "compute".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap();
    info!("reachable from 'compute': {:?}", &reachable);

    assert_eq!(reachable, vec![
        FullName(library_contract_id.clone(), "add".try_into().unwrap()),
        FullName(library_contract_id.clone(), "div".try_into().unwrap()),
        FullName(client_contract_id.clone(), "double".try_into().unwrap()),
        FullName(client_contract_id.clone(), "add-div".try_into().unwrap()),
    ]);
    
    let fq_name = FullName(client_contract_id.clone(), "add-div".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap();
    info!("reachable from 'add-div': {:?}", &reachable);

    assert_eq!(reachable, vec![
        FullName(library_contract_id.clone(), "div".try_into().unwrap()),
    ]);
    
    let fq_name = FullName(client_contract_id.clone(), "double".try_into().unwrap());
    let reachable = symbex.callgraph().reachable_from(&fq_name).unwrap();
    info!("reachable from 'double': {:?}", &reachable);
    
    assert_eq!(reachable, vec![
        FullName(library_contract_id.clone(), "add".try_into().unwrap()),
    ]);
}

#[test]
fn test_callgraph_reachability_contract_map_reads() {
    let library_contract_id = make_contract_id("library");
    let client_contract_id = make_contract_id("client");

    let symbex = Symbex::from_contracts(vec![
            (
                library_contract_id.clone(),
                r#"
                (define-map squares uint uint)
                (define-map cubes uint uint)
                (define-map quads uint uint)

                (define-read-only (get-square (x uint))
                    (default-to u0 (map-get? squares x)))

                (define-read-only (get-cube (x uint))
                    (default-to (* x (get-square x)) (map-get? cubes x)))

                (define-public (insert-cube (x uint))
                    (if true
                        (ok (map-insert cubes x (* x x x)))
                        (err u0)))

                (define-public (compute (x uint))
                    (if (is-eq u0 (mod x u3))
                        (let (
                            (y (get-square x))
                        )
                        (ok (map-insert quads x (* y y y y))))
                        (let (
                            (y (get-cube x))
                        )
                        (insert-cube y))))

                "#.to_string(),
                None
            ),
            (
                client_contract_id.clone(),
                r#"
                (define-map squares uint uint)
                (define-map quints uint uint)

                (define-read-only (get-square (x uint))
                    (default-to (contract-call? .library get-square x) (map-get? squares x)))

                (define-read-only (compute-quint (x uint))
                    (* (contract-call? .library get-cube x) (get-square x)))

                (define-public (insert-quint (x uint) (x_5 uint))
                    (if true
                        (ok (map-insert quints x x_5))
                        (err u0)))

                (define-public (compute (x uint))
                    (if (is-eq u0 (mod x u3))
                        (contract-call? .library compute x)
                        (insert-quint x (compute-quint x))))

                "#.to_string(),
                None
            )
        ],
        1
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(client_contract_id.clone(), "compute".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(library_contract_id.clone(), "squares".try_into().unwrap()),
        FullName(library_contract_id.clone(), "cubes".try_into().unwrap()),
        FullName(client_contract_id.clone(), "squares".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_access_set, expected_accesses);
    
    let fq_name = FullName(client_contract_id.clone(), "get-square".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(library_contract_id.clone(), "squares".try_into().unwrap()),
        FullName(client_contract_id.clone(), "squares".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_access_set, expected_accesses);
    
    let fq_name = FullName(client_contract_id.clone(), "compute-quint".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(library_contract_id.clone(), "squares".try_into().unwrap()),
        FullName(library_contract_id.clone(), "cubes".try_into().unwrap()),
        FullName(client_contract_id.clone(), "squares".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_access_set, expected_accesses);
    
    let fq_name = FullName(client_contract_id.clone(), "insert-quint".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = HashSet::new();

    assert_eq!(map_access_set, expected_accesses);
}

#[test]
fn test_callgraph_reachability_map_reads() {
    let contract_id = default_contract_id();
    let symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)
        (define-map cubes uint uint)
        (define-map quads uint uint)

        (define-private (get-square (x uint))
            (default-to u0 (map-get? squares x)))

        (define-private (get-cube (x uint))
            (default-to (* x (get-square x)) (map-get? cubes x)))

        (define-private (insert-cube (x uint))
            (map-insert cubes x (* x x x)))

        (define-private (compute (x uint))
            (if (is-eq u0 (mod x u3))
                (let (
                    (y (get-square x))
                )
                (map-insert quads x (* y y y y)))
                (let (
                    (y (get-cube x))
                )
                (insert-cube y))))

        (compute u21)
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(contract_id.clone(), "compute".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(contract_id.clone(), "squares".try_into().unwrap()),
        FullName(contract_id.clone(), "cubes".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_access_set, expected_accesses);
    
    let fq_name = FullName(contract_id.clone(), "get-square".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(contract_id.clone(), "squares".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_access_set, expected_accesses);
    
    let fq_name = FullName(contract_id.clone(), "get-cube".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(contract_id.clone(), "squares".try_into().unwrap()),
        FullName(contract_id.clone(), "cubes".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_access_set, expected_accesses);
    
    let fq_name = FullName(contract_id.clone(), "insert-cube".try_into().unwrap());
    let map_accesses = symbex.callgraph().reachable_map_accesses_from(&fq_name).unwrap();

    let map_access_set : HashSet<_> = map_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = HashSet::new();

    assert_eq!(map_access_set, expected_accesses);
}

#[test]
fn test_callgraph_reachability_contract_map_writes() {
    let library_contract_id = make_contract_id("library");
    let client_contract_id = make_contract_id("client");

    let symbex = Symbex::from_contracts(vec![
            (
                library_contract_id.clone(),
                r#"
                (define-map squares uint uint)
                (define-map cubes uint uint)
                (define-map quads uint uint)

                (define-read-only (get-square (x uint))
                    (default-to u0 (map-get? squares x)))

                (define-read-only (get-cube (x uint))
                    (default-to (* x (get-square x)) (map-get? cubes x)))

                (define-public (insert-cube (x uint))
                    (if true
                        (ok (map-insert cubes x (* x x x)))
                        (err u0)))

                (define-public (compute (x uint))
                    (if (is-eq u0 (mod x u3))
                        (let (
                            (y (get-square x))
                        )
                        (ok (map-insert quads x (* y y y y))))
                        (let (
                            (y (get-cube x))
                        )
                        (insert-cube y))))

                "#.to_string(),
                None
            ),
            (
                client_contract_id.clone(),
                r#"
                (define-map squares uint uint)
                (define-map quints uint uint)

                (define-read-only (get-square (x uint))
                    (default-to (contract-call? .library get-square x) (map-get? squares x)))

                (define-read-only (compute-quint (x uint))
                    (* (contract-call? .library get-cube x) (get-square x)))

                (define-public (insert-quint (x uint) (x_5 uint))
                    (if true
                        (ok (map-insert quints x x_5))
                        (err u0)))

                (define-public (compute (x uint))
                    (if (is-eq u0 (mod x u3))
                        (contract-call? .library compute x)
                        (insert-quint x (compute-quint x))))

                "#.to_string(),
                None
            )
        ],
        1
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(client_contract_id.clone(), "compute".try_into().unwrap());
    let map_mutations = symbex.callgraph().reachable_map_mutations_from(&fq_name).unwrap();

    let map_mutation_set : HashSet<_> = map_mutations.into_iter().collect();
    let expected_mutations : HashSet<_> = vec![
        FullName(client_contract_id.clone(), "quints".try_into().unwrap()),
        FullName(library_contract_id.clone(), "quads".try_into().unwrap()),
        FullName(library_contract_id.clone(), "cubes".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_mutation_set, expected_mutations);
    
    let fq_name = FullName(client_contract_id.clone(), "insert-quint".try_into().unwrap());
    let map_mutations = symbex.callgraph().reachable_map_mutations_from(&fq_name).unwrap();

    let map_mutation_set : HashSet<_> = map_mutations.into_iter().collect();
    let expected_mutations : HashSet<_> = vec![
        FullName(client_contract_id.clone(), "quints".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_mutation_set, expected_mutations);
}

#[test]
fn test_callgraph_reachability_map_writes() {
    let contract_id = default_contract_id();
    let symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map squares uint uint)
        (define-map cubes uint uint)
        (define-map quads uint uint)

        (define-private (set-square (x uint))
            (map-set squares x (* x x)))

        (define-private (insert-cube (x uint))
            (map-insert cubes x (* x x x)))

        (define-private (delete-square (x uint))
            (map-delete squares x))

        (define-private (compute (x uint))
            (if (is-eq u0 (mod x u3))
                (begin
                    (set-square x)
                    (map-insert quads x (* x x x x)))
                (begin
                    (delete-square x)
                    (insert-cube x))))

        (compute u21)
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(contract_id.clone(), "compute".try_into().unwrap());
    let map_mutations = symbex.callgraph().reachable_map_mutations_from(&fq_name).unwrap();

    let map_mutation_set : HashSet<_> = map_mutations.into_iter().collect();
    let expected_mutations : HashSet<_> = vec![
        FullName(contract_id.clone(), "squares".try_into().unwrap()),
        FullName(contract_id.clone(), "quads".try_into().unwrap()),
        FullName(contract_id.clone(), "cubes".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_mutation_set, expected_mutations);
    
    let fq_name = FullName(contract_id.clone(), "set-square".try_into().unwrap());
    let map_mutations = symbex.callgraph().reachable_map_mutations_from(&fq_name).unwrap();

    let map_mutation_set : HashSet<_> = map_mutations.into_iter().collect();
    let expected_mutations : HashSet<_> = vec![
        FullName(contract_id.clone(), "squares".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(map_mutation_set, expected_mutations);
}

// TODO: var-set reachability across contract-call

#[test]
fn test_callgraph_reachability_var_writes() {
    let contract_id = default_contract_id();
    let symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var square uint u0)
        (define-data-var cube uint u0)
        (define-data-var quad uint u0)

        (define-private (set-square (x uint))
            (var-set square (* x x)))

        (define-private (set-cube (x uint))
            (var-set cube (* x x x)))

        (define-private (compute (x uint))
            (if (is-eq u0 (mod x u3))
                (begin
                    (set-square x)
                    (var-set quad (* x x x x)))
                (begin
                    (var-set square u0)
                    (set-cube x))))

        (compute u21)
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(contract_id.clone(), "compute".try_into().unwrap());
    let var_mutations = symbex.callgraph().reachable_var_mutations_from(&fq_name).unwrap();
    
    let var_mutation_set : HashSet<_> = var_mutations.into_iter().collect();
    let expected_mutations : HashSet<_> = vec![
        FullName(contract_id.clone(), "square".try_into().unwrap()),
        FullName(contract_id.clone(), "quad".try_into().unwrap()),
        FullName(contract_id.clone(), "cube".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(var_mutation_set, expected_mutations);
    
    let fq_name = FullName(contract_id.clone(), "set-square".try_into().unwrap());
    let var_mutations = symbex.callgraph().reachable_var_mutations_from(&fq_name).unwrap();
    
    let var_mutation_set : HashSet<_> = var_mutations.into_iter().collect();
    let expected_mutations : HashSet<_> = vec![
        FullName(contract_id.clone(), "square".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(var_mutation_set, expected_mutations);
}

// TODO: var-get reachability across contract-call

#[test]
fn test_callgraph_reachability_var_reads() {
    let contract_id = default_contract_id();
    let symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-data-var square uint u0)
        (define-data-var cube uint u0)
        (define-data-var quad uint u0)

        (define-private (get-square (x uint))
            (var-get square))

        (define-private (get-cube (x uint))
            (var-get cube))

        (define-private (compute (x uint))
            (if (is-eq u0 (mod x u3))
                (let (
                    (y (get-square x))
                )
                (var-set quad (* x x x x)))
                (let (
                    (y (get-cube x))
                )
                (var-set square y))))

        (compute u21)
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let fq_name = FullName(contract_id.clone(), "compute".try_into().unwrap());
    let var_accesses = symbex.callgraph().reachable_var_accesses_from(&fq_name).unwrap();
    
    let var_access_set : HashSet<_> = var_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(contract_id.clone(), "square".try_into().unwrap()),
        FullName(contract_id.clone(), "cube".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(var_access_set, expected_accesses);
    
    let fq_name = FullName(contract_id.clone(), "get-square".try_into().unwrap());
    let var_accesses = symbex.callgraph().reachable_var_accesses_from(&fq_name).unwrap();
    
    let var_access_set : HashSet<_> = var_accesses.into_iter().collect();
    let expected_accesses : HashSet<_> = vec![
        FullName(contract_id.clone(), "square".try_into().unwrap()),
    ].into_iter().collect();

    assert_eq!(var_access_set, expected_accesses);
}

#[test]
fn test_halt_pox4_get_check_delegation() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        ;; Delegation relationships
        (define-map delegation-state
            { stacker: principal }
            {
                amount-ustx: uint,              ;; how many uSTX delegated?
                delegated-to: principal,        ;; who are we delegating?
                until-burn-ht: (optional uint), ;; how long does the delegation last?
                ;; does the delegate _need_ to use a specific
                ;; pox recipient address?
                pox-addr: (optional { version: (buff 1), hashbytes: (buff 32) })
            }
        )

        (define-read-only (get-check-delegation (stacker principal))
            (let ((delegation-info (try! (map-get? delegation-state { stacker: stacker }))))
                ;; did the existing delegation expire?
                (if (match (get until-burn-ht delegation-info)
                        until-burn-ht (> burn-block-height until-burn-ht)
                        false)
                    ;; it expired, return none
                    none
                    ;; delegation is active
                    (some delegation-info))))
        "#,
    )
    .unwrap();

    let termination_states = symbex.eval_user_function("get-check-delegation").unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(pand(vec![
                pgreater(vu("burn-block-height"), 
                   unwrap_panic(tget("until-burn-ht",
                        unwrap_panic(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))])))))),

                pi(is_some(tget("until-burn-ht",
                    unwrap_panic(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))])))))),

                pi(is_some(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))]))))]))
            .formula(none()),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    pi(is_none(tget("until-burn-ht",
                        unwrap_panic(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))])))))),

                    pi(is_some(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))]))))
                ]),
                pand(vec![
                    pleq(vu("burn-block-height"), 
                       unwrap_panic(tget("until-burn-ht",
                            unwrap_panic(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))])))))),

                    pi(is_some(tget("until-burn-ht",
                        unwrap_panic(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))])))))),

                    pi(is_some(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))]))))
                ])
            ]))
            .formula(some(unwrap_panic(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))]))))),

        Halt::new_test()
            .pred(pi(is_none(map_get("delegation-state", tcons(vec![("stacker", vp("stacker"))])))))
            .formula(none())
            .early_return()
    ]);
}

#[test]
fn test_halt_pox4_verify_signer_key_sig() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-constant ERR_NOT_ALLOWED 19)

        (define-constant ERR_INVALID_SIGNATURE_PUBKEY 35)
        (define-constant ERR_INVALID_SIGNATURE_RECOVER 36)

        (define-constant ERR_SIGNER_AUTH_AMOUNT_TOO_HIGH 38)
        (define-constant ERR_SIGNER_AUTH_USED 39)

        (define-constant SIP018_MSG_PREFIX 0x534950303138)

        ;; State for setting authorizations for signer keys to be used in
        ;; certain stacking transactions. These fields match the fields used
        ;; in the message hash for signature-based signer key authorizations.
        ;; Values in this map are set in `set-signer-key-authorization`.
        (define-map signer-key-authorizations
            {
                ;; The signer key being authorized
                signer-key: (buff 33),
                ;; The reward cycle for which the authorization is valid.
                ;; For `stack-stx` and `stack-extend`, this refers to the reward
                ;; cycle where the transaction is confirmed. For `stack-aggregation-commit`,
                ;; this refers to the reward cycle argument in that function.
                reward-cycle: uint,
                ;; For `stack-stx`, this refers to `lock-period`. For `stack-extend`,
                ;; this refers to `extend-count`. For `stack-aggregation-commit`, this is `u1`.
                period: uint,
                ;; A string representing the function where this authorization is valid. Either
                ;; `stack-stx`, `stack-extend`, `stack-increase` or `agg-commit`.
                topic: (string-ascii 14),
                ;; The PoX address that can be used with this signer key
                pox-addr: { version: (buff 1), hashbytes: (buff 32) },
                ;; The unique auth-id for this authorization
                auth-id: uint,
                ;; The maximum amount of uSTX that can be used (per tx) with this signer key
                max-amount: uint,
            }
            bool ;; Whether the authorization can be used or not
        )

        ;; State for tracking used signer key authorizations. This prevents re-use
        ;; of the same signature or pre-set authorization for multiple transactions.
        ;; Refer to the `signer-key-authorizations` map for the documentation on these fields
        (define-map used-signer-key-authorizations
            {
                signer-key: (buff 33),
                reward-cycle: uint,
                period: uint,
                topic: (string-ascii 14),
                pox-addr: { version: (buff 1), hashbytes: (buff 32) },
                auth-id: uint,
                max-amount: uint,
            }
            bool ;; Whether the field has been used or not
        )

        ;; Generate a message hash for validating a signer key.
        ;; The message hash follows SIP018 for signing structured data. The structured data
        ;; is the tuple `{ pox-addr: { version, hashbytes }, reward-cycle, auth-id, max-amount }`.
        ;; The domain is `{ name: "pox-4-signer", version: "1.0.0", chain-id: chain-id }`.
        (define-read-only (get-signer-key-message-hash (pox-addr { version: (buff 1), hashbytes: (buff 32) })
                                                       (reward-cycle uint)
                                                       (topic (string-ascii 14))
                                                       (period uint)
                                                       (max-amount uint)
                                                       (auth-id uint))
          (sha256 (concat
            SIP018_MSG_PREFIX
            (concat
              (sha256 (unwrap-panic (to-consensus-buff? { name: "pox-4-signer", version: "1.0.0", chain-id: chain-id })))
              (sha256 (unwrap-panic
                (to-consensus-buff? {
                  pox-addr: pox-addr,
                  reward-cycle: reward-cycle,
                  topic: topic,
                  period: period,
                  auth-id: auth-id,
                  max-amount: max-amount,
                })))))))


        (define-read-only (verify-signer-key-sig (pox-addr { version: (buff 1), hashbytes: (buff 32) })
                                                 (reward-cycle uint)
                                                 (topic (string-ascii 14))
                                                 (period uint)
                                                 (signer-sig-opt (optional (buff 65)))
                                                 (signer-key (buff 33))
                                                 (amount uint)
                                                 (max-amount uint)
                                                 (auth-id uint))
          (begin
            ;; Validate that amount is less than or equal to `max-amount`
            (asserts! (>= max-amount amount) (err ERR_SIGNER_AUTH_AMOUNT_TOO_HIGH))
            (asserts! (is-none (map-get? used-signer-key-authorizations { signer-key: signer-key, reward-cycle: reward-cycle, topic: topic, period: period, pox-addr: pox-addr, auth-id: auth-id, max-amount: max-amount }))
                      (err ERR_SIGNER_AUTH_USED))
            (match signer-sig-opt
              ;; `signer-sig` is present, verify the signature
              signer-sig (ok (asserts!
                (is-eq
                  (unwrap! (secp256k1-recover?
                    (get-signer-key-message-hash pox-addr reward-cycle topic period max-amount auth-id)
                    signer-sig) (err ERR_INVALID_SIGNATURE_RECOVER))
                  signer-key)
                (err ERR_INVALID_SIGNATURE_PUBKEY)))
              ;; `signer-sig` is not present, verify that an authorization was previously added for this key
              (ok (asserts! (default-to false (map-get? signer-key-authorizations
                    { signer-key: signer-key, reward-cycle: reward-cycle, period: period, topic: topic, pox-addr: pox-addr, auth-id: auth-id, max-amount: max-amount }))
                  (err ERR_NOT_ALLOWED)))
            ))
          )
        "#,
    )
    .unwrap();

    let termination_states = symbex.eval_user_function("verify-signer-key-sig").unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    let pox_addr_sym = vt("pox-addr", vec![("version", TS::SequenceType(SequenceSubtype::BufferType(1u32.try_into().unwrap()))), ("hashbytes", TS::SequenceType(SequenceSubtype::BufferType(32u32.try_into().unwrap())))]);
    let used_auth = map_get("used-signer-key-authorizations", tcons(vec![
        ("signer-key", vsb("signer-key", 33)),
        ("reward-cycle", vu("reward-cycle")),
        ("topic", vssa("topic", 14)),
        ("period", vu("period")),
        ("pox-addr", pox_addr_sym.clone()),
        ("auth-id", vu("auth-id")),
        ("max-amount", vu("max-amount"))
    ]));

    let signer_key_auth = map_get("signer-key-authorizations", tcons(vec![
        ("signer-key", vsb("signer-key", 33)),
        ("reward-cycle", vu("reward-cycle")),
        ("topic", vssa("topic", 14)),
        ("period", vu("period")),
        ("pox-addr", pox_addr_sym.clone()),
        ("auth-id", vu("auth-id")),
        ("max-amount", vu("max-amount"))
    ]));

    let signer_key_recover = secp256k1_recover(
        fcall(&format!("{contract_id}.get-signer-key-message-hash"), vec![pox_addr_sym.clone(), vu("reward-cycle"), vssa("topic", 14), vu("period"), vu("max-amount"), vu("auth-id")]),
        unwrap_panic(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap()))))
    );

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(plesser(vu("max-amount"), vu("amount")))
            .formula(cerr(vali(38)))
            .early_return(),

        Halt::new_test()
            .pred(pand(vec![
                pgeq(vu("max-amount"), vu("amount")),
                pis_some(used_auth.clone())
            ]))
            .formula(cerr(vali(39)))
            .early_return(),

        Halt::new_test()
            .pred(pand(vec![
                pgeq(vu("max-amount"), vu("amount")),
                pis_none(used_auth.clone()),
                pis_ok(signer_key_recover.clone()),
                pis_some(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap())))),
                pnot(peq(vsb("signer-key", 33), unwrap_panic(signer_key_recover.clone())))
            ]))
            .formula(cerr(vali(35)))
            .early_return(),

        Halt::new_test()
            .pred(pand(vec![
                pgeq(vu("max-amount"), vu("amount")),
                pis_some(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap())))),
                pis_none(used_auth.clone()),
                pis_err(signer_key_recover.clone()),
            ]))
            .formula(cerr(vali(36)))
            .early_return(),
       
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    pgeq(vu("max-amount"), vu("amount")),
                    pis_none(used_auth.clone()),
                    pis_none(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap())))),
                    pis_some(signer_key_auth.clone()),
                    pnot(pi(unwrap_panic(signer_key_auth.clone())))
                ]),
                pand(vec![
                    pgeq(vu("max-amount"), vu("amount")),
                    pis_none(used_auth.clone()),
                    pis_none(signer_key_auth.clone()),
                    pis_none(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap()))))
                ])
            ]))
            .formula(cerr(vali(19)))
            .early_return(),

        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    pgeq(vu("max-amount"), vu("amount")),
                    pis_none(used_auth.clone()),
                    pis_ok(signer_key_recover.clone()),
                    pis_some(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap())))),
                    peq(vsb("signer-key", 33), unwrap_panic(signer_key_recover.clone()))
                ]),
                pand(vec![
                    pgeq(vu("max-amount"), vu("amount")),
                    pis_none(used_auth.clone()),
                    pis_some(signer_key_auth.clone()),
                    pi(unwrap_panic(signer_key_auth.clone())),
                    pis_none(vo("signer-sig-opt", TS::SequenceType(SequenceSubtype::BufferType(65u32.try_into().unwrap()))))
                ])
            ]))
            .formula(cok(valb(true))),
    ]);
}

#[test]
fn test_continuation_combination() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map m uint uint)
        (define-data-var m-add uint u5)

        (define-private (inner-fold (idx uint) (acc (response uint uint)))
            (let (
                ;; short-circuit
                (mo (+ (try! acc) (var-get m-add)))
            )
            (asserts! (not (is-eq (mod idx mo) u0))
                (err u0))

            (asserts! (not (is-eq (mod idx mo) u1))
                (err u0))

            (asserts! (not (is-eq (mod idx mo) u2))
                (err u0))

            (if (map-insert m idx idx)
                (ok mo)
                (err u0))))

        (define-public (populate (modulus uint) (items (list 5 uint)))
            (begin
                (var-set m-add modulus)
                (try! (fold inner-fold items (ok modulus)))
                (ok (map-get? m modulus))))

        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let termination_states = symbex.eval_user_function("populate").unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    let map_is_none = |item| { pis_none(map_get("m", unwrap_panic(elat(vl("items", TS::UIntType, 5), cu(item))))) };
    let map_is_some = |item| { pis_some(map_get("m", unwrap_panic(elat(vl("items", TS::UIntType, 5), cu(item))))) };
    let item_at = |idx| { unwrap_panic(elat(vl("items", TS::UIntType, 5), cu(idx))) };

    let item_divisor = |idx| {
        if idx >= 1 {
            add2(mul2(cu(idx + 1), lv("m-add", vu("m-add"))), vu("modulus"))
        }
        else {
            add2(lv("m-add", vu("m-add")), vu("modulus"))
        }
    };

    let is_eq_mod = |idx, md| {
        if idx >= 1 {
            peq(rem(item_at(idx), item_divisor(idx)), cu(md))
        }
        else {
            peq(rem(item_at(idx), item_divisor(idx)), cu(md))
        }
    };

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(por(vec![
                pand(vec![
                    peqs(vec![llen(vl("items", TS::UIntType, 5)), rem(item_at(1), item_divisor(1)), cu(2)]),
                    map_is_none(0),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(1)),
                    is_eq_mod(0, 0)
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(1)),
                    is_eq_mod(0, 2)
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(1)),
                    map_is_some(0),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(2)),
                    is_eq_mod(1, 0),
                    map_is_none(0),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(2)),
                    is_eq_mod(1, 1),
                    map_is_none(0),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(2)),
                    map_is_none(0),
                    map_is_some(1),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(2)),
                    map_is_some(0),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(3)),
                    is_eq_mod(2, 0),
                    map_is_none(0),
                    map_is_none(1),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(3)),
                    is_eq_mod(2, 1),
                    map_is_none(0),
                    map_is_none(1),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(3)),
                    is_eq_mod(2, 2),
                    map_is_none(0),
                    map_is_none(1),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(3)),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_some(2),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(3)),
                    map_is_none(0),
                    map_is_some(1),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(4)),
                    is_eq_mod(3, 0),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(4)),
                    is_eq_mod(3, 1),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(4)),
                    is_eq_mod(3, 2),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(4)),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    map_is_some(3),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                    pnot(is_eq_mod(3, 0)),
                    pnot(is_eq_mod(3, 1)),
                    pnot(is_eq_mod(3, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(4)),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_some(2),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(5)),
                    is_eq_mod(4, 0),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    map_is_none(3),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                    pnot(is_eq_mod(3, 0)),
                    pnot(is_eq_mod(3, 1)),
                    pnot(is_eq_mod(3, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(5)),
                    is_eq_mod(4, 1),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    map_is_none(3),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                    pnot(is_eq_mod(3, 0)),
                    pnot(is_eq_mod(3, 1)),
                    pnot(is_eq_mod(3, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(5)),
                    is_eq_mod(4, 2),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    map_is_none(3),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                    pnot(is_eq_mod(3, 0)),
                    pnot(is_eq_mod(3, 1)),
                    pnot(is_eq_mod(3, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(5)),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    map_is_none(3),
                    map_is_some(4),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                    pnot(is_eq_mod(3, 0)),
                    pnot(is_eq_mod(3, 1)),
                    pnot(is_eq_mod(3, 2)),
                    pnot(is_eq_mod(4, 0)),
                    pnot(is_eq_mod(4, 1)),
                    pnot(is_eq_mod(4, 2)),
                ]),
                pand(vec![
                    peq(llen(vl("items", TS::UIntType, 5)), cu(5)),
                    map_is_none(0),
                    map_is_none(1),
                    map_is_none(2),
                    map_is_some(3),
                    pnot(is_eq_mod(0, 0)),
                    pnot(is_eq_mod(0, 1)),
                    pnot(is_eq_mod(0, 2)),
                    pnot(is_eq_mod(1, 0)),
                    pnot(is_eq_mod(1, 1)),
                    pnot(is_eq_mod(1, 2)),
                    pnot(is_eq_mod(2, 0)),
                    pnot(is_eq_mod(2, 1)),
                    pnot(is_eq_mod(2, 2)),
                    pnot(is_eq_mod(3, 0)),
                    pnot(is_eq_mod(3, 1)),
                    pnot(is_eq_mod(3, 2)),
                ]),
                peqs(vec![llen(vl("items", TS::UIntType, 5)), rem(unwrap_panic(elat(vl("items", TS::UIntType, 5), cu(0))), add2(lv("m-add", vu("m-add")), vu("modulus"))), cu(1)]),
            ]))
            .formula(cerr(valu(0)))
            .early_return()
            .reachable_map_write(contract_id.clone(), "m"),

        Halt::new_test()
            .pred(peq(llen(vl("items", TS::UIntType, 5)), cu(0)))
            .formula(ok(map_get("m", vu("modulus"))))
            .var(contract_id.clone(), "m-add", vu("modulus"))
            .reachable_map_write(contract_id.clone(), "m"),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(vl("items", TS::UIntType, 5)), cu(1)),
                map_is_none(0),
                pnot(is_eq_mod(0, 0)),
                pnot(is_eq_mod(0, 1)),
                pnot(is_eq_mod(0, 2)),
            ]))
            .formula(ok(map_get("m", vu("modulus"))))
            .var(contract_id.clone(), "m-add", vu("modulus"))
            .map(contract_id.clone(), "m", item_at(0), item_at(0))
            .reachable_map_write(contract_id.clone(), "m"),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(vl("items", TS::UIntType, 5)), cu(2)),
                map_is_none(0),
                map_is_none(1),
                pnot(is_eq_mod(0, 0)),
                pnot(is_eq_mod(0, 1)),
                pnot(is_eq_mod(0, 2)),
                pnot(is_eq_mod(1, 0)),
                pnot(is_eq_mod(1, 1)),
                pnot(is_eq_mod(1, 2)),
            ]))
            .formula(ok(map_get("m", vu("modulus"))))
            .var(contract_id.clone(), "m-add", vu("modulus"))
            .map(contract_id.clone(), "m", item_at(0), item_at(0))
            .map(contract_id.clone(), "m", item_at(1), item_at(1))
            .reachable_map_write(contract_id.clone(), "m"),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(vl("items", TS::UIntType, 5)), cu(3)),
                map_is_none(0),
                map_is_none(1),
                map_is_none(2),
                pnot(is_eq_mod(0, 0)),
                pnot(is_eq_mod(0, 1)),
                pnot(is_eq_mod(0, 2)),
                pnot(is_eq_mod(1, 0)),
                pnot(is_eq_mod(1, 1)),
                pnot(is_eq_mod(1, 2)),
                pnot(is_eq_mod(2, 0)),
                pnot(is_eq_mod(2, 1)),
                pnot(is_eq_mod(2, 2)),
            ]))
            .formula(ok(map_get("m", vu("modulus"))))
            .var(contract_id.clone(), "m-add", vu("modulus"))
            .map(contract_id.clone(), "m", item_at(0), item_at(0))
            .map(contract_id.clone(), "m", item_at(1), item_at(1))
            .map(contract_id.clone(), "m", item_at(2), item_at(2))
            .reachable_map_write(contract_id.clone(), "m"),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(vl("items", TS::UIntType, 5)), cu(4)),
                map_is_none(0),
                map_is_none(1),
                map_is_none(2),
                map_is_none(3),
                pnot(is_eq_mod(0, 0)),
                pnot(is_eq_mod(0, 1)),
                pnot(is_eq_mod(0, 2)),
                pnot(is_eq_mod(1, 0)),
                pnot(is_eq_mod(1, 1)),
                pnot(is_eq_mod(1, 2)),
                pnot(is_eq_mod(2, 0)),
                pnot(is_eq_mod(2, 1)),
                pnot(is_eq_mod(2, 2)),
                pnot(is_eq_mod(3, 0)),
                pnot(is_eq_mod(3, 1)),
                pnot(is_eq_mod(3, 2)),
            ]))
            .formula(ok(map_get("m", vu("modulus"))))
            .var(contract_id.clone(), "m-add", vu("modulus"))
            .map(contract_id.clone(), "m", item_at(0), item_at(0))
            .map(contract_id.clone(), "m", item_at(1), item_at(1))
            .map(contract_id.clone(), "m", item_at(2), item_at(2))
            .map(contract_id.clone(), "m", item_at(3), item_at(3))
            .reachable_map_write(contract_id.clone(), "m"),

        Halt::new_test()
            .pred(pand(vec![
                peq(llen(vl("items", TS::UIntType, 5)), cu(5)),
                map_is_none(0),
                map_is_none(1),
                map_is_none(2),
                map_is_none(3),
                map_is_none(4),
                pnot(is_eq_mod(0, 0)),
                pnot(is_eq_mod(0, 1)),
                pnot(is_eq_mod(0, 2)),
                pnot(is_eq_mod(1, 0)),
                pnot(is_eq_mod(1, 1)),
                pnot(is_eq_mod(1, 2)),
                pnot(is_eq_mod(2, 0)),
                pnot(is_eq_mod(2, 1)),
                pnot(is_eq_mod(2, 2)),
                pnot(is_eq_mod(3, 0)),
                pnot(is_eq_mod(3, 1)),
                pnot(is_eq_mod(3, 2)),
                pnot(is_eq_mod(4, 0)),
                pnot(is_eq_mod(4, 1)),
                pnot(is_eq_mod(4, 2)),
            ]))
            .formula(ok(map_get("m", vu("modulus"))))
            .var(contract_id.clone(), "m-add", vu("modulus"))
            .map(contract_id.clone(), "m", item_at(0), item_at(0))
            .map(contract_id.clone(), "m", item_at(1), item_at(1))
            .map(contract_id.clone(), "m", item_at(2), item_at(2))
            .map(contract_id.clone(), "m", item_at(3), item_at(3))
            .map(contract_id.clone(), "m", item_at(4), item_at(4))
            .reachable_map_write(contract_id.clone(), "m"),
    ]);
}

