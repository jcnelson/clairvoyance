use std::collections::HashMap;

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
use clarity_types::ClarityName;
use clarity_types::types::TupleData;
use clarity_types::types::signatures::{TypeSignature as TS, ListTypeData};
use clarity_types::types::SequenceSubtype;

use stacks_common::consts::CHAIN_ID_MAINNET;
use stacks_common::types::StacksEpochId;
use stacks_common::address::C32_ADDRESS_VERSION_MAINNET_SINGLESIG;

use clarity::vm::EvalHook;
use clarity_types::Value;

use serde_json;

use crate::sym::{Sym, SymOp, Symbex, SymId, Predicate, VarOp, MapOp, Continuation};
use crate::core::Error;
use crate::core::DEFAULT_STACKS_EPOCH;

fn f() -> Box<SymOp> { Box::new(SymOp::False()) }
fn t() -> Box<SymOp> { Box::new(SymOp::True()) }
fn valu(x: u128) -> Value { Value::UInt(x) }
fn vali(x: i128) -> Value { Value::Int(x) }
fn valb(x: bool) -> Value { Value::Bool(x) }
fn vall(x: Vec<Value>) -> Value { Value::cons_list(x, &DEFAULT_STACKS_EPOCH).unwrap() }

fn ci(x: i128) -> Box<SymOp> { Box::new(SymOp::Constant(Value::Int(x))) }
fn cu(x: u128) -> Box<SymOp> { Box::new(SymOp::Constant(Value::UInt(x))) }
fn cb(x: bool) -> Box<SymOp> { Box::new(SymOp::Constant(Value::Bool(x))) }
fn ct(fields: Vec<(&str, Value)>) -> Box<SymOp> {
    let consts : Vec<(ClarityName, Value)> = fields
        .into_iter()
        .map(|(name, v)| {
            (name.into(), v)
        })
        .collect();
            
    Box::new(SymOp::Constant(Value::Tuple(TupleData::from_data(consts).unwrap())))
}
fn cl(fields: Vec<Value>) -> Box<SymOp> { Box::new(SymOp::Constant(vall(fields))) }

fn si(name: &str) -> Sym { Sym::Int(name.into()) }
fn su(name: &str) -> Sym { Sym::UInt(name.into()) }
fn sb(name: &str) -> Sym { Sym::Bool(name.into()) }
fn sl(name: &str, ts: TS, len: u32) -> Sym { Sym::Sequence(name.into(), SequenceSubtype::ListType(ListTypeData::new_list(ts, len).unwrap())) }
fn so(name: &str, ts: TS) -> Sym { Sym::Optional(name.into(), ts) }
fn sr(name: &str, ok_ts: TS, err_ts: TS) -> Sym { Sym::Response(name.into(), ok_ts, err_ts) }

fn vi(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Int(name.into()))) }
fn vu(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::UInt(name.into()))) }
fn vb(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Bool(name.into()))) }

fn add(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Add(ops)) }
fn add2(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { add(vec![op1, op2]) }
fn sub(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Subtract(ops)) }
fn sub2(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { sub(vec![op1, op2]) }
fn mul(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Multiply(ops)) }
fn mul2(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { mul(vec![op1, op2]) }
fn div(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Divide(ops)) }
fn rem(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Modulo(op1, op2)) }
fn and(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::And(ops)) }
fn or(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Or(ops)) }
fn not(op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Not(op)) }
fn gt(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Greater(op1, op2)) }
fn geq(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Geq(op1, op2)) }
fn lt(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Less(op1, op2)) }
fn leq(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Leq(op1, op2)) }
fn eq(op1: Box<SymOp>, op2: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::Equals(vec![op1, op2])) }
fn eqs(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Equals(ops)) }
fn tcons(fields: Vec<(&str, Box<SymOp>)>) -> Box<SymOp> { Box::new(SymOp::TupleCons(fields.into_iter().map(|(name, op)| (name.into(), op)).collect())) }
fn tget(name: &str, op: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::TupleGet(name.into(), op)) }
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
fn lv(n: &str, s: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::LoadedDataVariable(n.into(), s)) }
fn lm(n: &str, key: Box<SymOp>, value: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::LoadedMapEntry(n.into(), key, Some(value))) }

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

pub struct Halt {
    predicate: Box<Predicate>,
    formula: Box<SymOp>,
    vars: Vec<VarOp>,
    map_state: HashMap<ClarityName, HashMap<SymOp, SymOp>>,
    early_return: bool,
    panicking: bool
}

impl Halt {
    pub fn new() -> Self {
        Self {
            predicate: pf(),
            formula: cb(false),
            vars: vec![],
            map_state: HashMap::new(),
            early_return: false,
            panicking: false
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

    pub fn var(mut self, var_name: &str, var_value: Box<SymOp>) -> Self {
        self.vars.push(VarOp::Set(var_name.into(), *var_value));
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

fn assert_halts(mut conts: Vec<Continuation>, halts: Vec<Halt>) {
    let rolled_up_conts : Vec<_> = conts
        .into_iter()
        .map(|c| c.rollup())
        .collect();
    conts = rolled_up_conts;

    info!("Expected halting states:");
    for h in halts.iter() {
        info!("   Condition: {}", &h.predicate.clone().simplify().unwrap());
        info!("   Formula:   {}", &h.formula.clone().simplify().unwrap());
        for v in h.vars.iter() {
            info!("   Var:       {}", v.clone().simplify().unwrap());
        }
        for (map_name, map) in h.map_state.iter() {
            info!("   Map {map_name}");
            for (key, value) in map.iter() {
                info!("      key:   {key}");
                info!("      value: {value}");
            }
        }
    }

    info!("Computed halting states:");
    for c in conts.iter() {
        info!("   Condition: {}", &c.predicate.clone().simplify().unwrap());
        info!("   Formula:   {}", &c.final_formula.clone().simplify().unwrap());
        for v in c.post_vars.iter() {
            info!("   Var:       {}", v.clone().simplify().unwrap());
        }
        for (map_name, map) in c.map_state.iter() {
            info!("   Map {map_name}");
            for (key, value) in map.iter() {
                let key = key.clone().simplify().unwrap();
                let value = value.clone().simplify().unwrap();
                info!("      key:   {key}");
                info!("      value: {value}");
            }
        }
    }

    // each continuation must have reached exactly one halt
    for h in halts.iter() {
        let mut found_cont = None;
        for (i, cont) in conts.iter().enumerate() {
            if cont.predicate.clone().simplify().unwrap() == *h.predicate && cont.final_formula.clone().simplify().unwrap() == *h.formula {

                // this halting state might match
                assert_eq!(cont.early_return, h.early_return);
                assert_eq!(cont.panicking, h.panicking);

                let mut post_vars = cont.post_vars.clone();
                for v in h.vars.iter() {
                    let mut found_var = None;
                    for (j, var) in post_vars.iter().enumerate() {
                        if var.clone().simplify().unwrap() == v.clone().simplify().unwrap() {
                            found_var = Some(j);
                            break;
                        }
                    }
                    let j = found_var.expect(&format!("Did not find expected variable {v:?} in continuation {cont:?}"));
                    post_vars.remove(j);
                }
                assert_eq!(post_vars.len(), 0, "continuation had unaccounted final variables {:?}", &post_vars);

                assert_eq!(cont.map_state, h.map_state);

                found_cont = Some(i);
                break;
            }
            else if cont.predicate.clone().simplify().unwrap() == *h.predicate {
                info!("Predicate {} matches, but not final formula:\n   Computed: {:?}\n      Given: {:?}\n", &h.predicate, cont.final_formula.clone().simplify().unwrap(), &h.formula);
            }
            else {
                info!("Final formula {} matches, but not predicate:\n   Computed: {:?}\n      Given: {:?}\n", &h.formula, cont.predicate.clone().simplify().unwrap(), &h.predicate);
            }
        }

        let i = found_cont.expect(&format!("halting condition {} state {} not found in continuations", h.predicate.clone().simplify().unwrap(), h.formula.clone().simplify().unwrap()));
        conts.remove(i);
    }

    if conts.len() > 0 {
        for c in conts {
            error!("Unaccounted continuation {} state {}", &c.predicate, &c.final_formula.clone().simplify().unwrap());
        }
        panic!();
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
    
    // (x - 1) * (x - 2) == (x*x + 2) - (x * 3)
    let symop = mul(vec![sub2(vu("x"), cu(1)), sub2(vu("x"), cu(2))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *sub2(add2(mul2(vu("x"), vu("x")), cu(2)), mul2(vu("x"), cu(3))));

    // (x - 1) * (x - 2) * (x - 3)
    // (x*x - 3*x + 2) * (x - 3)
    // (x*x*x - 3*x*x + 2*x - 3*x*x + 9*x - 6
    // (x*x*x + 11*x) - (6*x*x + 6)
    let symop = mul(vec![sub2(vu("x"), cu(1)), sub2(vu("x"), cu(2)), sub2(vu("x"), cu(3))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    info!("symop = {symop}, simplifed = {simplified}");
    assert_eq!(simplified, *sub2(add2(mul(vec![vu("x"), vu("x"), vu("x")]), mul2(vu("x"), cu(11))), add2(mul(vec![cu(6), vu("x"), vu("x")]), cu(6))));
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
    
    // (get x (loaded-var z (some { x : y }))) == Ok(y)
    let symop = tget("x", lv("z", some(tcons(vec![("x", vu("y"))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));
    
    // (get x (some (loaded-var z { x : y }))) == Ok(y)
    let symop = tget("x", some(lv("z", tcons(vec![("x", vu("y"))]))));
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));

    // (get x (map-get? m z { x : y })) == Ok(y)
    let symop = tget("x", lm("m", vu("z"), tcons(vec![("x", vu("y"))]))); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));
    
    // (get x (loaded-entry m z (some { x : y }))) == Ok(y)
    let symop = tget("x", lm("m", vu("z"), tcons(vec![("x", vu("y"))]))); 
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, Ok(*vu("y")));
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
        .bind_symbol("x".into(), *cu(3))
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
        .bind_symbol("x".into(), *add2(vu("y"), cu(3)))
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
        .bind_symbol("x".into(), *cu(1))
        .bind_symbol("y".into(), *cu(2))
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
        .bind_symbol("y".into(), *cu(5))
        .simplify()
        .unwrap();


    info!("symop = {symop:?}, simplifed = {simplified:?}");
    assert_eq!(simplified, *cu(11));
}


#[test]
fn test_halt_if_sym() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x bool true)
        (if (var-get x)
            u2
            u3)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    // two halting states
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(cu(2)),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cu(3)),
    ]);
}

#[test]
fn test_halt_as_max_len_sym_shrink() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (list 3 bool) (list true))
        ;; shrinking
        (as-max-len? (var-get x) u2)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    // two halting states -- one where the shrink works, and one where it doesn't
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pleq(llen(var_get(sl("x", TS::BoolType, 3))), cu(2)))
            .formula(some(var_get(sl("x", TS::BoolType, 3)))),
        
        // TODO: propagate new length
        Halt::new()
            .pred(pgreater(llen(var_get(sl("x", TS::BoolType, 3))), cu(2)))
            .formula(none())
    ]);
}

#[test]
fn test_halt_as_max_len_sym_grow() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (list 3 bool) (list true))
        ;; shrinking
        (as-max-len? (var-get x) u4)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    // one halting state, since the new length exceeds the type's max length
    assert_halts(termination_states, vec![
        // TODO: propagate new length
        Halt::new()
            .pred(pleq(llen(var_get(sl("x", TS::BoolType, 3))), cu(4)))
            .formula(some(var_get(sl("x", TS::BoolType, 3)))),
    ]);
}

#[test]
fn test_halt_tuple_cons() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x bool true)
        (define-data-var y uint u0)
        (define-data-var z (list 4 uint) (list ))

        { x: (var-get x), y: (if (var-get x) (var-get y) (+ u1 (var-get y))), z: (var-get z) }
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", var_get(su("y"))),
                ("z", var_get(sl("z", TS::UIntType, 4)))
            ])),

        Halt::new()
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
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x bool true)
        (get y (if (var-get x) { y: u1 } { y: u2 }))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(cu(1)),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_tuple_merge() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x bool true)
        (merge { x: (var-get x) } (if (var-get x) { y: u1 } { y: u2 }))
        "#,
        None
    ).unwrap();
    
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", cu(1))
            ])),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(tcons(vec![
                ("x", var_get(sb("x"))),
                ("y", cu(2))
            ]))
    ]);
}

#[test]
fn test_halt_begin() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pand(vec![
                pi(var_get(sb("x"))),
                pi(var_get(sb("y")))
            ]))
            .formula(cb(true))
            .var("x", lv("x", cb(false)))
            .var("y", lv("y", cb(false))),

        Halt::new()
            .pred(pand(vec![
                pnot(pi(var_get(sb("x")))),
                pi(var_get(sb("y")))
            ]))
            .formula(cb(true))
            .var("y", lv("y", cb(false))),

        Halt::new()
            .pred(pand(vec![
                pi(var_get(sb("x"))),
                pnot(pi(var_get(sb("y"))))
            ]))
            .formula(cb(true))
            .var("x", lv("x", cb(false))),

        Halt::new()
            .pred(pand(vec![
                pnot(pi(var_get(sb("x")))),
                pnot(pi(var_get(sb("y"))))
            ]))
            .formula(cb(true))
    ]);
}

#[test]
fn test_halt_default_to() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (optional bool) none)
        (default-to false (var-get x))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_some(var_get(so("x", TS::BoolType)))))
            .formula(unwrap_panic(var_get(so("x", TS::BoolType)))),

        Halt::new()
            .pred(pi(is_none(var_get(so("x", TS::BoolType)))))
            .formula(cb(false))
    ]);
}

#[test]
fn test_halt_asserts() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x bool true)
        (asserts! (var-get x) (err u0))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(cb(true)),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_opt() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (optional bool) (some true))
        (unwrap! (var-get x) (err u0))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_some(var_get(so("x", TS::BoolType)))))
            .formula(unwrap_panic(var_get(so("x", TS::BoolType)))),

        Halt::new()
            .pred(pi(is_none(var_get(so("x", TS::BoolType)))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_res() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (response bool uint) (ok true))
        (unwrap! (var-get x) (err u0))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_err() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (response bool uint) (err u1))
        (unwrap-err! (var-get x) (err u0))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_err_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(Box::new(err(cu(0)).simplify().unwrap()))
            .early_return()

    ]);
}

#[test]
fn test_halt_unwrap_panic_opt() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (optional bool) (some true))
        (unwrap-panic (var-get x))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_some(var_get(so("x", TS::BoolType)))))
            .formula(unwrap_panic(var_get(so("x", TS::BoolType)))),

        Halt::new()
            .pred(pi(is_none(var_get(so("x", TS::BoolType)))))
            .formula(panic())
            .early_return()
            .panic()

    ]);
}

#[test]
fn test_halt_unwrap_panic_res() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (response bool uint) (ok true))
        (unwrap-panic (var-get x))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(panic())
            .early_return()
            .panic()

    ]);
}

#[test]
fn test_halt_unwrap_err_panic() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (response bool uint) (err u0))
        (unwrap-err-panic (var-get x))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_err(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(unwrap_err_panic(var_get(sr("x", TS::BoolType, TS::UIntType)))),

        Halt::new()
            .pred(pi(is_ok(var_get(sr("x", TS::BoolType, TS::UIntType)))))
            .formula(panic())
            .early_return()
            .panic()

    ]);
}

#[test]
fn test_halt_match_opt() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (optional uint) (some u10))
        (match (var-get x)
            y (+ y u1)
            u2)
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_some(var_get(so("x", TS::UIntType)))))
            .formula(add2(cu(1), unwrap_panic(var_get(so("x", TS::UIntType))))),

        Halt::new()
            .pred(pi(is_none(var_get(so("x", TS::UIntType)))))
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_match_res() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (response uint uint) (ok u10))
        (match (var-get x)
            ok-y (+ ok-y u1)
            err-y (- err-y u1))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_ok(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(add2(cu(1), unwrap_panic(var_get(sr("x", TS::UIntType, TS::UIntType))))),

        Halt::new()
            .pred(pi(is_err(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(sub2(unwrap_err_panic(var_get(sr("x", TS::UIntType, TS::UIntType))), cu(1)))
    ]);
}

#[test]
fn test_halt_try_opt() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (optional uint) (some u10))
        (try! (var-get x))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_some(var_get(so("x", TS::UIntType)))))
            .formula(unwrap_panic(var_get(so("x", TS::UIntType)))),

        Halt::new()
            .pred(pi(is_none(var_get(so("x", TS::UIntType)))))
            .formula(none())
            .early_return()
    ]);
}

#[test]
fn test_halt_try_res() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x (response uint uint) (ok u10))
        (try! (var-get x))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(is_ok(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(unwrap_panic(var_get(sr("x", TS::UIntType, TS::UIntType)))),

        Halt::new()
            .pred(pi(is_err(var_get(sr("x", TS::UIntType, TS::UIntType)))))
            .formula(unwrap_err_panic(var_get(sr("x", TS::UIntType, TS::UIntType))))
            .early_return()
    ]);
}

#[test]
fn test_halt_symop_add() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(+ u1 (+ u2 u3 u4) u5)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(1 + 2 + 3 + 4 + 5))
    ]);
}

#[test]
fn test_halt_symop_if_constant() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(if true u2 u3)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(2)),
    ]);
}

#[test]
fn test_halt_symop_if_sym_constant() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(define-constant x true) (if x u2 u3)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    // unreachable continuation was eliminated
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_symop_if_sym_var() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(define-data-var x bool true) (if (var-get x) u2 u3)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(cu(2)),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cu(3))
    ]);
}

#[test]
fn test_halt_symop_var_set_if_sym_var() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(define-data-var x bool true) (define-data-var y uint u0) (if (var-get x) (var-set y u2) (var-set y u3))", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(cb(true))
            .var("y", lv("y", cu(2))),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cb(true))
            .var("y", lv("y", cu(3)))
    ]);
}

#[test]
fn test_halt_symop_multiple_var_set_if_sym_var() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("x"))))
            .formula(cb(true))
            .var("y", lv("y", cu(2)))
            .var("z", lv("z", cu(20))),

        Halt::new()
            .pred(pnot(pi(var_get(sb("x")))))
            .formula(cb(true))
            .var("y", lv("y", cu(3)))
            .var("z", lv("z", cu(30)))
    ]);
}

#[test]
fn test_halt_add_from_identical_ifs() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var a bool true)

        (+
            (if (var-get a) u0 u10)
            (if (var-get a) u1 u11)
            (if (var-get a) u2 u12)
            (if (var-get a) u3 u13))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("a"))))
            .formula(cu(0 + 1 + 2 + 3)),

        Halt::new()
            .pred(pnot(pi(var_get(sb("a")))))
            .formula(cu(10 + 11 + 12 + 13))
    ]);
}

#[test]
fn test_halt_add_from_unrelated_ifs() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cu(0 + 1 + 2 + 3)),

        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(0 + 1 + 2 + 13)),

        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cu(0 + 1 + 12 + 3)),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(0 + 1 + 12 + 13)),

        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cu(0 + 11 + 2 + 3)),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(0 + 11 + 2 + 13)),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cu(0 + 11 + 12 + 3)),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(0 + 11 + 12 + 13)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cu(10 + 1 + 2 + 3)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(10 + 1 + 2 + 13)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cu(10 + 1 + 12 + 3)),
         
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(10 + 1 + 12 + 13)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cu(10 + 11 + 2 + 3)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(10 + 11 + 2 + 13)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cu(10 + 11 + 12 + 3)),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cu(10 + 11 + 12 + 13))
    ])
}

#[test]
fn test_halt_list_cons_from_same_if() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var a bool true)

        (list
            (if (var-get a) u0 u10)
            (if (var-get a) u1 u11)
            (if (var-get a) u2 u12)
            (if (var-get a) u3 u13))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pi(var_get(sb("a"))))
            .formula(cl(vec![valu(0), valu(1), valu(2), valu(3)])),
        
        Halt::new()
            .pred(pnot(pi(var_get(sb("a")))))
            .formula(cl(vec![valu(10), valu(11), valu(12), valu(13)]))
    ]);
}

#[test]
fn test_halt_list_cons_from_unrelated_ifs() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(1), valu(2), valu(3)])),

        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(1), valu(2), valu(13)])),

        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(1), valu(12), valu(3)])),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(1), valu(12), valu(13)])),

        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(11), valu(2), valu(3)])),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(11), valu(2), valu(13)])),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(0), valu(11), valu(12), valu(3)])),
        
        Halt::new()
            .pred(pand(vec![pi(var_get(sb("a"))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(0), valu(11), valu(12), valu(13)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(1), valu(2), valu(3)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(1), valu(2), valu(13)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(1), valu(12), valu(3)])),
         
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pi(var_get(sb("b"))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(1), valu(12), valu(13)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(11), valu(2), valu(3)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pi(var_get(sb("c"))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(11), valu(2), valu(13)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pi(var_get(sb("d")))]))
            .formula(cl(vec![valu(10), valu(11), valu(12), valu(3)])),
        
        Halt::new()
            .pred(pand(vec![pnot(pi(var_get(sb("a")))), pnot(pi(var_get(sb("b")))), pnot(pi(var_get(sb("c")))), pnot(pi(var_get(sb("d"))))]))
            .formula(cl(vec![valu(10), valu(11), valu(12), valu(13)]))
    ])
}

#[test]
fn test_halt_function_call() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-private (foo (x uint))
            (+ u1 x))

        (foo u0)
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(1))
    ]);
}

#[test]
fn test_halt_mod() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(mod u2 u3)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(2 % 3))
    ]);
}

#[test]
fn test_halt_is_eq() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(is-eq u2 u3 u4)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cb(false))
    ]);
}

#[test]
fn test_halt_if_is_eq() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, "(if (is-eq u2 u3 u4) u1 u2)", None).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(2))
    ]);
}

#[test]
fn test_halt_function_call_if_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-private (foo (x uint))
            (if (is-eq (mod x u2) u0)
                (+ u1 x)
                (+ u3 x)))

        (foo u0)
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cu(1))
    ]);
}

#[test]
fn test_halt_function_call_if_branch_pre_post_vars() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)
        (define-private (foo (x uint))
            (if (is-eq (mod x u2) u0)
                (var-set v (+ u1 x))
                (var-set v (+ u3 x))))

        (foo (var-get v))
        "#,
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(cb(true))
            .var("v", add(vec![cu(1), var_get(su("v"))])),

        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cb(true))
            .var("v", add(vec![cu(3), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_var_get_set_tower() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(add(vec![cu(6), var_get(su("w"))]))
            .var("w", add(vec![cu(5), var_get(su("w"))]))
            .var("v", add(vec![cu(6), var_get(su("w"))]))
    ]);
}

#[test]
fn test_halt_var_get_set_if_tree() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peqs(vec![
                rem(var_get(su("v")), cu(2)),
                rem(var_get(su("w")), cu(2)),
                cu(0)
            ]))
            .formula(cl(vec![valu(101), valu(101)]))
            .var("v", cu(101))
            .var("w", cu(101)),

        Halt::new()
            .pred(pand(vec![peq(rem(var_get(su("v")), cu(2)), cu(0)), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(cl(vec![valu(201), valu(200)]))
            .var("v", cu(201))
            .var("w", cu(200)),

        Halt::new()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), peq(rem(var_get(su("w")), cu(2)), cu(0))]))
            .formula(cl(vec![valu(300), valu(301)]))
            .var("v", cu(300))
            .var("w", cu(301)),
            
        Halt::new()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(cl(vec![valu(400), valu(400)]))
            .var("v", cu(400))
            .var("w", cu(400))
    ]);
}

#[test]
fn test_halt_var_get_set_tower_if_tree() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peqs(vec![
                rem(var_get(su("v")), cu(2)),
                rem(var_get(su("w")), cu(2)),
                cu(0)
            ]))
            .formula(add(vec![cu(6), var_get(su("w"))]))
            .var("v", add(vec![cu(6), var_get(su("w"))]))
            .var("w", add(vec![cu(5), var_get(su("w"))])),

        Halt::new()
            .pred(pand(vec![peq(rem(var_get(su("v")), cu(2)), cu(0)), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(add(vec![cu(24), var_get(su("w"))]))
            .var("v", add(vec![cu(24), var_get(su("w"))]))
            .var("w", add(vec![cu(23), var_get(su("w"))])),

        Halt::new()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), peq(rem(var_get(su("w")), cu(2)), cu(0))]))
            .formula(add(vec![cu(42), var_get(su("w"))]))
            .var("v", add(vec![cu(42), var_get(su("w"))]))
            .var("w", add(vec![cu(32), var_get(su("w"))])),

        Halt::new()
            .pred(pand(vec![pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))), pnot(peq(rem(var_get(su("w")), cu(2)), cu(0)))]))
            .formula(add(vec![cu(60), var_get(su("w"))]))
            .var("v", add(vec![cu(60), var_get(su("w"))]))
            .var("w", add(vec![cu(50), var_get(su("w"))]))
    ]);
}

#[test]
fn test_halt_var_get_set_if_sequence() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peqs(vec![
                rem(var_get(su("v")), cu(2)),
                rem(var_get(su("v")), cu(3)),
                rem(var_get(su("v")), cu(5)),
                cu(0)
            ]))
            .formula(lcons(vec![var_get(su("v")), cu(40)]))
            .var("w", cu(40)),

        Halt::new()
            .pred(pand(vec![
                peqs(vec![
                    rem(var_get(su("v")), cu(2)),
                    rem(var_get(su("v")), cu(3)),
                    cu(0)
                ]),
                pnot(peq(rem(var_get(su("v")), cu(5)), cu(0)))
            ]))
            .formula(cl(vec![valu(6), valu(30)]))
            .var("v", cu(6))
            .var("w", cu(30)),

        Halt::new()
            .pred(pand(vec![
                peq(rem(var_get(su("v")), cu(2)), cu(0)),
                pnot(peq(rem(var_get(su("v")), cu(3)), cu(0))),
            ]))
            .formula(cl(vec![valu(5), valu(40)]))
            .var("v", cu(5))
            .var("w", cu(40)),

        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cl(vec![valu(5), valu(40)]))
            .var("v", cu(5))
            .var("w", cu(40)),
    ])
}

#[test]
fn test_halt_simplify_var_get_const() {
    let symop = SymOp::LoadedDataVariable("foo".try_into().unwrap(), Box::new(SymOp::Constant(Value::UInt(3))));
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
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (let (
            (a (var-get v))
            (b (+ u1 a))
            (c (+ u2 b))
        )
        (var-set v c))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(cb(true))
            .var("v", add(vec![cu(3), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_if_let_bind() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (let (
            (a (var-get v))
            (b (if (is-eq (mod a u2) u0) (+ u1 a) (+ u2 a)))
        )
        (var-set v b))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(cb(true))
            .var("v", add(vec![cu(1), var_get(su("v"))])),
        
        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cb(true))
            .var("v", add(vec![cu(2), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_if_let_var_set_bind() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (let (
            (a (var-get v))
            (b (if (is-eq (mod a u2) u0) false (var-set v (+ u2 a))))
            (c (if b (var-get v) u10))
        )
        (var-set v c))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(cb(true))
            .var("v", cu(10)),

        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cb(true))
            .var("v", add(vec![cu(2), var_get(su("v"))]))
    ]);
}

#[test]
fn test_halt_map_user_func() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (x uint))
           (+ (var-get v) x))

        (map fetch-add (list u0 u1 u2 u3))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(lcons(vec![var_get(su("v")), add2(cu(1), var_get(su("v"))), add2(cu(2), var_get(su("v"))), add2(cu(3), var_get(su("v")))]))
    ]);
}

#[test]
fn test_halt_map_user_func_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (define-private (fetch-add-sub (x uint))
           (if (is-eq (mod (var-get v) u2) u0)
              (+ (var-get v) x)
              (- (var-get v) x)))

        (map fetch-add-sub (list u0 u1 u2 u3))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(lcons(vec![var_get(su("v")), add2(cu(1), var_get(su("v"))), add2(cu(2), var_get(su("v"))), add2(cu(3), var_get(su("v")))])),
        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(lcons(vec![var_get(su("v")), sub2(var_get(su("v")), cu(1)), sub2(var_get(su("v")), cu(2)), sub2(var_get(su("v")), cu(3))]))
    ])
}

#[test]
fn test_halt_map_sequence_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (x uint))
           (+ (var-get v) x))

        (map fetch-add (if (is-eq (mod (var-get v) u2) u0) (list u0 u1 u2 u3) (list u10 u11 u12 u13)))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(lcons(vec![var_get(su("v")), add2(cu(1), var_get(su("v"))), add2(cu(2), var_get(su("v"))), add2(cu(3), var_get(su("v")))])),
        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(lcons(vec![add2(cu(10), var_get(su("v"))), add2(cu(11), var_get(su("v"))), add2(cu(12), var_get(su("v"))), add2(cu(13), var_get(su("v")))]))
    ])
}

#[test]
fn test_halt_map_symbolic_list() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)
        (define-data-var list-v (list 4 uint) (list u0 u1 u2 u3))

        (define-private (fetch-add (x uint))
           (+ (var-get v) x))

        (map fetch-add (var-get list-v))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(cu(0), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(cl(vec![])),

        Halt::new()
            .pred(peq(cu(1), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0))))
            ])),

        Halt::new()
            .pred(peq(cu(2), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(1))))
            ])),
        
        Halt::new()
            .pred(peq(cu(3), llen(var_get(sl("list-v", TS::UIntType, 4)))))
            .formula(lcons(vec![
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(0)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(1)))),
                add2(var_get(su("v")), unwrap_panic(elat(var_get(sl("list-v", TS::UIntType, 4)), cu(2))))
            ])),
        
        Halt::new()
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
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)
        (define-data-var list-v1 (list 4 uint) (list u0 u1 u10 u11))
        (define-data-var list-v2 (list 4 uint) (list u2 u3 u12 u13))
        (define-data-var list-v3 (list 4 uint) (list u4 u5 u14 u15))

        (define-private (fetch-add (x uint) (y uint) (z uint))
           (+ (var-get v) x y z))

        (map fetch-add (var-get list-v1) (var-get list-v2) (var-get list-v3))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
    
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(por(vec![
                peq(cu(0), llen(var_get(sl("list-v1", TS::UIntType, 4)))),
                peq(cu(0), llen(var_get(sl("list-v2", TS::UIntType, 4)))),
                peq(cu(0), llen(var_get(sl("list-v3", TS::UIntType, 4))))
            ]))
            .formula(cl(vec![])),

        Halt::new()
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
        
        Halt::new()
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
        
        Halt::new()
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
        
        Halt::new()
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
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (idx uint) (value uint))
           (+ (var-get v) idx value))

        (fold fetch-add (list u0 u1 u2 u3) u10)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(pt())
            .formula(add(vec![
                mul2(cu(4), var_get(su("v"))),
                cu(16)
            ]))
        
    ]);
}

#[test]
fn test_halt_fold_user_func_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(add(vec![
                mul2(cu(4), var_get(su("v"))),
                cu(16)
            ])),

        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(cu(8))
    ]);
}

#[test]
fn test_halt_fold_sequence_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (define-private (fetch-add (x uint) (value uint))
           (+ (var-get v) x value))

        (fold fetch-add (if (is-eq (mod (var-get v) u2) u0) (list u0 u1 u2 u3) (list u10 u11 u12 u13)) u10)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(rem(var_get(su("v")), cu(2)), cu(0)))
            .formula(add2(mul2(var_get(su("v")), cu(4)), cu(16))),

        Halt::new()
            .pred(pnot(peq(rem(var_get(su("v")), cu(2)), cu(0))))
            .formula(add2(mul2(var_get(su("v")), cu(4)), cu(56))),
    ]);
}

#[test]
fn test_halt_fold_symbolic_lists() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)
        (define-data-var list-v1 (list 4 uint) (list u0 u1 u10 u11))

        (define-private (fetch-add (x uint) (value uint))
           (+ (var-get v) x value))

        (fold fetch-add (var-get list-v1) u10)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
   
    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(0)))
            .formula(cu(10)),

        Halt::new()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(1)))
            .formula(add(vec![
                var_get(su("v")),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                cu(10)
            ])),

        Halt::new()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(2)))
            .formula(add(vec![
                mul2(cu(2), var_get(su("v"))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                cu(10)
            ])),

        Halt::new()
            .pred(peq(llen(var_get(sl("list-v1", TS::UIntType, 4))), cu(3)))
            .formula(add(vec![
                mul2(cu(3), var_get(su("v"))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(0))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(1))),
                unwrap_panic(elat(var_get(sl("list-v1", TS::UIntType, 4)), cu(2))),
                cu(10)
            ])),

        Halt::new()
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
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u1)

        (define-private (parity (x uint))
            (is-eq (mod x u2) (var-get v)))

        (filter parity (list u0 u1 u2 u3))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(var_get(su("v")), cu(0)))
            .formula(cl(vec![valu(0), valu(2)])),

        Halt::new()
            .pred(peq(var_get(su("v")), cu(1)))
            .formula(cl(vec![valu(1), valu(3)])),

        Halt::new()
            .pred(pand(vec![pnot(peq(var_get(su("v")), cu(0))), pnot(peq(var_get(su("v")), cu(1)))]))
            .formula(cl(vec![]))
    ]);
}

#[test]
fn test_halt_filter_user_func_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u0)

        (define-private (parity-is-three (x uint))
           (if (is-eq (mod x u2) u0)
              (is-eq (var-get v) u3)
              (is-eq x u3)))

        (filter parity-is-three (list u0 u1 u2 u3))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(var_get(su("v")), cu(3)))
            .formula(cl(vec![valu(0), valu(2), valu(3)])),

        Halt::new()
            .pred(pnot(peq(var_get(su("v")), cu(3))))
            .formula(cl(vec![valu(3)]))
    ]);
}

#[test]
fn test_halt_filter_sequence_branch() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u1)

        (define-private (parity (x uint))
            (is-eq (mod x u2) (var-get v)))

        (filter parity (if (is-eq (var-get v) u1) (list u0 u1 u2 u3) (list u5 u10 u15 u20)))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new()
            .pred(peq(var_get(su("v")), cu(1)))
            .formula(cl(vec![valu(1), valu(3)])),

        Halt::new()
            .pred(peq(var_get(su("v")), cu(0)))
            .formula(cl(vec![valu(10), valu(20)])),

        Halt::new()
            .pred(pand(vec![pnot(peq(var_get(su("v")), cu(0))), pnot(peq(var_get(su("v")), cu(1)))]))
            .formula(cl(vec![]))
    ]);
}

#[test]
fn test_halt_filter_symbolic_lists() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var v uint u1)
        (define-data-var l (list 3 uint) (list u0 u1 u2))

        (define-private (parity (x uint))
            (is-eq (mod x u2) (var-get v)))

        (filter parity (var-get l))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        // length 0 -- 1 possibility
        Halt::new()
            .pred(peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(0)))
            .formula(cl(vec![])),

        // length 1 -- 2 possibilities
        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(1)),
                peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))
            ]))
            .formula(lcons(vec![unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0)))])),
        
        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(1)),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2))))
            ]))
            .formula(cl(vec![])),
           
        // length 2 -- 4 possibilities
        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)),
                ])
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1)))
            ])),

        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
            ])),

        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))),
            ])),

        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(2)),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
            ]))
            .formula(cl(vec![])),

        // length 3 -- 8 possibilities
        Halt::new()
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

        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)),
                ]),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))),
            ])),
        
        Halt::new()
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
        
        Halt::new()
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
        
        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2))
                ]),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))),
            ])),

        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                peqs(vec![
                    var_get(su("v")),
                    rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2))
                ]),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
            ]))
            .formula(lcons(vec![
                unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))),
            ])),

        Halt::new()
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

        Halt::new()
            .pred(pand(vec![
                peq(llen(var_get(sl("l", TS::UIntType, 3))), cu(3)),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(0))), cu(2)))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(1))), cu(2)))),
                pnot(peq(var_get(su("v")), rem(unwrap_panic(elat(var_get(sl("l", TS::UIntType, 3)), cu(2))), cu(2)))),
            ]))
            .formula(cl(vec![])),
    ]);
}

#[test]
fn test_halt_map_get() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-map squares uint uint)

        (define-private (add-or-square (x uint))
            (match (map-get? squares x)
                y (* y y)
                (+ x x)))

        (add-or-square u3)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

}

#[test]
fn test_halt_map_set() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-map squares uint uint)

        (define-private (add-and-square (x uint))
            (match (map-get? squares x)
                y (map-set squares y (* y y))
                (map-set squares x (+ x x))))

        (add-and-square u3)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_multiple_map_set() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-map squares uint uint)

        (begin
            (map-set squares u1 u1)
            (map-set squares u1 u2)
            (map-set squares u1 u3))

        (map-get? squares u1)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_multiple_sym_map_set() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-data-var x uint u1)
        (define-map squares uint uint)

        (begin
            (map-set squares (var-get x) (var-get x))
            (map-set squares (var-get x) (+ u1 (var-get x)))
            (map-set squares (var-get x) (+ u2 (var-get x))))

        (map-get? squares (var-get x))
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_multiple_map_get_none() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-map squares uint uint)

        (begin
            (map-set squares u1 u1)
            (map-set squares u1 u2)
            (map-set squares u1 u3))

        (map-get? squares u2)
        "#,
        None
    ).unwrap();
    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_limit_function_exploration() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-map squares uint uint)

        (define-private (ignored-function (x uint) (y uint))
            (map-set squares x (* y y)))

        (define-private (store-squares (x uint) (y uint))
            (begin
                (ignored-function x y)
                (ignored-function y x)))

        (store-squares u2 u3)
        "#,
        None
    )
    .unwrap()
    .with_skipped_function_call("ignored-function".into());

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_eager_function_evaluation() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
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
        None
    )
    .unwrap()
    .with_eager_function_eval("evaled-function".into());

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_halt_rollup_early_return() {
    let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::new(C32_ADDRESS_VERSION_MAINNET_SINGLESIG, [0x11; 20]).unwrap(), "contract".into());
    let mut symbex = Symbex::from_contract(contract_id, r#"
        (define-public (early-return-if-mod-6 (x uint))
            (begin
                (asserts! (is-eq (mod x u3) u0) (err u1))
                (asserts! (is-eq (mod x u2) u0) (err u2))
                (ok (* x x x))))

        (define-data-var input uint u12)
        (early-return-if-mod-6 (var-get input))
        "#,
        None
    )
    .unwrap()
    .with_eager_function_eval("early-return-if-mod-6".into());

    let termination_states = symbex.eval_all().unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}
        
                
