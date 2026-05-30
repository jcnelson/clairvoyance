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

use stacks_common::consts::CHAIN_ID_MAINNET;
use stacks_common::types::StacksEpochId;
use stacks_common::address::C32_ADDRESS_VERSION_MAINNET_SINGLESIG;

use clarity::vm::EvalHook;
use clarity_types::Value;

use serde_json;

use crate::sym::{Sym, SymOp, Symbex, SymId, Predicate, VarOp, MapOp, Continuation};
use crate::core::Error;
use crate::core::DEFAULT_STACKS_EPOCH;

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

fn vi(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Int(name.into()))) }
fn vu(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::UInt(name.into()))) }
fn vb(name: &str) -> Box<SymOp> { Box::new(SymOp::Variable(Sym::Bool(name.into()))) }

fn add(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Add(ops)) }
fn sub(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Subtract(ops)) }
fn mul(ops: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::Multiply(ops)) }
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
fn bitand(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::BitwiseAnd(items)) }
fn bitor(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::BitwiseOr(items)) }
fn bitxor(items: Vec<Box<SymOp>>) -> Box<SymOp> { Box::new(SymOp::BitwiseXor(items)) }
fn var_get(s: Sym) -> Box<SymOp> { lv(s.clone().id(), Box::new(SymOp::Variable(s))) }
fn lv(n: &str, s: Box<SymOp>) -> Box<SymOp> { Box::new(SymOp::LoadedDataVariable(n.into(), s)) }

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
    maps: Vec<MapOp>,
    early_return: bool,
    panicking: bool
}

impl Halt {
    pub fn new() -> Self {
        Self {
            predicate: pf(),
            formula: cb(false),
            vars: vec![],
            maps: vec![],
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
}

fn assert_halts(mut conts: Vec<Continuation>, halts: Vec<Halt>) {
    let rolled_up_conts : Vec<_> = conts
        .into_iter()
        .map(|c| c.rollup())
        .collect();
    conts = rolled_up_conts;

    info!("Expected halting states:");
    for h in halts.iter() {
        info!("   Condition: {:?}", &h.predicate.clone().simplify().unwrap());
        info!("   Formula:   {:?}", &h.formula.clone().simplify().unwrap());
        for v in h.vars.iter() {
            info!("   Var:       {}", v.clone().simplify().unwrap());
        }
        for m in h.maps.iter() {
            info!("   Map:       {}", m);
        }
    }

    info!("Computed halting states:");
    for c in conts.iter() {
        info!("   Condition: {:?}", &c.predicate.clone().simplify().unwrap());
        info!("   Formula:   {:?}", &c.final_formula.clone().simplify().unwrap());
        for v in c.post_vars.iter() {
            info!("   Var:       {}", v.clone().simplify().unwrap());
        }
        for m in c.post_maps.iter() {
            info!("   Map:       {}", m.clone().simplify().unwrap());
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

                let mut post_maps = cont.post_maps.clone();
                for m in h.maps.iter() {
                    let mut found_map = None;
                    for (j, map) in post_maps.iter().enumerate() {
                        if map.clone().simplify().unwrap() == m.clone().simplify().unwrap() {
                            found_map = Some(j);
                            break;
                        }
                    }
                    let j = found_map.expect(&format!("Did not find expected map value {m:?} in continuation {cont:?}"));
                    post_maps.remove(j);
                }
                assert_eq!(post_maps.len(), 0, "continuation had unaccounted final map values {:?}", &post_maps);

                found_cont = Some(i);
                break;
            }
        }
        let i = found_cont.expect(&format!("halting condition {:?} state {:?} not found in continuations", h.predicate.clone().simplify().unwrap(), h.formula.clone().simplify().unwrap()));
        conts.remove(i);
    }

    if conts.len() > 0 {
        for c in conts {
            error!("Unaccounted continuation {:?} state {:?}", &c.predicate, &c.final_formula.clone().simplify().unwrap());
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
    
    // u1 - (u2 - u3) == Err:Arithmetic
    let symop = sub(vec![cu(1), sub(vec![cu(2), cu(3)])]);
    let simplified = symop.clone().simplify();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    let Err(Error::Arithmetic(_s)) = &simplified else { panic!("{:?}", simplified) };
    
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

    // (get x { x : y }) == Ok(x)
    let symop = tget("x", tcons(vec![("x", vu("y"))]));
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
    for t in termination_states.into_iter() {
        info!("termination state: ==================================\n{}\n", &t.rollup());
    }
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
    for t in termination_states.into_iter() {
        info!("termination state: ==================================\n{}\n", &t.rollup());
    }
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
    for t in termination_states.into_iter() {
        info!("termination state: ==================================\n{}\n", &t.rollup());
    }
}

#[test]
fn test_halt_simplify_var_get_const() {
    let symop = SymOp::LoadedDataVariable("foo".try_into().unwrap(), Box::new(SymOp::Constant(Value::UInt(3))));
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");

    let symop = SymOp::Modulo(Box::new(symop.clone()), Box::new(SymOp::Constant(Value::UInt(3))));
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
    
    let symop = SymOp::Equals(vec![Box::new(symop.clone()), Box::new(SymOp::Constant(Value::UInt(0)))]);
    let simplified = symop.clone().simplify().unwrap();
    info!("symop = {symop:?}, simplifed = {simplified:?}");
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
    for t in termination_states.into_iter() {
        info!("termination state: ==================================\n{}\n", &t.rollup());
    }
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
    for t in termination_states.into_iter() {
        info!("termination state: ==================================\n{}\n", &t.rollup());
    }
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
    for t in termination_states.into_iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.rollup());
    }
}
