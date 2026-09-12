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

use std::collections::VecDeque;
use std::collections::HashMap;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::fmt;

use clarity_types::Value;
use clarity_types::ClarityName;
use clarity_types::representations::{SymbolicExpression, SymbolicExpressionType};
use clarity_types::types::TupleData;
use clarity_types::types::{SequenceData, CharType};
use clarity_types::types::QualifiedContractIdentifier;
use clarity_types::types::StandardPrincipalData;
use clarity_types::types::PrincipalData;
use clarity_types::types::TraitIdentifier;

use clarity::vm::ContractContext;
use clarity::vm::contexts::GlobalContext;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::eval_all;
use clarity::vm::types::TypeSignature;
use clarity::vm::types::TypeSignatureExt;

use crate::core::Error;
use crate::core::BackingStore;
use crate::core::ast;
use crate::sym::Symbex;
use crate::sym::SymOp;
use crate::sym::Sym;
use crate::sym::Predicate;
use crate::sym::FullName;
use crate::sym::Continuation;
use crate::sym::GetContractSymOps;

use crate::core::{DEFAULT_STACKS_EPOCH, DEFAULT_CLARITY_VERSION, ProofFailures};

use stacks_common::consts::CHAIN_ID_MAINNET;
use stacks_common::address::C32_ADDRESS_VERSION_MAINNET_SINGLESIG;

const COMMANDS_INTERPRETER: &'static str = include_str!("./command.clar");

/// Description of a halting state for a function
#[derive(Debug, Clone, PartialEq)]
pub struct Halt {
    /// The function's return value
    pub formula: Box<SymOp>,
    /// The logical expression which must be true for this halting state to be reached
    pub predicate: Box<Predicate>,
    /// The halting condition which, if given, must be implied by the predicate.
    /// If this is Some(cond), then the halting state will be treated as reachable by continuation C
    /// if C.predicate --> cond (i.e. (or (not C.predicate) cond) evaluates to true).  Otherwise,
    /// C.predicate will be checked directly against self.predicate.
    pub condition: Option<Box<Predicate>>,
    /// Variables written
    pub vars: HashMap<FullName, SymOp>,
    /// Map items written
    pub map_state: HashMap<FullName, HashMap<SymOp, SymOp>>,
    /// Map items deleted
    pub map_tombstones: HashMap<FullName, HashSet<SymOp>>,
    /// Possibly-accessable variables
    pub reachable_var_reads: HashSet<FullName>,
    /// Possibly-writable variables
    pub reachable_var_writes: HashSet<FullName>,
    /// Possibly-accessable maps
    pub reachable_map_reads: HashSet<FullName>,
    /// Possibly-writable maps
    pub reachable_map_writes: HashSet<FullName>,
    /// Whether or not this halting state is an early-return
    pub early_return: bool,
    /// Whether or not this halting state is a panic
    pub panicking: bool,
    /// Whether or not to analyze possibly-reachable writes
    pub analyze_write_reachability: bool,
}

impl Halt {
    pub fn new(formula: SymOp, predicate: Predicate) -> Self {
        Self {
            formula: Box::new(formula),
            predicate: Box::new(predicate),
            condition: None,
            vars: HashMap::new(),
            map_state: HashMap::new(),
            map_tombstones: HashMap::new(),
            reachable_var_reads: HashSet::new(),
            reachable_var_writes: HashSet::new(),
            reachable_map_reads: HashSet::new(),
            reachable_map_writes: HashSet::new(),
            early_return: false,
            panicking: false,
            analyze_write_reachability: false,
        }
    }

    pub fn from_symbolic_expressions(ctx: &CommandContext, exprs: &[SymbolicExpression]) -> Result<Self, Error> {
        let mut formula = None;
        let mut condition = None;
        let mut predicate = None;
        let mut vars = HashMap::new();
        let mut map_state : HashMap<FullName, HashMap<SymOp, SymOp>> = HashMap::new();
        let mut map_tombstones : HashMap<FullName, HashSet<SymOp>> = HashMap::new();
        let mut reachable_var_reads = HashSet::new();
        let mut reachable_var_writes = HashSet::new();
        let mut reachable_map_reads = HashSet::new();
        let mut reachable_map_writes = HashSet::new();
        let mut panicking = false;
        let mut early_return = false;
        let mut analyze_write_reachability = false;

        for (i, expr) in exprs.iter().enumerate() {
            let Some(lv) = expr.match_list() else {
                return Err(Error::new_program_error(format!("Expression #{i} in `halt` is not a list: {expr}")));
            };
            let Some(directive) = lv[0].match_atom() else {
                return Err(Error::new_program_error(format!("List expression #{i} in `halt` does not start with an atom: {expr}")));
            };
            match directive.as_str() {
                "result" => {
                    if formula.is_some() {
                        return Err(Error::new_program_error(format!("List expression #{i} is a duplicate directive `{directive}`: {expr}")));
                    }
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let symop = ctx.parse_symop(&lv[1])?;
                    formula = Some(Box::new(symop));
                }
                "condition" => {
                    if predicate.is_some() || condition.is_some() {
                        return Err(Error::new_program_error(format!("List expression #{i} is a duplicate directive `{directive}`, or `predicate` is already defined: {expr}")));
                    }
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let inv = ctx.parse_symop(&lv[1])?.try_as_predicate()?;
                    condition = Some(Box::new(inv));
                }
                "predicate" => {
                    if predicate.is_some() || condition.is_some() {
                        return Err(Error::new_program_error(format!("List expression #{i} is a duplicate directive `{directive}`, or `condition` is already defined: {expr}")));
                    }
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let inv = ctx.parse_symop(&lv[1])?.try_as_predicate()?;
                    predicate = Some(Box::new(inv));
                }
                "var-write" => {
                    if lv.len() != 3 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 2 arguments: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    let value = ctx.parse_symop(&lv[2])?;
                    vars.insert(name, value);
                }
                "map-write" => {
                    if lv.len() != 4 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 3 arguments: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    let key = ctx.parse_symop(&lv[2])?;
                    let value = ctx.parse_symop(&lv[3])?;

                    if let Some(state) = map_state.get_mut(&name) {
                        state.insert(key, value);
                    }
                    else {
                        let mut state = HashMap::new();
                        state.insert(key, value);
                        map_state.insert(name, state);
                    }
                }
                "map-delete" => {
                    if lv.len() != 3 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 2 arguments: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    let key = ctx.parse_symop(&lv[2])?;

                    if let Some(keys) = map_tombstones.get_mut(&name) {
                        keys.insert(key);
                    }
                    else {
                        let mut keys = HashSet::new();
                        keys.insert(key);
                        map_tombstones.insert(name.clone(), keys);
                    }
                }
                "reachable-var-read" => {
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    reachable_var_reads.insert(name);
                }
                "reachable-var-write" => {
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    reachable_var_writes.insert(name);
                }
                "reachable-map-read" => {
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    reachable_map_reads.insert(name);
                }
                "reachable-map-write" => {
                    if lv.len() != 2 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 1 argument: {expr}")));
                    }
                    let name = SymOp::match_fullname(&lv[1])?;
                    reachable_map_writes.insert(name);
                }
                "panicking" => {
                    if lv.len() != 1 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 0 arguments: {expr}")));
                    }
                    panicking = true;
                }
                "early-return" => {
                    if lv.len() != 1 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 0 arguments: {expr}")));
                    }
                    early_return = true;
                }
                "analyze-write-reachability" => {
                    if lv.len() != 1 {
                        return Err(Error::new_program_error(format!("List expression #{i} (directive `{directive}`) expects 0 arguments: {expr}")));
                    }
                    analyze_write_reachability = true;
                }
                _ => {
                    return Err(Error::new_program_error(format!("Unrecognized directive `{directive}` in list expression #{i}: {expr}")));
                }
            }
        }
        let Some(formula) = formula.take() else {
            return Err(Error::new_program_error(format!("No `result` directive given")));
        };
        let (cond, pred) = match (condition.take(), predicate.take()) {
            (None, None) => {
                return Err(Error::new_program_error(format!("No `condition` or `predicate` directive given")));
            }
            (Some(..), Some(..)) => {
                return Err(Error::new_program_error(format!("Both `condition` and `predicate` directives given. Use only one or the other.")));
            },
            (Some(cond), None) => {
                (Some(cond), Box::new(Predicate::True))
            }
            (None, Some(pred)) => {
                (None, pred)
            }
        };

        let halt = Self {
            formula,
            predicate: pred,
            condition: cond,
            vars,
            map_state,
            map_tombstones,
            reachable_var_reads,
            reachable_var_writes,
            reachable_map_reads,
            reachable_map_writes,
            early_return,
            panicking,
            analyze_write_reachability
        };

        Ok(halt)
    }

    pub fn to_comment_block(&self) -> String {
        let halt = format!("{}", self);
        let mut halt_strs = halt.split("\n");
        let mut halt_with_comments = vec![];
        while let Some(halt_str) = halt_strs.next() {
            halt_with_comments.push(format!(";;     {halt_str}"));
        }
        let halts = halt_with_comments.join("\n");
        halts
    }
}

impl fmt::Display for Halt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "(halt\n")?;
        write!(f, "  (result {})\n", self.formula)?;
        if let Some(cond) = self.condition.as_ref() {
            write!(f, "  (condition {cond})\n")?;
        }
        else {
            write!(f, "  (predicate {})\n", self.predicate)?;
        }
        for (var_name, symop) in self.vars.iter() {
            write!(f, "  (var-write\n    {var_name}\n    {symop})\n")?;
        }
        for (map_name, map_state) in self.map_state.iter() {
            for (key, value) in map_state {
                write!(f, "  (map-write\n    {map_name}\n      {key}\n      {value})\n")?;
            }
        }
        for (map_name, keys) in self.map_tombstones.iter() {
            for key in keys {
                write!(f, "  (map-delete\n    {map_name}\n    {key})\n")?;
            }
        }
        for name in self.reachable_var_writes.iter() {
            if self.vars.contains_key(name) {
                continue;
            }
            write!(f, "  (reachable-var-write {name})\n")?;
        }
        for name in self.reachable_map_writes.iter() {
            if self.map_state.contains_key(name) || self.map_tombstones.contains_key(name) {
                continue;
            }
            write!(f, "  (reachable-map-write {name})\n")?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl From<Continuation> for Halt {
    fn from(cont: Continuation) -> Self {
        Self {
            formula: Box::new(cont.final_formula),
            predicate: Box::new(cont.predicate),
            condition: None,
            vars: cont.var_state,
            map_state: cont.map_state,
            map_tombstones: cont.map_tombstones,
            reachable_var_reads: cont.reachable_var_reads,
            reachable_var_writes: cont.reachable_var_writes,
            reachable_map_reads: cont.reachable_map_reads,
            reachable_map_writes: cont.reachable_map_writes,
            early_return: cont.early_return,
            panicking: cont.panicking,
            analyze_write_reachability: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    /// No-op
    Test(String),
    /// Define a symbol with the given name.  It will be substituted into subsequent formulae
    /// as-is (a "dumb" macro)
    DefineSymbol(ClarityName, SymOp),
    /// Specify a halting state that must be met by a resulting continuation
    Halt(Halt),
    /// Specify a trait concretization for a function definition
    /// (trait-name, trait-impl-contract-id)
    ConcretizeTrait(ClarityName, QualifiedContractIdentifier),
    /// Skip a function call, and treat it as a symbol.
    /// * if attached to a function definition, then a name must be given
    /// * if attached to the callsite, then no name needs to be given.
    SkipFunctionCall(Option<ClarityName>),
    /// Skip a contract-call, and treat it as a symbol.
    /// * if attached to a function definition, then a fullname must be given
    /// * if attached to the callsite, then no name needs to be given
    SkipContractCall(Option<FullName>),
    /// Stop exploring from this continuation and exit 
    StopExploring,
    /// Drop early-return continuations
    DropEarlyReturns,
    /// Force the result of all continuations produced to have this symop
    SetResult(SymOp),
    /// Explore each continuation, even if they all have the same result
    /// Sets `combine_continuations` to false
    /// Sets `skip_pure` to false
    /// Sets `skip_causally_independent_calls` to false
    ExploreAll,
    /// Load and instantiate a dependent smart contract
    Dependency(QualifiedContractIdentifier, String, Option<StandardPrincipalData>),
    /// The contract's deployed ID
    ContractId(QualifiedContractIdentifier),
    /// This contract's sponsor
    ContractSponsor(StandardPrincipalData),
    /// Default trait impelmentation 
    DefaultTraitImpl(TraitIdentifier, QualifiedContractIdentifier),
    /// Log some debug output
    PrintLn(SymOp),
    /// Print out the current continuation for the given symbolic expression
    PrintContinuation,
    /// Print out all computed continuations for this symbolic expression
    PrintProducedContinuations,
    /// Pause execution at the given symblic expression
    Pause(SymbolicExpression),
    /// Ensure that a given (boolean) invariant holds in all continuations
    Invariant(SymOp),
}


impl From<Halt> for Command {
    fn from(h: Halt) -> Command {
        Command::Halt(h)
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Test(msg) => write!(f, "(test \"{msg}\")"),
            Self::DefineSymbol(name, op) => write!(f, "(define-symbol {name} {op})"),
            Self::Halt(halt) => write!(f, "{halt}"),
            Self::ConcretizeTrait(var_name, contract) => write!(f, "(concretize-trait {var_name} '{contract})"),
            Self::SkipFunctionCall(name_opt) => {
                if let Some(name) = name_opt.as_ref() {
                    write!(f, "(skip-function-call {name})")
                }
                else {
                    write!(f, "(skip-function-call)")
                }
            }
            Self::SkipContractCall(name_opt) => {
                if let Some(name) = name_opt.as_ref() {
                    write!(f, "(skip-contract-call {name})")
                }
                else {
                    write!(f, "(skip-contract-call)")
                }
            }
            Self::StopExploring => write!(f, "(stop)"),
            Self::DropEarlyReturns => write!(f, "(drop-early-returns)"),
            Self::SetResult(op) => write!(f, "(set-result {op})"),
            Self::ExploreAll => write!(f, "(explore-all)"),
            Self::Dependency(contract_id, path, sponsor_opt) => {
                if let Some(sponsor) = sponsor_opt.as_ref() {
                    write!(f, "(dependency {contract_id} u\"{path}\" '{sponsor})")
                }
                else {
                    write!(f, "(dependency {contract_id} u\"{path}\")")
                }
            }
            Self::ContractId(contract_id) => write!(f, "(contract-id '{contract_id})"),
            Self::ContractSponsor(sponsor) => write!(f, "(contract-sponsor '{sponsor})"),
            Self::DefaultTraitImpl(trait_id, contract_id) => write!(f, "(defailt-trait-impl {trait_id} '{contract_id})"),
            Self::PrintLn(symop) => write!(f, "(println {symop})"),
            Self::PrintContinuation => write!(f, "(print-continuation)"),
            Self::PrintProducedContinuations => write!(f, "(print-produced-continuations)"),
            Self::Pause(..) => write!(f, "(pause)"),
            Self::Invariant(op) => write!(f, "(invariant {op})"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CommandContext {
    /// defined formulae names and values, which must be stored in order since they will be applied
    /// in order via rewrite rules.
    used_names: HashMap<ClarityName, usize>,
    defined_formulae: Vec<(ClarityName, SymOp)>,
}

impl CommandContext {
    pub fn new() -> Self {
        Self {
            used_names: HashMap::new(),
            defined_formulae: vec![],
        }
    }

    pub fn parse_symop(&self, expr: &SymbolicExpression) -> Result<SymOp, Error> {
        let mut symop = SymOp::try_from(expr)?;
        for (name, op) in self.defined_formulae.iter() {
            symop = *symop.bind_symbol(name.clone().into(), op.clone());
        }
        Ok(symop)
    }

    fn decode_to_string(string_data: &CharType) -> Result<String, Error> {
        let s = match string_data {
            CharType::ASCII(ascii_data) => {
                let s = String::from_utf8_lossy(&ascii_data.data).to_string();
                s
            }
            CharType::UTF8(utf8_data) => {
                let mut s = String::new();
                for c_bytes in utf8_data.data.iter() {
                    let mut u32_bytes = [0u8; 4];
                    if c_bytes.len() >= 1 {
                        u32_bytes[0] = c_bytes[0];
                    }
                    if c_bytes.len() >= 2 {
                        u32_bytes[1] = c_bytes[1];
                    }
                    if c_bytes.len() >= 3 {
                        u32_bytes[2] = c_bytes[2];
                    }
                    if c_bytes.len() == 4 {
                        u32_bytes[3] = c_bytes[3];
                    }

                    let cu32 = u32::from_be_bytes(u32_bytes);
                    let chr = char::from_u32(cu32).ok_or_else(|| Error::new_program_error(format!("Invalid UTF-8 path: {:?}", utf8_data.data)))?;
                    s.push(chr);
                }
                s
            }
        };
        Ok(s)
    }

    pub fn try_interpret(&mut self, command_name: &str, exprs: &[SymbolicExpression], body: Option<&SymbolicExpression>) -> Result<Command, Error> {
        match command_name {
            "test" => {
                if exprs.len() != 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` expects 1 argument, got {}", exprs.len())));
                }
                let op = SymOp::try_from(&exprs[0])?;
                let op_str = format!("{op}");
                if op_str == "\"force-failure!\"" {
                    return Err(Error::new_program_error(format!("`{command_name}` command forced to fail")));
                }
                Ok(Command::Test(format!("{op}")))
            },
            "define-symbol" => {
                if exprs.len() != 2 {
                    return Err(Error::new_program_error(format!("`{command_name}` expects 2 arguments, got {}", exprs.len())));
                }

                let Some(name) = exprs[0].match_atom() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects an atom as its first argument, got {}", &exprs[0])));
                };
                let formula = self.parse_symop(&exprs[1])?;
                if self.used_names.contains_key(name) {
                    return Err(Error::new_program_error(format!("Name already used: `{name}` in `(define-symbol {name} {formula})`")));
                }

                let idx = self.defined_formulae.len();
                self.defined_formulae.push((name.clone(), formula.clone()));
                self.used_names.insert(name.clone(), idx);

                Ok(Command::DefineSymbol(name.clone(), formula))
            }
            "halt" => {
                Ok(Command::Halt(Halt::from_symbolic_expressions(self, exprs)?))
            }
            "concretize-trait" => {
                if exprs.len() != 2 {
                    return Err(Error::new_program_error(format!("`{command_name}` expects 3 arguments, got {}", exprs.len())));
                }
                let Some(var_name) = exprs[0].match_atom() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects an atom (a function argument name) for its first argument, got {}", &exprs[0])));
                };
                let Some(Value::Principal(PrincipalData::Contract(contract_id))) = exprs[1].match_literal_value() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects an principal literal (the concretized trait address) for its second argument, got {}", &exprs[1])));
                };
                Ok(Command::ConcretizeTrait(var_name.clone(), contract_id.clone()))
            },
            "skip-function-call" => {
                let name_opt = if exprs.len() == 1 {
                    let Some(name) = exprs[0].match_atom() else {
                        return Err(Error::new_program_error(format!("`{command_name}` expects an atom (a function name) for its first argument, got {}", &exprs[0])));
                    };
                    Some(name)
                }
                else if exprs.len() > 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` expects only 1 argument, got {}", exprs.len())));
                }
                else {
                    None
                };
                Ok(Command::SkipFunctionCall(name_opt.cloned()))
            }
            "skip-contract-call" => {
                let name_opt = if exprs.len() == 1 {
                    let name = SymOp::match_fullname(&exprs[0])?;
                    Some(name)
                }
                else if exprs.len() > 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` expects only 1 argument, got {}", exprs.len())));
                }
                else {
                    None
                };
                Ok(Command::SkipContractCall(name_opt))
            }
            "stop" => {
                if exprs.len() > 0 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 0 arguments, got {}", exprs.len())));
                }
                Ok(Command::StopExploring)
            },
            "drop-early-returns" => {
                if exprs.len() > 0 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 0 arguments, got {}", exprs.len())));
                }
                Ok(Command::DropEarlyReturns)
            }
            "set-result" => {
                if exprs.len() != 2 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 1 argument, got {}", exprs.len())));
                }
                let result = self.parse_symop(&exprs[0])?;
                Ok(Command::SetResult(result))
            }
            "explore-all" => {
                if exprs.len() > 0 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 0 arguments, got {}", exprs.len())));
                }
                Ok(Command::ExploreAll)
            }
            "dependency" => {
                if exprs.len() < 2 || exprs.len() > 3 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 2-3 arguments, got {}", exprs.len())));
                }
                let Some(Value::Principal(PrincipalData::Contract(contract_id))) = exprs[0].match_literal_value() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects a contract principal literal (the concretized trait address) for its first argument, got {}", &exprs[0])));
                };
                let Some(Value::Sequence(SequenceData::String(string_data))) = exprs[1].match_literal_value() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects a string literal (the path to the concretized trait source code) for its second argument, got {}", &exprs[1])));
                };
                let sponsor_opt = if exprs.len() == 3 {
                    let Some(Value::Principal(PrincipalData::Standard(sponsor))) = exprs[2].match_literal_value() else {
                        return Err(Error::new_program_error(format!("`{command_name}` expects a standard principal literal (the concretized trait address) for its third argument, got {}", &exprs[2])));
                    };
                    Some(sponsor.clone())
                }
                else {
                    None
                };

                let code = Self::decode_to_string(string_data)?;
                Ok(Command::Dependency(contract_id.clone(), code, sponsor_opt))
            }
            "contract-id" => {
                if exprs.len() != 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 1 argument, got {}", exprs.len())));
                }
                let Some(Value::Principal(PrincipalData::Contract(contract_id))) = exprs[0].match_literal_value() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects a contract principal literal (the deployed contract ID) for its first argument, got {}", &exprs[0])));
                };
                Ok(Command::ContractId(contract_id.clone()))
            }
            "contract-sponsor" => {
                if exprs.len() != 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 1 argument, got {}", exprs.len())));
                }
                let Some(Value::Principal(PrincipalData::Standard(sponsor))) = exprs[0].match_literal_value() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects a standard principal literal (the concretized trait address) for its first argument, got {}", &exprs[0])));
                };
                Ok(Command::ContractSponsor(sponsor.clone()))
            }
            "default-trait-impl" => {
                if exprs.len() != 2 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 2 argument, got {}", exprs.len())));
                }
                let Some(trait_id) = exprs[0].match_field() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects a trait ID for its first argument, got {}", &exprs[0])));
                };
                let Some(Value::Principal(PrincipalData::Contract(contract_id))) = exprs[1].match_literal_value() else {
                    return Err(Error::new_program_error(format!("`{command_name}` expects a contract principal literal (the default implementation address) for its second argument, got {}", &exprs[1])));
                };
                Ok(Command::DefaultTraitImpl(trait_id.clone(), contract_id.clone()))
            }
            "println" => {
                if exprs.len() != 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 1 argument, got {}", exprs.len())));
                }
                let expr = SymOp::try_from(&exprs[0])?;
                Ok(Command::PrintLn(expr))
            }
            "print-continuation" => {
                if exprs.len() != 0 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes no arguments, got {}", exprs.len())));
                }
                Ok(Command::PrintContinuation)
            }
            "print-produced-continuations" => {
                if exprs.len() != 0 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes no arguments, got {}", exprs.len())));
                }
                Ok(Command::PrintProducedContinuations)
            }
            "pause" => {
                if exprs.len() != 0 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes no arguments, got {}", exprs.len())));
                }
                let Some(body) = body else {
                    return Err(Error::new_program_error(format!("`{command_name}` requires a symbolic expression")));
                };
                Ok(Command::Pause(body.clone()))
            }
            "invariant" => {
                if exprs.len() != 1 {
                    return Err(Error::new_program_error(format!("`{command_name}` takes 1 argument, got {}", exprs.len())));
                }
                let symop = self.parse_symop(&exprs[0])?;
                Ok(Command::Invariant(symop))
            }
            _ => {
                Err(Error::NotFound(format!("Unrecognized command '{command_name}'")))
            }
        }
    }
}

impl SymOp {
    /// Decode a SymOp from a list of SymbolicExpressions which has the form
    /// `(op_name op1 op2 ...)`
    /// Returns Ok(list-of-ops) if the first symbolic expression is an atom matching `expected_name` and has the expected number of ops
    /// Returns Err(..) otherwise.
    fn decode_symop_ops(min_len: usize, max_len: Option<usize>, symexps: &[SymbolicExpression]) -> Result<Vec<Box<Self>>, Error> {
        if symexps.len() < min_len {
            return Err(Error::new_program_error(format!("Symbolic expression list `( {} )` has unexpected length {} (expected at least {min_len})", symexps.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(" "), symexps.len())));
        }
        
        if let Some(max_len) = max_len && symexps.len() > max_len {
            return Err(Error::new_program_error(format!("Symbolic expression list `( {} )` has more than {} items (expected at least {max_len})", symexps.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(" "), symexps.len())));
        }

        let mut ret = vec![];
        for exp in symexps.iter() {
            let op = SymOp::try_from(exp)?;
            ret.push(Box::new(op));
        }
        Ok(ret)
    }

    fn decode_1op(symexps: &[SymbolicExpression]) -> Result<Box<Self>, Error> {
        let mut ops = Self::decode_symop_ops(1, Some(1), symexps)?;
        let Some(op1) = ops.pop() else {
            return Err(Error::Bug("Did not get 1 op".into()));
        };
        Ok(op1)
    }

    fn decode_2ops(symexps: &[SymbolicExpression]) -> Result<(Box<Self>, Box<Self>), Error> {
        let mut ops = Self::decode_symop_ops(2, Some(2), symexps)?;
        let Some(op2) = ops.pop() else {
            return Err(Error::Bug("Did not get op2".into()));
        };
        let Some(op1) = ops.pop() else {
            return Err(Error::Bug("Did not get op1".into()));
        };
        Ok((op1, op2))
    }

    fn decode_3ops(symexps: &[SymbolicExpression]) -> Result<(Box<Self>, Box<Self>, Box<Self>), Error> {
        let mut ops = Self::decode_symop_ops(3, Some(3), symexps)?;
        let Some(op3) = ops.pop() else {
            return Err(Error::Bug("Did not get op3".into()));
        };
        let Some(op2) = ops.pop() else {
            return Err(Error::Bug("Did not get op2".into()));
        };
        let Some(op1) = ops.pop() else {
            return Err(Error::Bug("Did not get op1".into()));
        };
        Ok((op1, op2, op3))
    }
    
    fn decode_4ops(symexps: &[SymbolicExpression]) -> Result<(Box<Self>, Box<Self>, Box<Self>, Box<Self>), Error> {
        let mut ops = Self::decode_symop_ops(4, Some(4), symexps)?;
        let Some(op4) = ops.pop() else {
            return Err(Error::Bug("Did not get op4".into()));
        };
        let Some(op3) = ops.pop() else {
            return Err(Error::Bug("Did not get op3".into()));
        };
        let Some(op2) = ops.pop() else {
            return Err(Error::Bug("Did not get op2".into()));
        };
        let Some(op1) = ops.pop() else {
            return Err(Error::Bug("Did not get op1".into()));
        };
        Ok((op1, op2, op3, op4))
    }

    fn decode_5ops(symexps: &[SymbolicExpression]) -> Result<(Box<Self>, Box<Self>, Box<Self>, Box<Self>, Box<Self>), Error> {
        let mut ops = Self::decode_symop_ops(5, Some(5), symexps)?;
        let Some(op5) = ops.pop() else {
            return Err(Error::Bug("Did not get op5".into()));
        };
        let Some(op4) = ops.pop() else {
            return Err(Error::Bug("Did not get op4".into()));
        };
        let Some(op3) = ops.pop() else {
            return Err(Error::Bug("Did not get op3".into()));
        };
        let Some(op2) = ops.pop() else {
            return Err(Error::Bug("Did not get op2".into()));
        };
        let Some(op1) = ops.pop() else {
            return Err(Error::Bug("Did not get op1".into()));
        };
        Ok((op1, op2, op3, op4, op5))
    }

    fn decode_varops(symexps: &[SymbolicExpression]) -> Result<Vec<Box<Self>>, Error> {
        let ops = Self::decode_symop_ops(2, None, symexps)?;
        Ok(ops)
    }
    
    fn decode_varops1(symexps: &[SymbolicExpression]) -> Result<Vec<Box<Self>>, Error> {
        let ops = Self::decode_symop_ops(1, None, symexps)?;
        Ok(ops)
    }
    
    fn decode_varops0(symexps: &[SymbolicExpression]) -> Result<Vec<Box<Self>>, Error> {
        let ops = Self::decode_symop_ops(0, None, symexps)?;
        Ok(ops)
    }

    fn match_fullname(symexp: &SymbolicExpression) -> Result<FullName, Error> {
        let Some(name_field) = symexp.match_field().cloned() else {
            return Err(Error::new_program_error(format!("Fullname `{symexp}` is not a fully-qualified name")));
        };
        let name = FullName(name_field.contract_identifier, name_field.name);
        Ok(name)
    }
}

struct InterpreterGetContractSymOps { }

impl InterpreterGetContractSymOps {
    pub fn new() -> Self {
        Self { }
    }
}

impl GetContractSymOps for InterpreterGetContractSymOps {
    fn get_tx_sender_symop(&self) -> SymOp {
        SymOp::Variable(Sym::Principal("tx-sender".into()))
    }

    fn get_tx_sponsor_symop(&self) -> SymOp {
        SymOp::Variable(Sym::Principal("tx-sponsor?".into()))
    }

    fn get_contract_caller_symop(&self) -> SymOp {
        SymOp::Variable(Sym::Principal("contract-caller".into()))
    }

    fn get_current_contract_symop(&self) -> SymOp {
        SymOp::Variable(Sym::Principal("current-contract".into()))
    }
}

impl SymOp {
    fn inner_try_from(symexp: &SymbolicExpression) -> Result<Self, Error> {
        trace!("Decode: `{symexp}`");
        if let Some(value) = symexp.match_literal_value() {
            // constant
            return Ok(Self::Constant(value.clone()));
        }
        if let Some(sym) = symexp.match_atom() {
            if let Some(symop) = Symbex::try_atom_as_symbol(&InterpreterGetContractSymOps::new(), sym)? {
                return Ok(symop);
            };
            return Err(Error::new_program_error(format!("Symbolic expression is an unrecognized atom: {symexp}")));
        }
        let Some(lv) = symexp.match_list() else {
            return Err(Error::new_program_error(format!("Symbolic expression is not a literal value or a list: {symexp}")));
        };
        let Some(first) = lv.get(0) else {
            return Err(Error::new_program_error(format!("Symbolic expression is empty: {symexp}")));
        };
        let Some(second) = lv.get(1) else {
            return Err(Error::new_program_error(format!("Symbolic expression has only one element: {symexp}")));
        };

        let Some(first_name_atom) = first.match_atom() else {
            return Err(Error::new_program_error(format!("Symbolic expression `{first}` is not an atom (in {symexp})")));
        };

        // if `first` is an atom and `second` is a type signature, then this is a symbol
        if let Ok(ts) = TypeSignature::parse_type_repr(DEFAULT_STACKS_EPOCH, second, &mut ()) {
            let sym = Sym::from_name_and_type_signature(first_name_atom, &ts);
            return Ok(Self::Variable(sym));
        }

        let Some(opexps) = lv.get(1..) else {
            return Err(Error::new_program_error(format!("Symbolic expression has only one element: {symexp}")));
        };

        let first_name = first_name_atom.as_str();

        // everything else takes the form `(name op1 op2 ...)`
        let symop = match first_name {
            "loaded-var"
            | "loaded-var-const"
            | "loaded-var-type"
            | "loaded-var-sym" => {
                let var_name = Self::match_fullname(second)?;
                let Some(value_symexp) = lv.get(2) else {
                    return Err(Error::new_program_error(format!("loaded-var variable value not given in {symexp}")));
                };

                match first_name {
                    "loaded-var" | "loaded-var-sym" => {
                        let value = Box::new(Self::try_from(value_symexp)?);
                        SymOp::LoadedDataVariable(var_name, value)
                    },
                    "loaded-var-const" => {
                        let Self::Constant(value) = Self::try_from(value_symexp)? else {
                            return Err(Error::new_program_error(format!("`(loaded-var-const {var_name} x)` where `x` is not a constant (but is `{value_symexp}`) (in {symexp})")));
                        };
                        SymOp::LoadedDataVariable(var_name, Box::new(Self::Constant(value)))
                    },
                    "loaded-var-type" => {
                        let Ok(ts) = TypeSignature::parse_type_repr(DEFAULT_STACKS_EPOCH, value_symexp, &mut ()) else {
                            return Err(Error::new_program_error(format!("`(loaded-var-type {var_name} x)` where `x` is not a type signature (but is `{value_symexp}`) (in {symexp})")));
                        };
                        let local_name = var_name.name().clone();
                        SymOp::LoadedDataVariable(var_name, Box::new(Self::Variable(Sym::from_name_and_type_signature(&local_name, &ts))))
                    },
                    _x => {
                        unreachable!()
                    }
                }
            }
            "+" => Self::Add(Self::decode_varops(opexps)?),
            "-" => Self::Subtract(Self::decode_varops1(opexps)?),
            "*" => Self::Multiply(Self::decode_varops(opexps)?),
            "/" => Self::Divide(Self::decode_varops(opexps)?),
            "mod" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Modulo(op1, op2)
            }
            "to-int" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ToInt(op1)
            }
            "to-uint" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ToUInt(op1)
            }
            "power" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Power(op1, op2)
            }
            "sqrti" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Sqrti(op1)
            }
            "log2" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Log2(op1)
            }
            "and" => Self::And(Self::decode_varops(opexps)?),
            "or" => Self::Or(Self::decode_varops(opexps)?),
            "not" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Not(op1)
            }
            ">" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Greater(op1, op2)
            }
            ">=" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Geq(op1, op2)
            }
            "is-eq" => Self::Equals(Self::decode_varops(opexps)?),
            "<=" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Leq(op1, op2)
            }
            "<" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Less(op1, op2)
            }
            "append" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Append(op1, op2)
            }
            "concat" => Self::Concat(Self::decode_varops(opexps)?),
            "as-max-len?" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::AsMaxLen(op1, op2)
            }
            "len" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Len(op1)
            }
            "element-at" | "element-at?" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::ElementAt(op1, op2)
            }
            "index-of" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::IndexOf(op1, op2)
            }
            "buff-to-int-le" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::BuffToIntLe(op1)
            }
            "buff-to-int-be" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::BuffToIntBe(op1)
            }
            "buff-to-uint-le" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::BuffToUIntLe(op1)
            }
            "buff-to-uint-be" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::BuffToUIntBe(op1)
            }
            "is-standard" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IsStandard(op1)
            }
            "principal-destruct" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::PrincipalDestruct(op1)
            }
            "principal-construct" => {
                let mut ops = Self::decode_varops(opexps)?;
                if ops.len() == 2 {
                    let op2 = ops.pop().expect("unreachable");
                    let op1 = ops.pop().expect("unreachable");
                    Self::PrincipalConstruct(op1, op2, None)
                }
                else if ops.len() == 3 {
                    let op3 = ops.pop().expect("unreachable");
                    let op2 = ops.pop().expect("unreachable");
                    let op1 = ops.pop().expect("unreachable");
                    Self::PrincipalConstruct(op1, op2, Some(op3))
                }
                else {
                    return Err(Error::new_program_error(format!("principal-construct takes 2 or 3 args; got {}", lv.len() - 1)));
                }
            },
            "string-to-int?" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::StringToInt(op1)
            }
            "string-to-uint?" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::StringToUInt(op1)
            }
            "int-to-ascii" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IntToAscii(op1)
            }
            "int-to-utf8" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IntToUtf8(op1)
            }
            "list" => Self::ListCons(Self::decode_varops0(opexps)?),
            "var-get" => {
                let var_name = Self::match_fullname(second)?;
                Self::FetchVar(var_name)
            }
            "var-set" => {
                let var_name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::SetVar(var_name, op1)
            }
            "map-get?" => {
                let map_name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::FetchEntry(map_name, op1)
            }
            "map-entry"
            | "map-entry-const"
            | "map-entry-type"
            | "map-entry-sym" => {
                let map_name = Self::match_fullname(second)?;
                let Some(key_sym) = lv.get(2) else {
                    return Err(Error::new_program_error(format!("map `{second}` has no key symbolic expression (in {symexp})")));
                };
                let key_symop = Box::new(Self::try_from(key_sym)?);
                let value_symop_opt = match lv.get(3) {
                    Some(val_sym) => Some(Box::new(Self::try_from(val_sym)?)),
                    None => None
                };

                match first_name {
                    "map-entry"
                    | "map-entry-sym" => Self::LoadedMapEntry(map_name, key_symop, value_symop_opt),
                    "map-entry-const" => {
                        let Some(Self::Constant(value)) = value_symop_opt.map(|op| *op) else {
                            return Err(Error::new_program_error(format!("map-entry-const `{second}` has no constant value (in {symexp})")));
                        };
                        Self::LoadedMapEntry(map_name, key_symop, Some(Box::new(Self::Constant(value))))
                    }
                    "map-entry-type" => {
                        let Some(Self::Variable(sym)) = value_symop_opt.map(|op| *op) else {
                            return Err(Error::new_program_error(format!("map-entry-type `{second}` has no symbol value (in {symexp})")));
                        };
                        let Some(ts_symexp) = lv.get(4) else {
                            return Err(Error::new_program_error(format!("map-entry-type `{second}` has no type signature (in {symexp})")));
                        };
                        let Ok(ts) = TypeSignature::parse_type_repr(DEFAULT_STACKS_EPOCH, ts_symexp, &mut ()) else {
                            return Err(Error::new_program_error(format!("map-entry-type `{second}` has invalid type signature `{ts_symexp}`")));
                        };
                        // parity check
                        if sym.type_str() != format!("{ts}") {
                            return Err(Error::new_program_error(format!("map-entry-type `{second}` has invalid type signature: expected `{}`, got `{ts}`", sym.type_str())));
                        };
                        Self::LoadedMapEntry(map_name, key_symop, Some(Box::new(Self::Variable(sym))))
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            "map-set" => {
                let map_name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and two arguments")))?;
                let (op1, op2) = Self::decode_2ops(args)?;
                Self::SetEntry(map_name, op1, op2)
            }
            "map-insert" => {
                let map_name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and two arguments")))?;
                let (op1, op2) = Self::decode_2ops(args)?;
                Self::InsertEntry(map_name, op1, op2)
            }
            "map-delete" => {
                let map_name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and two arguments")))?;
                let op1 = Self::decode_1op(args)?;
                Self::DeleteEntry(map_name, op1)
            }
            "tuple" => {
                let mut inner = vec![];
                for (i, name_and_opexp_symexp) in opexps.iter().enumerate() {
                    let Some(name_and_opexp) = name_and_opexp_symexp.match_list() else {
                        return Err(Error::new_program_error(format!("tuple binding #{i} ({name_and_opexp_symexp}) is not a list (in {symexp})")));
                    };
                    if name_and_opexp.len() != 2 {
                        return Err(Error::new_program_error(format!("tuple binding #{i} ({name_and_opexp_symexp}) is not a 2-item list (in {symexp})")));
                    }
                    let Some(name) = name_and_opexp[0].match_atom() else {
                        return Err(Error::new_program_error(format!("First item in tuple binding #{i} ({name_and_opexp_symexp}) is not an atom (in {symexp})")));
                    };
                    let op = Self::try_from(&name_and_opexp[1])?;
                    inner.push((name.clone(), Box::new(op)));
                }
                Self::TupleCons(inner)
            },
            "get" => {
                let Some(field_name_atom) = second.match_atom() else {
                    return Err(Error::new_program_error(format!("tuple field name `{second}` is not an atom (in {symexp})")));
                };
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::TupleGet(field_name_atom.clone(), op1)
            }
            "merge" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::TupleMerge(op1, op2)
            }
            "hash160" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Hash160(op1)
            }
            "sha256" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Sha256(op1)
            }
            "sha512" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Sha512(op1)
            }
            "sha512/256" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Sha512Trunc256(op1)
            }
            "keccak256" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::Keccak256(op1)
            }
            "secp256k1-recover?" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::Secp256k1Recover(op1, op2)
            }
            "secp256k1-verify" => {
                let (op1, op2, op3) = Self::decode_3ops(opexps)?;
                Self::Secp256k1Verify(op1, op2, op3)
            }
            "contract-of" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ContractOf(op1)
            }
            "principal-of" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::PrincipalOf(op1)
            }
            "is-ok" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IsOkay(op1)
            }
            "is-err" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IsErr(op1)
            }
            "is-some" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IsSome(op1)
            }
            "is-none" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::IsNone(op1)
            }
            "unwrap-panic" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::UnwrapPanic(op1)
            }
            "unwrap-err-panic" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::UnwrapErrPanic(op1)
            }
            "err" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ConsError(op1)
            }
            "ok" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ConsOkay(op1)
            }
            "some" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ConsSome(op1)
            }
            "ft-get-balance" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::GetTokenBalance(name, op1)
            }
            "nft-get-owner?" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::GetNftOwner(name, op1)
            }
            "ft-transfer?" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and 3 arguments")))?;
                let (op1, op2, op3) = Self::decode_3ops(args)?;
                Self::TransferToken(name, op1, op2, op3)
            }
            "nft-transfer?" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and 3 arguments")))?;
                let (op1, op2, op3) = Self::decode_3ops(args)?;
                Self::TransferNft(name, op1, op2, op3)
            }
            "ft-mint?" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and 2 arguments")))?;
                let (op1, op2) = Self::decode_2ops(args)?;
                Self::MintToken(name, op1, op2)
            }
            "nft-mint" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and 2 arguments")))?;
                let (op1, op2) = Self::decode_2ops(args)?;
                Self::MintNft(name, op1, op2)
            }
            "ft-get-supply" => {
                let name = Self::match_fullname(second)?;
                Self::GetTokenSupply(name)
            }
            "ft-burn?" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::BurnToken(name, op1)
            }
            "nft-burn?" => {
                let name = Self::match_fullname(second)?;
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and 2 arguments")))?;
                let (op1, op2) = Self::decode_2ops(args)?;
                Self::BurnNft(name, op1, op2)
            }
            "stx-get-balance" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::GetStxBalance(op1)
            }
            "stx-transfer?" => {
                let (op1, op2, op3) = Self::decode_3ops(opexps)?;
                Self::StxTransfer(op1, op2, op3)
            }
            "stx-transfer-memo?" => {
                let (op1, op2, op3, op4) = Self::decode_4ops(opexps)?;
                Self::StxTransferMemo(op1, op2, op3, op4)
            }
            "stx-burn?" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::StxBurn(op1)
            }
            "stx-account" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::StxGetAccount(op1)
            }
            "bit-and" => Self::BitwiseAnd(Self::decode_varops(opexps)?),
            "bit-or" => Self::BitwiseOr(Self::decode_varops(opexps)?),
            "bit-xor" | "xor" => Self::BitwiseXor(Self::decode_varops(opexps)?),
            "bit-not" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::BitwiseNot(op1)
            }
            "bit-shift-left" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::BitwiseLShift(op1, op2)
            }
            "bit-shift-right" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::BitwiseRShift(op1, op2)
            }
            "slice" | "slice?" => {
                let (op1, op2, op3) = Self::decode_3ops(opexps)?;
                Self::Slice(op1, op2, op3)
            }
            "to-consensus-buff?" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ToConsensusBuff(op1)
            }
            "from-consensus-buff?" => {
                let Some(ts_symexp) = lv.get(1) else {
                    return Err(Error::new_program_error(format!("`{first_name}` is missing a type signature (in {symexp})")));
                };
                let Some(buf_sym) = lv.get(2) else {
                    return Err(Error::new_program_error(format!("`{first_name}` is missing a buffer (in {symexp})")));
                };

                let Ok(ts) = TypeSignature::parse_type_repr(DEFAULT_STACKS_EPOCH, ts_symexp, &mut ()) else {
                    return Err(Error::new_program_error(format!("Failed to parse type signature `{ts_symexp}` (in {symexp})")));
                };
                let buf_symop = Box::new(Self::try_from(buf_sym)?);
                Self::FromConsensusBuff(ts, buf_symop)
            }
            "replace-at?" => {
                let (op1, op2, op3) = Self::decode_3ops(opexps)?;
                Self::ReplaceAt(op1, op2, op3)
            }
            "get-stacks-block-info?" => {
                let Some(name_atom) = second.match_atom() else {
                    return Err(Error::new_program_error(format!("NFT name `{second}` is not an atom (in {symexp})")));
                };
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::GetStacksBlockInfo(name_atom.clone(), op1)
            }
            "get-tenure-info?" => {
                let Some(name_atom) = second.match_atom() else {
                    return Err(Error::new_program_error(format!("NFT name `{second}` is not an atom (in {symexp})")));
                };
                let args = lv.get(2..).ok_or_else(|| Error::new_program_error(format!("{first_name} expected a name and an argument")))?;
                let op1 = Self::decode_1op(args)?;
                Self::GetTenureInfo(name_atom.clone(), op1)
            }
            "contract-hash" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ContractHash(op1)
            }
            "to-ascii?" => {
                let op1 = Self::decode_1op(opexps)?;
                Self::ToAscii(op1)
            }
            "secp256r1-verify?" => {
                let (op1, op2, op3) = Self::decode_3ops(opexps)?;
                Self::Secp256r1Verify(op1, op2, op3)
            }
            "verify-merkle-proof" => {
                let (op1, op2, op3, op4, op5) = Self::decode_5ops(opexps)?;
                Self::VerifyMerkleProof(op1, op2, op3, op4, op5)
            }
            "get-bitcoin-tx-output?" => {
                let (op1, op2) = Self::decode_2ops(opexps)?;
                Self::GetBitcoinTxOutput(op1, op2)
            }
            x => {
                return Err(Error::Bug(format!("Unrecognized Clarity function `{x}`")));
            }
        };
        Ok(symop)
    }
}

impl TryFrom<&SymbolicExpression> for SymOp {
    type Error = Error;
    fn try_from(symexp: &SymbolicExpression) -> Result<Self, Error> {
        match Self::inner_try_from(symexp) {
            Ok(op) => Ok(op),
            Err(e) => Err(e.program_error(symexp.span.start_line, format!("in {symexp}"))),
        }
    }
}

impl CommandContext {
    /// Extract the program to run from within `(@clairvoyance ...)`
    pub fn extract_command_programs(command_buff: &str) -> Vec<String> {
        #[derive(Debug)]
        enum TokenState {
            NormalComment,
            BeginProgram(String),
            // tokens, next-token, quoted, comment, nesting start-depth
            Program(Vec<String>, Option<String>, bool, bool, usize)
        }

        let mut state = TokenState::NormalComment;
        let mut nesting : usize = 0;
        let mut programs = vec![];

        let advance_token = |c: char, tokens: Vec<String>, mut cur_tok: Option<String>, quoted: bool, comment: bool, depth: usize| {
            if let Some(tok) = cur_tok.as_mut() {
                tok.push(c);
            }
            else {
                cur_tok.replace(c.to_string());
            }
            TokenState::Program(tokens, cur_tok, quoted, comment, depth)
        };

        let mut consume_program = |mut tokens: Vec<String>, mut cur_tok: Option<String>| {
            if let Some(tok) = cur_tok.take() {
                tokens.push(tok);
            }

            let program = tokens.join(" ");
            if program.len() > 0 {
                programs.push(program);
            }
        };

        let mut last_c = None;
       
        trace!("decode `{command_buff}`");
        for c in command_buff.chars() {
            match c {
                '(' => {
                    state = match state {
                        TokenState::NormalComment => {
                            nesting += 1;
                            TokenState::BeginProgram("".to_string())
                        }
                        TokenState::BeginProgram(..) => {
                            nesting += 1;
                            TokenState::BeginProgram("".to_string())
                        }
                        TokenState::Program(mut tokens, mut cur_tok, quoted, comment, depth) => {
                            if !comment {
                                if !quoted {
                                    nesting += 1;
                                    if let Some(tok) = cur_tok.take() {
                                        tokens.push(tok);
                                    }
                                    tokens.push(c.to_string());
                                    TokenState::Program(tokens, None, false, false, depth)
                                }
                                else {
                                    advance_token(c, tokens, cur_tok, quoted, comment, depth)
                                }
                            }
                            else {
                                TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                            }
                        }
                    };
                }
                ')' => {
                    state = match state {
                        TokenState::NormalComment => {
                            nesting = nesting.saturating_sub(1);
                            TokenState::NormalComment
                        }
                        TokenState::BeginProgram(..) => {
                            nesting = nesting.saturating_sub(1);
                            TokenState::NormalComment
                        }
                        TokenState::Program(mut tokens, mut cur_tok, quoted, comment, depth) => {
                            if !comment {
                                if !quoted {
                                    assert!(nesting > 0, "BUG: parsing a program with zero nesting");
                                    nesting -= 1;
                                    if nesting < depth {
                                        consume_program(tokens, cur_tok);
                                        TokenState::NormalComment
                                    }
                                    else {
                                        if let Some(tok) = cur_tok.take() {
                                            tokens.push(tok);
                                        }

                                        tokens.push(c.to_string());
                                        TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                                    }
                                }
                                else {
                                    advance_token(c, tokens, cur_tok, quoted, comment, depth)
                                }
                            }
                            else {
                                TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                            }
                        }
                    }
                }
                ' ' | '\t' | '\r' | '\n' => {
                    state = match state {
                        TokenState::NormalComment => TokenState::NormalComment,
                        TokenState::BeginProgram(clairvoyance_tag) => {
                            if clairvoyance_tag == "@clairvoyance" {
                                TokenState::Program(vec![], None, false, false, nesting)
                            }
                            else {
                                TokenState::NormalComment
                            }
                        },
                        TokenState::Program(mut tokens, mut cur_tok, quoted, comment, depth) => {
                            let comment = comment && c != '\n';
                            if !comment {
                                if !quoted {
                                    if let Some(tok) = cur_tok.take() {
                                        tokens.push(tok);
                                    }
                                    TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                                }
                                else {
                                    advance_token(c, tokens, cur_tok, quoted, comment, depth)
                                }
                            }
                            else {
                                TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                            }
                        }
                    }
                }
                '"' => {
                    state = match state {
                        TokenState::NormalComment => TokenState::NormalComment,
                        TokenState::BeginProgram(..) => TokenState::NormalComment,
                        TokenState::Program(tokens, cur_tok, quoted, comment, depth) => {
                            if !comment {
                                if let Some(last_c) = last_c.as_ref() {
                                    if *last_c == '\\' {
                                        advance_token(c, tokens, cur_tok, quoted, comment, depth)
                                    }
                                    else {
                                        advance_token(c, tokens, cur_tok, !quoted, comment, depth)
                                    }
                                }
                                else {
                                    advance_token(c, tokens, cur_tok, !quoted, comment, depth)
                                }
                            }
                            else {
                                TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                            }
                        }
                    }
                }
                x => {
                    if x == ';' && last_c == Some(';') {
                        state = match state {
                            TokenState::NormalComment => TokenState::NormalComment,
                            TokenState::BeginProgram(..) => TokenState::NormalComment,
                            TokenState::Program(mut tokens, mut cur_tok, quoted, comment, depth) => {
                                if !quoted {
                                    // pop the last ';'
                                    if let Some(t) = cur_tok.as_mut() && t.len() > 0 {
                                        let _ = t.pop();
                                        if t.len() == 0 {
                                            cur_tok = None;
                                        }
                                    }
                                    else if let Some(t) = tokens.last_mut() && t.len() > 0 {
                                        let _ = t.pop();
                                    }
                                    TokenState::Program(tokens, cur_tok, quoted, true, depth)
                                }
                                else {
                                    advance_token(c, tokens, cur_tok, quoted, comment, depth)
                                }
                            }
                        }
                    }
                    else {
                        state = match state {
                            TokenState::NormalComment => TokenState::NormalComment,
                            TokenState::BeginProgram(mut tag) => {
                                tag.push(x);
                                TokenState::BeginProgram(tag)
                            }
                            TokenState::Program(tokens, cur_tok, quoted, comment, depth) => {
                                if !comment {
                                    advance_token(c, tokens, cur_tok, quoted, comment, depth)
                                }
                                else {
                                    TokenState::Program(tokens, cur_tok, quoted, comment, depth)
                                }
                            }
                        }
                    }
                }
            }
            trace!("c = {c}, last_c = {last_c:?}, nesting = {nesting}, state = {state:?}");
            last_c = Some(c);
        }

        if let TokenState::Program(tokens, cur_tok, quoted, ..) = state {
            if !quoted {
                consume_program(tokens, cur_tok);
            }
        }

        programs
    }

    pub fn eval_program(&mut self, prog: &str, source_start_line: u32, origin_symexp: Option<&SymbolicExpression>) -> Result<Vec<Command>, Error> {
        let contract_id = QualifiedContractIdentifier::new(StandardPrincipalData::transient(), "clairvoyance".try_into()?);
        let mut ast = ast::parse_ast(&contract_id, prog)?;

        let mut symexp_ptrs = VecDeque::new();
        for exp in ast.expressions.iter_mut() {
            symexp_ptrs.push_back(exp);
        }
        while let Some(exp) = symexp_ptrs.pop_front() {
            exp.span.start_line += source_start_line;
            exp.span.end_line += source_start_line;
            if let SymbolicExpressionType::List(exps) = &mut exp.expr {
                for exp in exps {
                    symexp_ptrs.push_back(exp);
                }
            }
        }
        
        // program is in the form of:
        // ```
        // (@clairvoyance
        //     (clairvoyance-directive ...)
        //     (clairvoyance-directive ...)
        //     ...)

        let exprs = ast.expressions;
        let mut commands = vec![];
        for (i, expr) in exprs.iter().enumerate() {
            let Some(lv) = expr.match_list() else {
                return Err(Error::new_program_error(format!("Directive #{i} is not a list: {expr}")));
            };
            if lv.len() == 0 {
                return Err(Error::new_program_error(format!("Directive #{i} is empty")));
            }
            let Some(directive_expr) = lv.get(0) else {
                return Err(Error::new_program_error(format!("Directive #{i} is empty")));
            };
            let Some(directive_name) = directive_expr.match_atom() else {
                return Err(Error::new_program_error(format!("Directive #{i} does not start with an atom (got `{directive_expr}` in `{expr}`)")));
            };

            let symexps = lv.get(1..).unwrap_or(&[]);
            let command = self.try_interpret(directive_name.as_str(), symexps, origin_symexp)?;
            commands.push(command);
        }
        Ok(commands)
    }

    /// Extract and interpret commands from pre-comments.
    pub fn eval(&mut self, symexp: &SymbolicExpression) -> Result<Vec<Command>, Error> {
        let mut comments = vec![];
        let mut start_line : Option<u32> = None;
        for (command, span) in symexp.pre_comments.iter() {
            if let Some(sl) = start_line.as_mut() {
                *sl = (*sl).min(span.start_line);
            }
            else {
                start_line = Some(span.start_line);
            }

            comments.push(command.clone());
        }
        let Some(start_line) = start_line else {
            return Ok(vec![]);
        };
       
        let comment_buff = comments.join("\n");
        if comment_buff.len() > 0 {
            debug!("Got comments on {symexp}:\n{comment_buff}");
        }

        let programs = Self::extract_command_programs(&comment_buff);
        
        let mut commands = vec![];
        for program in programs.iter() {
            let com = self.eval_program(program, start_line, Some(symexp))?;
            commands.extend(com.into_iter());
        }
        Ok(commands)
    }
}

