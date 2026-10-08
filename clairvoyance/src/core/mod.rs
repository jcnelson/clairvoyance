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

use std::fmt;
use std::collections::HashMap;
use std::collections::HashSet;

use clarity_types::Value;
use clarity_types::ClarityName;
use clarity_types::types::TypeSignature;
use clarity_types::representations::SymbolicExpression;
use clarity_types::types::{PrincipalData, StandardPrincipalData, QualifiedContractIdentifier};
use stacks_common::types::StacksEpochId;
use clarity::vm::database::ClarityDatabase;
use clarity::vm::database::MemoryBackingStore;
use clarity::vm::analysis::AnalysisDatabase;
use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::analysis::errors::CommonCheckErrorKind;
use clarity::vm::errors::StaticCheckError;
use clarity::vm::errors::ClarityEvalError;
use clarity::vm::errors::VmExecutionError;
use clarity::vm::errors::ClarityTypeError;
use clarity::vm::contracts::Contract;

use clarity::vm::ClarityVersion;
use clarity::vm::ast::errors::ParseError;
use crate::sym::FullName;
use crate::sym::command::Halt;
use crate::sym::{Predicate, Continuation, SymOp};

pub const DEFAULT_STACKS_EPOCH : StacksEpochId = StacksEpochId::Epoch40;
pub const DEFAULT_CLARITY_VERSION: ClarityVersion = ClarityVersion::Clarity6;

pub mod ast;

pub struct BackingStore {
    store: MemoryBackingStore
}

impl fmt::Debug for BackingStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BackingStore")
    }
}

impl PartialEq for BackingStore {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl BackingStore {
    pub fn new() -> Self {
        Self {
            store: MemoryBackingStore::new()
        }
    }

    pub fn as_clarity_db(&mut self) -> ClarityDatabase<'_> {
        self.store.as_clarity_db()
    }

    pub fn as_analysis_db(&mut self) -> AnalysisDatabase<'_> {
        self.store.as_analysis_db()
    }

    pub fn get_contract(&mut self, contract_id: &QualifiedContractIdentifier) -> Result<Contract, Error> {
        Ok({
            let mut db = self.as_clarity_db();
            db.begin();
            let contract_res = db.get_contract(contract_id);
            db.roll_back()?;
            contract_res?
        })
    }

    pub fn get_contract_analysis(&mut self, contract_id: &QualifiedContractIdentifier) -> Result<ContractAnalysis, Error> {
        Ok({
            let mut db = self.as_analysis_db();
            db.begin();
            let analysis_res = db.load_contract(contract_id, &DEFAULT_STACKS_EPOCH);
            db.roll_back()?;
            analysis_res?.ok_or_else(|| Error::NotFound(format!("No analysis loaded for {}", contract_id)))?
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct ProofFailures {
    /// continuations not checked by the list of halting states
    pub unchecked_continuations: Vec<Continuation>,
    /// extraneous halting conditions that could not be matched to a continuation
    pub unmatched_halting_conditions: Vec<Predicate>,

    /// incorrect written variable -- variable was written in this continuation,
    /// but it has the wrong value
    /// (matched-continuation, var-name, var-value, wrong-var-value)
    pub incorrect_var_writes: Vec<(Continuation,  FullName, SymOp, SymOp)>,
    /// missing written variable -- variable listed by the proof but not written in this continuation
    pub missing_var_writes: Vec<(Continuation,  FullName)>,
    /// extraneous written variable -- variable was listed in the proof, but not written in any
    /// continuation
    pub unmatched_var_writes: Vec<(FullName, SymOp)>,
    /// unchecked written variable -- variable was written in the continuation, but not checked by
    /// the proof
    pub unchecked_var_writes: Vec<(Continuation, FullName, SymOp)>,

    /// incorrect map-write
    /// (matched-continuation, map-name, map-key, map-value, wrong-map-value)
    pub incorrect_map_writes: Vec<(Continuation, FullName, SymOp, SymOp, SymOp)>,
    /// missing map write: no map write for given key in the given continuation
    pub missing_map_writes: Vec<(Continuation, FullName, SymOp)>,
    /// extraneous map write
    pub unmatched_map_writes: Vec<(FullName, SymOp, SymOp)>,
    /// unchecked map writes
    pub unchecked_map_writes: Vec<(Continuation, FullName, SymOp, SymOp)>,

    /// no given map-delete in continuation
    pub missing_map_deletes: Vec<(Continuation, FullName, SymOp)>,
    /// extraneous map delete
    pub unmatched_map_deletes: Vec<(FullName, SymOp)>,
    /// unchecked map deletes
    pub unchecked_map_deletes: Vec<(Continuation, FullName, SymOp)>,

    /// early-return mismatch
    pub early_return_mismatch: bool,
    /// panicking mismatch
    pub panicking_mismatch: bool,

    /// unchecked reachable var read -- a map was read in the continuation, but not checked in
    /// the proof
    pub unchecked_reachable_var_writes: HashMap<Predicate, HashSet<FullName>>,
    /// unmatched reachable var read -- a map was declared read in the proof, but not present
    /// in any continuation
    pub unmatched_reachable_var_writes: HashMap<Predicate, HashSet<FullName>>,
    /// unchecked reachable map write -- a map was written in the continuation, but not checked in
    /// the proof
    pub unchecked_reachable_map_writes: HashMap<Predicate, HashSet<FullName>>,
    /// unmatched reachable map read -- a map was declared written in the proof, but not present
    /// in any continuation
    pub unmatched_reachable_map_writes: HashMap<Predicate, HashSet<FullName>>,
}

impl ProofFailures {
    pub fn new() -> Self {
        Self {
            unchecked_continuations: vec![],
            unmatched_halting_conditions: vec![],
            incorrect_var_writes: vec![],
            missing_var_writes: vec![],
            unmatched_var_writes: vec![],
            unchecked_var_writes: vec![],
            incorrect_map_writes: vec![],
            missing_map_writes: vec![],
            unmatched_map_writes: vec![],
            unchecked_map_writes: vec![],
            missing_map_deletes: vec![],
            unmatched_map_deletes: vec![],
            unchecked_map_deletes: vec![],
            early_return_mismatch: false,
            panicking_mismatch: false,
            unchecked_reachable_var_writes: HashMap::new(),
            unmatched_reachable_var_writes: HashMap::new(),
            unchecked_reachable_map_writes: HashMap::new(),
            unmatched_reachable_map_writes: HashMap::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.unchecked_continuations.len() == 0
        && self.unmatched_halting_conditions.len() == 0
        && self.incorrect_var_writes.len() == 0
        && self.missing_var_writes.len() == 0
        && self.unmatched_var_writes.len() == 0
        && self.unchecked_var_writes.len() == 0
        && self.incorrect_map_writes.len() == 0
        && self.missing_map_writes.len() == 0
        && self.unmatched_map_writes.len() == 0
        && self.unchecked_map_writes.len() == 0
        && self.missing_map_deletes.len() == 0
        && self.unmatched_map_deletes.len() == 0
        && self.unchecked_map_deletes.len() == 0
        && !self.early_return_mismatch
        && !self.panicking_mismatch
        && self.unchecked_reachable_var_writes.len() == 0
        && self.unmatched_reachable_var_writes.len() == 0
        && self.unchecked_reachable_map_writes.len() == 0
        && self.unmatched_reachable_map_writes.len() == 0
    }

    pub fn unchecked_continuation(&mut self, cont: Continuation) {
        debug!("Continuation not checked by given halting conditions:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        self.unchecked_continuations.push(cont);
    }

    pub fn unmatched_halting_condition(&mut self, cond: Predicate) {
        debug!("Halting condition '{cond}' did not match any continuation");
        self.unmatched_halting_conditions.push(cond);
    }

    pub fn incorrect_var_write(&mut self, cont: Continuation, var_name: FullName, computed_var_value: SymOp, given_var_value: SymOp) {
        debug!("Incorrect var-set:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("  Variable: {var_name}");
        debug!("  Expected: {computed_var_value}");
        debug!("     Given: {given_var_value}");
        self.incorrect_var_writes.push((cont, var_name, computed_var_value, given_var_value));
    }

    pub fn missing_var_write(&mut self, cont: Continuation, var_name: FullName) {
        debug!("Missing var-set:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("  Variable: {var_name}");
        self.missing_var_writes.push((cont, var_name));
    }

    pub fn unmatched_var_write(&mut self, var_name: FullName, value: SymOp) {
        debug!("Unmatched given var-set:");
        debug!("  Variable: {var_name}");
        debug!("     Given: {value}");
        self.unmatched_var_writes.push((var_name, value));
    }

    pub fn unchecked_var_write(&mut self, cont: Continuation, var_name: FullName, computed_var_value: SymOp) {
        debug!("Unchecked var-set:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("  Variable: {var_name}");
        debug!("  Expected: {computed_var_value}");
        self.unchecked_var_writes.push((cont, var_name, computed_var_value));
    }
    
    pub fn incorrect_map_write(&mut self, cont: Continuation, map_name: FullName, map_key: SymOp, computed_map_value: SymOp, given_map_value: SymOp) {
        debug!("Incorrect map-insert or map-set:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("       Map: {map_name}");
        debug!("       Key: {map_key}");
        debug!("  Expected: {computed_map_value}");
        debug!("     Given: {given_map_value}");
        self.incorrect_map_writes.push((cont, map_name, map_key, computed_map_value, given_map_value));
    }
    
    pub fn missing_map_write(&mut self, cont: Continuation, map_name: FullName, map_key: SymOp) {
        debug!("Incorrect map-insert or map-set:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("       Map: {map_name}");
        debug!("       Key: {map_key}");
        self.missing_map_writes.push((cont, map_name, map_key));
    }

    pub fn unmatched_map_write(&mut self, map_name: FullName, map_key: SymOp, value: SymOp) {
        debug!("Unmatched given map-insert or map-set:");
        debug!("       Map: {map_name}");
        debug!("       Key: {map_key}");
        debug!("     Given: {value}");
        self.unmatched_map_writes.push((map_name, map_key, value));
    }

    pub fn unchecked_map_write(&mut self, cont: Continuation, map_name: FullName, map_key: SymOp, computed_map_value: SymOp) {
        debug!("Unchecked map-insert or map-set:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("       Map: {map_name}");
        debug!("       Key: {map_key}");
        debug!("  Expected: {computed_map_value}");
        self.unchecked_map_writes.push((cont, map_name, map_key, computed_map_value));
    }
    
    pub fn missing_map_delete(&mut self, cont: Continuation, map_name: FullName, map_key: SymOp) {
        debug!("Missing map-delete:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("       Map: {map_name}");
        debug!(" Given key: {map_key}");
        self.missing_map_deletes.push((cont, map_name, map_key));
    }

    pub fn unmatched_map_delete(&mut self, map_name: FullName, value: SymOp) {
        debug!("Unmatched given map-delete:");
        debug!("       Map: {map_name}");
        debug!("     Given: {value}");
        self.unmatched_map_deletes.push((map_name, value));
    }

    pub fn unchecked_map_delete(&mut self, cont: Continuation, map_name: FullName, computed_map_key: SymOp) {
        debug!("Unchecked map-delete:");
        debug!("      Path: {}", &cont.get_function_path());
        debug!("   Formula: {}", &cont.final_formula);
        debug!("       Map: {map_name}");
        debug!("  Expected: {computed_map_key}");
        self.unchecked_map_deletes.push((cont, map_name, computed_map_key));
    }


    pub fn unchecked_reachable_var_write(&mut self, pred: Predicate, name: FullName) {
        debug!("Unchecked reachable var write {name} in condition {pred}");
        if let Some(names) = self.unchecked_reachable_var_writes.get_mut(&pred) {
            names.insert(name);
        }
        else {
            let mut names = HashSet::new();
            names.insert(name);
            self.unchecked_reachable_var_writes.insert(pred, names);
        }
    }
    
    pub fn unmatched_reachable_var_write(&mut self, pred: Predicate, name: FullName) {
        debug!("Unmatched reachable var write {name} in condition {pred}");
        if let Some(names) = self.unmatched_reachable_var_writes.get_mut(&pred) {
            names.insert(name);
        }
        else {
            let mut names = HashSet::new();
            names.insert(name);
            self.unmatched_reachable_var_writes.insert(pred, names);
        }
    }
    
    pub fn unchecked_reachable_map_write(&mut self, pred: Predicate, name: FullName) {
        debug!("Unchecked reachable map write {name} in condition {pred}");
        if let Some(names) = self.unchecked_reachable_map_writes.get_mut(&pred) {
            names.insert(name);
        }
        else {
            let mut names = HashSet::new();
            names.insert(name);
            self.unchecked_reachable_map_writes.insert(pred, names);
        }
    }
    
    pub fn unmatched_reachable_map_write(&mut self, pred: Predicate, name: FullName) {
        debug!("Unmatched reachable map write {name} in condition {pred}");
        if let Some(names) = self.unmatched_reachable_map_writes.get_mut(&pred) {
            names.insert(name);
        }
        else {
            let mut names = HashSet::new();
            names.insert(name);
            self.unmatched_reachable_map_writes.insert(pred, names);
        }
    }

    pub fn unaccounted_continuation(&mut self, cont: Continuation) {
        self.unchecked_continuation(cont.clone());
        for (name, val) in cont.var_state.iter() {
            self.unchecked_var_write(cont.clone(), name.clone(), val.clone());
        }
        for (name, state) in cont.map_state.iter() {
            for (key, value) in state.iter() {
                self.unchecked_map_write(cont.clone(), name.clone(), key.clone(), value.clone());
            }
        }
        for (name, keys) in cont.map_tombstones.iter() {
            for key in keys.iter() {
                self.unchecked_map_delete(cont.clone(), name.clone(), key.clone());
            }
        }
    }

    /// Compute proof failures from a list of continuations (computed state) and halts (given /
    /// proof state).
    pub fn from_continuations_and_halts(mut conts: Vec<Continuation>, halts: Vec<Halt>) -> Result<Self, Error> {
        let mut failures = ProofFailures::new();

        let rolled_up_conts : Vec<_> = conts
            .into_iter()
            .map(|c| c.rollup())
            .collect();
        conts = rolled_up_conts;

        trace!("Expected halting states:");
        for h in halts.iter() {
            trace!("   Condition:\n{}", &h.predicate.clone().simplify()?.as_symop().to_pretty_string(5));
            trace!("   Formula:   {}", &h.formula.clone().simplify()?);
            let mut var_names : Vec<_> = h.vars.keys().collect();
            var_names.sort();
            for var_name in var_names {
                let var_val = h.vars.get(&var_name).expect("infallible");
                trace!("   Var:       {}", var_val.clone().simplify()?);
            }
            for (map_name, map) in h.map_state.iter() {
                trace!("   Map state: {map_name}");
                for (key, value) in map.iter() {
                    trace!("      key:   {key}");
                    trace!("      value: {value}");
                }
            }
            for (map_name, map) in h.map_tombstones.iter() {
                trace!("   Map deletes: {map_name}");
                for key in map.iter() {
                    trace!("      key:   {key}");
                }
            }
            for var_name in h.reachable_var_reads.iter() {
                trace!("   Reachable var read: {var_name}");
            }
            for map_name in h.reachable_map_reads.iter() {
                trace!("   Reachable map read: {map_name}");
            }
            for var_name in h.reachable_var_writes.iter() {
                trace!("   Reachable var write: {var_name}");
            }
            for map_name in h.reachable_map_writes.iter() {
                trace!("   Reachable map write: {map_name}");
            }
        }

        trace!("Computed halting states:");
        for c in conts.iter() {
            trace!("   ID:        {}", c.id);
            trace!("   Path:      {}", &c.get_function_path());
            trace!("   Condition:\n{}", &c.predicate.clone().simplify()?.as_symop().to_pretty_string(5));
            trace!("   Formula:   {}", &c.final_formula.clone().simplify()?);
            let mut keys : Vec<_> = c.var_state.keys().collect();
            keys.sort();
            for k in keys.iter() {
                let v = c.var_state.get(k).expect("unreachable");
                trace!("   Var:       {v}");
            }
            for (map_name, map) in c.map_state.iter() {
                trace!("   Map state: {map_name}");
                for (key, value) in map.iter() {
                    let key = key.clone().simplify()?;
                    let value = value.clone().simplify()?;
                    trace!("      key:   {key}");
                    trace!("      value: {value}");
                }
                for (map_name, map) in c.map_tombstones.iter() {
                    trace!("   Map deletes: {map_name}");
                    for key in map.iter() {
                        trace!("      key:   {key}");
                    }
                }
            }
            for var_name in c.reachable_var_reads.iter() {
                trace!("   Reachable var read: {var_name}");
            }
            for map_name in c.reachable_map_reads.iter() {
                trace!("   Reachable map read: {map_name}");
            }
            for var_name in c.reachable_var_writes.iter() {
                trace!("   Reachable var write: {var_name}");
            }
            for map_name in c.reachable_map_writes.iter() {
                trace!("   Reachable map write: {map_name}");
            }
        }

        // each continuation must have reached exactly one halt
        for h in halts.iter() {
            let mut found_cont = None;
            for (i, cont) in conts.iter().enumerate() {
                let logic_matches = if let Some(cond) = h.condition.as_ref() {
                    let implication = cont.predicate.clone().not().or(*cond.clone()).simplify()?;
                    implication == Predicate::True
                }
                else {
                    cont.predicate.clone().simplify()? == h.predicate.clone().simplify()?
                };
                let formula_matches = cont.final_formula.clone().simplify()? == h.formula.clone().simplify()?;
                if logic_matches && formula_matches {
                    // check nature of the halt -- did it panic? did it early-return?
                    if cont.early_return != h.early_return {
                        failures.early_return_mismatch = true;
                    }
                    if cont.panicking != h.panicking {
                        failures.panicking_mismatch = true;
                    }

                    // check variable state
                    let mut var_state = cont.var_state.clone();
                    for (h_name, h_val) in h.vars.iter() {
                        let Some(v) = var_state.remove(h_name) else {
                            failures.missing_var_write(cont.clone(), h_name.clone());
                            continue;
                        };
                        if v != *h_val {
                            failures.incorrect_var_write(cont.clone(), h_name.clone(), v.clone(), h_val.clone());
                            continue;
                        }
                    }
                    for (name, val) in var_state.into_iter() {
                        failures.unchecked_var_write(cont.clone(), name, val);
                    }

                    // check map state
                    let mut map_state = cont.map_state.clone();
                    for (h_name, h_state) in h.map_state.iter() {
                        let Some(mut state) = map_state.remove(h_name) else {
                            for (h_key, _h_value) in h_state.iter() {
                                failures.missing_map_write(cont.clone(), h_name.clone(), h_key.clone());
                            }
                            continue;
                        };
                        for (h_key, h_value) in h_state.iter() {
                            let Some(value) = state.remove(h_key) else {
                                failures.missing_map_write(cont.clone(), h_name.clone(), h_key.clone());
                                continue;
                            };
                            if *h_value != value {
                                failures.incorrect_map_write(cont.clone(), h_name.clone(), h_key.clone(), value.clone(), h_value.clone());
                                continue;
                            }
                        }
                        for (key, value) in state.into_iter() {
                            failures.unchecked_map_write(cont.clone(), h_name.clone(), key, value);
                        }
                    }

                    // check map deletes
                    let mut map_tombstones = cont.map_tombstones.clone();
                    for (h_name, h_keys) in h.map_tombstones.iter() {
                        let Some(mut keys) = map_tombstones.remove(h_name) else {
                            for h_key in h_keys.iter() {
                                failures.missing_map_delete(cont.clone(), h_name.clone(), h_key.clone());
                            }
                            continue;
                        };
                        for h_key in h_keys.iter() {
                            if !keys.remove(h_key) {
                                failures.unmatched_map_delete(h_name.clone(), h_key.clone());
                            }
                        }
                    }
                    for (name, keys) in map_tombstones.into_iter() {
                        for key in keys.iter() {
                            failures.unchecked_map_delete(cont.clone(), name.clone(), key.clone());
                        }
                    }

                    if h.analyze_write_reachability {
                        for var_write in cont.reachable_var_writes.difference(&h.reachable_var_writes) {
                            failures.unchecked_reachable_var_write(cont.predicate.clone(), var_write.clone());
                        }
                        for var_write in h.reachable_var_writes.difference(&cont.reachable_var_writes) {
                            failures.unmatched_reachable_var_write(cont.predicate.clone(), var_write.clone());
                        }
                        for map_write in cont.reachable_map_writes.difference(&h.reachable_map_writes) {
                            failures.unchecked_reachable_map_write(cont.predicate.clone(), map_write.clone());
                        }
                        for map_write in h.reachable_map_writes.difference(&cont.reachable_map_writes) {
                            failures.unmatched_reachable_map_write(cont.predicate.clone(), map_write.clone());
                        }
                    }
                    found_cont = Some(i);
                    break;
                }
                else if logic_matches && !formula_matches {
                    trace!("Predicate {} matches, but not final formula:\n   Computed: {:?}\n      Given: {:?}\n",
                           &h.predicate.clone().to_pretty_string(1), cont.final_formula.clone().simplify()?, &h.formula);
                }
                else if !logic_matches && formula_matches {
                    trace!("Final formula {} matches, but not predicate:\n   Computed: {}\n      Given: {}\n",
                           &h.formula, cont.predicate.clone().simplify()?.to_pretty_string(1), &h.predicate.clone().to_pretty_string(1));
                }
            }

            let Some(i) = found_cont.take() else {
                // this halting condition does match any continuation
                if let Some(cond) = h.condition.as_ref() {
                    failures.unmatched_halting_condition(*cond.clone());
                }
                else {
                    failures.unmatched_halting_condition(*h.predicate.clone());
                }
                continue;
            };
            conts.remove(i);
        }

        if conts.len() > 0 {
            for c in conts {
                // this is an unaccounted continuation 
                failures.unaccounted_continuation(c);
            }
        }
        Ok(failures)
    }
}


impl fmt::Display for ProofFailures {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.unchecked_continuations.len() > 0 {
            for cont in self.unchecked_continuations.iter() {
                write!(f, "Unchecked halting state:\n{cont}\n")?;
                let halts = Halt::from(cont.clone()).to_comment_block();
                write!(f, "Unchecked halting description:\n{halts}\n")?;
            }
            write!(f, "\n")?;
        }
        if self.unmatched_halting_conditions.len() > 0 {
            for pred in self.unmatched_halting_conditions.iter() {
                write!(f, "Unmatched halting condition:\n{}", pred.clone().as_symop().to_pretty_string(1))?;
            }
            write!(f, "\n")?;
        }
        if self.incorrect_var_writes.len() > 0 {
            for (cont, var_name, computed_var_value, given_var_value) in self.incorrect_var_writes.iter() {
                writeln!(f, "Incorrect var-set:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "  Variable: {var_name}")?;
                writeln!(f, "  Expected: {computed_var_value}")?;
                writeln!(f, "     Given: {given_var_value}")?;
            }
        }
        if self.missing_var_writes.len() > 0 {
            for (cont, var_name) in self.missing_var_writes.iter() {
                writeln!(f, "Missing var-set:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "  Variable: {var_name}")?;
            }
        }
        if self.unmatched_var_writes.len() > 0 {
            for (var_name, value) in self.unmatched_var_writes.iter() {
                writeln!(f, "Unmatched given var-set:")?;
                writeln!(f, "  Variable: {var_name}")?;
                writeln!(f, "     Given: {value}")?;
            }
        }
        if self.unchecked_var_writes.len() > 0 {
            for (cont, var_name, computed_var_value) in self.unchecked_var_writes.iter() {
                writeln!(f, "Unchecked var-set:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "  Variable: {var_name}")?;
                writeln!(f, "  Expected: {computed_var_value}")?;
            }
        }
        if self.incorrect_map_writes.len() > 0 {
            for (cont, map_name, map_key, computed_map_value, given_map_value) in self.incorrect_map_writes.iter() {
                writeln!(f, "Incorrect map-insert or map-set:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "       Map: {map_name}")?;
                writeln!(f, "       Key: {map_key}")?;
                writeln!(f, "  Expected: {computed_map_value}")?;
                writeln!(f, "     Given: {given_map_value}")?;
            }
        }
        if self.missing_map_writes.len() > 0 {
            for (cont, map_name, map_key) in self.missing_map_writes.iter() {
                writeln!(f, "Missing map-insert or map-set:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "       Map: {map_name}")?;
                writeln!(f, "       Key: {map_key}")?;
            }
        }
        if self.unmatched_map_writes.len() > 0 {
            for (map_name, map_key, value) in self.unmatched_map_writes.iter() {
                writeln!(f, "Unmatched given map-insert or map-set:")?;
                writeln!(f, "       Map: {map_name}")?;
                writeln!(f, "       Key: {map_key}")?;
                writeln!(f, "     Given: {value}")?;
            }
        }
        if self.unchecked_map_writes.len() > 0 {
            for (cont, map_name, map_key, computed_map_value) in self.unchecked_map_writes.iter() {
                writeln!(f, "Unchecked map-insert or map-set:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "       Map: {map_name}")?;
                writeln!(f, "       Key: {map_key}")?;
                writeln!(f, "  Expected: {computed_map_value}")?;
            }
        }
        if self.missing_map_deletes.len() > 0 {
            for (cont, map_name, key) in self.missing_map_deletes.iter() {
                writeln!(f, "Missing map-delete:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "       Map: {map_name}")?;
                writeln!(f, "       Key: {key}")?;
            }
        }
        if self.unmatched_map_deletes.len() > 0 {
            for (map_name, value) in self.unmatched_map_deletes.iter() {
                writeln!(f, "Unmatched given map-delete:")?;
                writeln!(f, "       Map: {map_name}")?;
                writeln!(f, "     Given: {value}")?;
            }
        }
        if self.unchecked_map_deletes.len() > 0 {
            for (cont, map_name, computed_map_key) in self.unchecked_map_deletes.iter() {
                writeln!(f, "Unchecked map-delete:")?;
                writeln!(f, "      Path: {}", &cont.get_function_path())?;
                writeln!(f, "   Formula: {}", &cont.final_formula)?;
                writeln!(f, "  Variable: {map_name}")?;
                writeln!(f, "  Expected: {computed_map_key}")?;
            }
        }
        if self.early_return_mismatch {
            writeln!(f, "Early-return mismatch")?;
        }
        if self.panicking_mismatch {
            writeln!(f, "Panicking mismatch")?;
        }

        if self.unchecked_reachable_var_writes.len() > 0 {
            for (pred, names) in self.unchecked_reachable_var_writes.iter() {
                writeln!(f, "Unchecked reachable variable writes in condition {pred}:")?;
                for name in names.iter() {
                    writeln!(f, "  {name}")?;
                }
            }
        }
        if self.unmatched_reachable_var_writes.len() > 0 {
            for (pred, names) in self.unmatched_reachable_var_writes.iter() {
                writeln!(f, "Unmatched reachable variable writes in condition {pred}:")?;
                for name in names.iter() {
                    writeln!(f, "  {name}")?;
                }
            }
        }
        if self.unchecked_reachable_map_writes.len() > 0 {
            for (pred, names) in self.unchecked_reachable_map_writes.iter() {
                writeln!(f, "Unchecked reachable map writes in condition {pred}:")?;
                for name in names.iter() {
                    writeln!(f, "  {name}")?;
                }
            }
        }
        if self.unmatched_reachable_map_writes.len() > 0 {
            for (pred, names) in self.unmatched_reachable_map_writes.iter() {
                writeln!(f, "Unmatched reachable map writes in condition {pred}:")?;
                for name in names.iter() {
                    writeln!(f, "  {name}")?;
                }
            }
        }

        if self.is_empty() {
            write!(f, "(all checks passed)\n")?;
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub struct ProgramError {
    pub line_no: Option<u32>,
    pub cause: String,
    pub stack: Vec<String>
}

impl fmt::Display for ProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let cause = &self.cause;
        let stack = &self.stack;
        if let Some(lineno) = self.line_no.as_ref() {
            write!(f, "Clairvoyance program error near line {lineno}: {cause}\n")?;
        }
        else {
            write!(f, "Clairvoyance program error: {cause}\n")?;
        }

        write!(f, "Backtrace:\n")?;
        for (i, stack_item) in stack.iter().enumerate() {
            write!(f, "{i}: {stack_item}\n")?;
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    /// Clarity AST construction error
    Parse(ParseError),
    /// Clarity eval error
    Eval(ClarityEvalError),
    /// Clarity VM execution error
    VM(VmExecutionError),
    /// Clarity type error
    Type(ClarityTypeError),
    /// Clarity typecheck error
    Check(CommonCheckErrorKind),
    /// Analysis error
    Analysis(StaticCheckError),
    /// Generic error message
    Failed(String),
    /// Something was not found
    NotFound(String),
    /// Arithmetic overflow or underflow
    Arithmetic(String),
    /// Incomparable types
    Comparison(String),
    /// Type converstion
    Conversion(String),
    /// Re-entrancy detected
    Reentrancy(FullName),
    /// Something happend that shouldn't have
    Bug(String),
    /// Invalid input
    Invalid(String),
    /// Clairvoyance program failed to parse
    Program(ProgramError),
    /// Clairvoyance program failed to run
    ProofFailure(ProofFailures),
    /// Directed to stop
    Stopped,
    /// Invariant failure
    InvariantFailure(SymbolicExpression, SymOp, Vec<Continuation>),
    /// Assumption failure
    AssumptionFailure(SymbolicExpression, SymOp),
}

impl Error {
    pub fn new_program_error(msg: String) -> Self {
        Self::Program(ProgramError {
            line_no: None,
            cause: msg,
            stack: vec![]
        })
    }

    pub fn program_error(self, lineno: u32, msg: String) -> Self {
        match self {
            Self::Program(mut program_error) => {
                program_error.stack.push(msg);
                program_error.line_no = Some(lineno);
                Self::Program(program_error)
            }
            x => {
                Self::Program(ProgramError {
                    line_no: Some(lineno),
                    cause: format!("{x:?}"),
                    stack: vec![msg]
                })
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Program(program_error) => {
                write!(f, "Clairvoynace was unable to parse an expression:\n")?;
                write!(f, "{program_error}\n")
            }
            Self::ProofFailure(failures) => {
                write!(f, "Clairvoyance encountered one or more errors while checking halting states:\n")?;
                write!(f, "{failures}\n")
            },
            Self::InvariantFailure(exp, inv, conts) => {
                write!(f, "Clairvoyance encountered one or more errors while checking invariants against symbolic continuations:\n")?;
                write!(f, "Current symbolic expression: {exp}\n")?;
                write!(f, "Invariant: {inv}\n")?;
                for cont in conts.iter() {
                    write!(f, "Violating halting state:\n{}\n", Halt::from(cont.clone()).to_comment_block())?;
                }
                Ok(())
            }
            Self::AssumptionFailure(exp, assumption) => {
                write!(f, "All symbolic continuations were found to be incompatible with an assumption\n")?;
                write!(f, "Current symbolic expression: {exp}\n")?;
                write!(f, "Assumption: {assumption}\n")?;
                Ok(())
            }
            x => {
                write!(f, "{x:?}")
            }
        }
    }
}

impl From<ParseError> for Error {
    fn from(pe: ParseError) -> Self {
        Self::Parse(pe)
    }
}

impl From<ClarityEvalError> for Error {
    fn from(ee: ClarityEvalError) -> Self {
        Self::Eval(ee)
    }
}

impl From<ClarityTypeError> for Error {
    fn from(te: ClarityTypeError) -> Self {
        Self::Type(te)
    }
}

impl From<VmExecutionError> for Error {
    fn from(ve: VmExecutionError) -> Self {
        Self::VM(ve)
    }
}

impl From<StaticCheckError> for Error {
    fn from(ae: StaticCheckError) -> Self {
        Self::Analysis(ae)
    }
}

impl From<CommonCheckErrorKind> for Error {
    fn from(ccek: CommonCheckErrorKind) -> Self {
        Self::Check(ccek)
    }
}
