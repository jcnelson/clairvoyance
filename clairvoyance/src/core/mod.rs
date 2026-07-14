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

use clarity_types::Value;
use clarity_types::ClarityName;
use clarity_types::types::TypeSignature;
use clarity_types::types::{PrincipalData, StandardPrincipalData, QualifiedContractIdentifier};
use stacks_common::types::StacksEpochId;
use clarity::vm::database::ClarityDatabase;
use clarity::vm::database::MemoryBackingStore;
use clarity::vm::analysis::AnalysisDatabase;
use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::errors::StaticCheckError;
use clarity::vm::errors::ClarityEvalError;
use clarity::vm::errors::VmExecutionError;
use clarity::vm::errors::ClarityTypeError;
use clarity::vm::contracts::Contract;

use clarity::vm::ClarityVersion;
use clarity::vm::ast::errors::ParseError;
use crate::sym::CallableName;

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
pub enum Error {
    /// Clarity AST construction error
    Parse(ParseError),
    /// Clarity eval error
    Eval(ClarityEvalError),
    /// Clarity VM execution error
    VM(VmExecutionError),
    /// Clarity type error
    Type(ClarityTypeError),
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
    Reentrancy(CallableName),
    /// Something happend that shouldn't have
    Bug(String),
    /// Invalid input
    Invalid(String),
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

