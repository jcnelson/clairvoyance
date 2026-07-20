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

use std::sync::Arc;

use crate::core::DEFAULT_STACKS_EPOCH;
use crate::core::DEFAULT_CLARITY_VERSION;

use crate::core::Error;
use crate::core::BackingStore;

use clarity_types::types::PrincipalData;

use clarity::vm::analysis;
use clarity::vm::analysis::ContractAnalysis;
use clarity::vm::types::QualifiedContractIdentifier;
use clarity::vm::ast::types::ContractAST;
use clarity::vm::ast::build_ast;
use clarity::vm::contexts::OwnedEnvironment;
use clarity::vm::contexts::ContractContext;
use clarity::vm::eval_all;
use clarity::vm::errors::ClarityEvalError;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::time_tracker::TimeTracker;

use stacks_common::consts::CHAIN_ID_MAINNET;

pub fn parse_ast(
    contract_id: &QualifiedContractIdentifier,
    code: &str
) -> Result<ContractAST, Error> {
    Ok(build_ast(contract_id, code, &mut (), DEFAULT_CLARITY_VERSION, DEFAULT_STACKS_EPOCH)?)
}

pub fn make_contract_analysis(
    backing_store: &mut BackingStore,
    contract_id: &QualifiedContractIdentifier,
    program: &str
) -> Result<ContractAnalysis, Error> {
    let ast = parse_ast(contract_id, program)?;
    make_contract_analysis_from_ast(backing_store, contract_id, &ast)
}

pub fn make_contract_analysis_from_ast(
    backing_store: &mut BackingStore,
    contract_id: &QualifiedContractIdentifier,
    ast: &ContractAST
) -> Result<ContractAnalysis, Error> {
    if let Ok(analysis) = backing_store.get_contract_analysis(contract_id) {
        return Ok(analysis);
    }

    let mut analysis_db = backing_store.as_analysis_db();
    let cost_track = LimitedCostTracker::new_free();
    analysis_db.begin();
    let analysis = match analysis::run_analysis(
        contract_id,
        &ast.expressions,
        &mut analysis_db,
        true,
        cost_track,
        DEFAULT_STACKS_EPOCH,
        DEFAULT_CLARITY_VERSION,
        true,
        TimeTracker::unlimited()
    ) {
        Ok(analysis) => analysis,
        Err(boxed_error) => {
            let (analysis_error, _) = *boxed_error;
            return Err(analysis_error.into());
        }
    };
    analysis_db.commit()?;

    Ok(analysis)
}

pub fn make_contract_context(
    backing_store: &mut BackingStore,
    contract_id: &QualifiedContractIdentifier,
    program: &str
) -> Result<ContractContext, Error> {
    let ast = parse_ast(contract_id, program)?;
    make_contract_context_from_ast(backing_store, contract_id, program, &ast, None)
}

pub fn make_contract_context_from_ast(
    backing_store: &mut BackingStore,
    contract_id: &QualifiedContractIdentifier,
    program: &str,
    ast: &ContractAST,
    sponsor: Option<PrincipalData>
) -> Result<ContractContext, Error> {
    let epoch_id = DEFAULT_STACKS_EPOCH;
    let clarity_version = DEFAULT_CLARITY_VERSION;

    let conn = backing_store.as_clarity_db();

    let mut env = OwnedEnvironment::new_free(true, CHAIN_ID_MAINNET, conn, epoch_id);

    let (_, _asset_map, _events) = env.initialize_contract_from_ast(
        contract_id.clone(),
        clarity_version,
        ast,
        program,
        sponsor
    )?;

    // get back the contract
    let contract = backing_store.get_contract(&contract_id)?;
    let mut context = Arc::into_inner(contract.contract_context).expect("infallible -- Arc<ContractContext> should have only one reference");
    context.canonicalize_types(&epoch_id)?;
    Ok(context)
}
