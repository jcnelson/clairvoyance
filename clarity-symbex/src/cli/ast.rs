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

use clarity::vm::types::QualifiedContractIdentifier;
use clarity::vm::ast::types::ContractAST;
use clarity::vm::contexts::ContractContext;
use clarity::vm::analysis::ContractAnalysis;

use crate::core::ast;
use crate::core::Error;
use crate::core::BackingStore;

use crate::cli::load_from_file_or_stdin;

use serde_json;

fn dump_ast(contract_id: &QualifiedContractIdentifier, code_path_or_stdin: &str) -> Result<ContractAST, Error> {
    let code_bytes = load_from_file_or_stdin(code_path_or_stdin)?;
    let code_str = str::from_utf8(&code_bytes)
        .map_err(|_e| Error::Failed("Code is not UTF-8".into()))?;

    let ast = ast::parse_ast(contract_id, code_str)?;
    Ok(ast)
}

fn dump_contract(contract_id: &QualifiedContractIdentifier, code_path_or_stdin: &str) -> Result<ContractContext, Error> {
    let code_bytes = load_from_file_or_stdin(code_path_or_stdin)?;
    let code_str = str::from_utf8(&code_bytes)
        .map_err(|_e| Error::Failed("Code is not UTF-8".into()))?;

    let mut backing_store = BackingStore::new();
    let context = ast::make_contract_context(&mut backing_store, contract_id, code_str)?;
    Ok(context)
}

fn dump_analysis(contract_id: &QualifiedContractIdentifier, code_path_or_stdin: &str) -> Result<ContractAnalysis, Error> {
    let code_bytes = load_from_file_or_stdin(code_path_or_stdin)?;
    let code_str = str::from_utf8(&code_bytes)
        .map_err(|_e| Error::Failed("Code is not UTF-8".into()))?;

    let mut backing_store = BackingStore::new();
    let analysis = ast::make_contract_analysis(&mut backing_store, contract_id, code_str)?;
    Ok(analysis)
}

pub fn cli_dump_ast(argv: &[String]) -> (i32, String) {
    let Some(contract_id_str) = argv.get(0) else {
        return (1, "Missing contract ID".into());
    };
    let Some(code_path_or_stdin) = argv.get(1) else {
        return (1, "Missing code".into());
    };
    let Ok(contract_id) = QualifiedContractIdentifier::parse(&contract_id_str) else {
        return (1, format!("Failed to parse {contract_id_str}"));
    };
    let contract_ast = match dump_ast(&contract_id, code_path_or_stdin) {
        Ok(ast) => ast,
        Err(e) => {
            return (2, format!("Failed to decode contract: {e:?}"));
        }
    };

    let contract_ast_str = match serde_json::to_string(&contract_ast) {
        Ok(ast_json) => ast_json,
        Err(e) => {
            return (2, format!("Failed to serialize contract AST to JSON: {e:?}"));
        }
    };

    (0, contract_ast_str)
}

pub fn cli_dump_contract(argv: &[String]) -> (i32, String) {
    let Some(contract_id_str) = argv.get(0) else {
        return (1, "Missing contract ID".into());
    };
    let Some(code_path_or_stdin) = argv.get(1) else {
        return (1, "Missing code".into());
    };
    let Ok(contract_id) = QualifiedContractIdentifier::parse(&contract_id_str) else {
        return (1, format!("Failed to parse {contract_id_str}"));
    };
    let context = match dump_contract(&contract_id, code_path_or_stdin) {
        Ok(context) => context,
        Err(e) => {
            return (2, format!("Failed to decode contract: {e:?}"));
        }
    };
    let context_str = match serde_json::to_string(&context) {
        Ok(context_json) => context_json,
        Err(e) => {
            return (2, format!("Failed to serialize contract context to JSON: {e:?}"));
        }
    };
    (0, context_str)
}

pub fn cli_dump_analysis(argv: &[String]) -> (i32, String) {
    let Some(contract_id_str) = argv.get(0) else {
        return (1, "Missing contract ID".into());
    };
    let Some(code_path_or_stdin) = argv.get(1) else {
        return (1, "Missing code".into());
    };
    let Ok(contract_id) = QualifiedContractIdentifier::parse(&contract_id_str) else {
        return (1, format!("Failed to parse {contract_id_str}"));
    };
    let analysis = match dump_analysis(&contract_id, code_path_or_stdin) {
        Ok(a) => a,
        Err(e) => {
            return (2, format!("Failed to decode contract: {e:?}"));
        }
    };
    let analysis_str = match serde_json::to_string(&analysis) {
        Ok(analysis_json) => analysis_json,
        Err(e) => {
            return (2, format!("Failed to serialize contract analysis to JSON: {e:?}"));
        }
    };
    (0, analysis_str)
}

pub fn run_cli_contract(argv: &mut Vec<String>) -> (i32, String) {
    if argv.len() == 0 {
        return (1, "Missing subcommand".into());
    }

    let subcommand = argv.remove(0);
    match subcommand.as_str() {
        "ast" => {
            cli_dump_ast(&argv)
        }
        "context" => {
            cli_dump_contract(&argv)
        }
        "analyze" => {
            cli_dump_analysis(&argv)
        }
        _ => {
            (1, format!("Unrecognized subcommand '{subcommand}'"))
        }
    }
}


