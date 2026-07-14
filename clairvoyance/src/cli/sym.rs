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

use clarity_types::types::{PrincipalData, StandardPrincipalData, QualifiedContractIdentifier};
use clarity_types::ClarityName;

use crate::sym::Symbex;
use crate::sym::Continuation;
use crate::sym::Callgraph;
use crate::sym::CallableName;
use crate::core::Error;
use crate::cli;

fn exec_user_function(
    contract_id: QualifiedContractIdentifier,
    src: &str,
    user_function: &str,
    tx_sender: Option<StandardPrincipalData>,
    contract_caller: Option<PrincipalData>,
    tx_sponsor: Option<StandardPrincipalData>,
    contract_tx_sponsor: Option<StandardPrincipalData>,
    skip_functions: bool,
    skip_function_list: Vec<ClarityName>,
    explore_all: bool
) -> Result<Vec<Continuation>, Error> {
    let mut symbex = Symbex::from_contract_ex(contract_id, src, contract_tx_sponsor)?
        .with_tx_sender(tx_sender)
        .with_tx_sponsor(tx_sponsor)
        .with_contract_caller(contract_caller)
        .with_function_call_exploration(!skip_functions)
        .skip_pure(!explore_all)
        .skip_causally_independent(!explore_all);

    for name in skip_function_list.into_iter() {
        symbex = symbex
            .with_skipped_function_call(name);
    }

    debug!("Symbolic execution begins on function '{user_function}'");
    symbex.eval_user_function(user_function)
}

fn cli_get_callgraph(
    src: &str,
    user_function: &str,
) -> Result<(Callgraph, CallableName), Error> {
    let contract_id = QualifiedContractIdentifier::transient();
    let symbex = Symbex::from_contract(contract_id.clone(), src)?;
    Ok((symbex.callgraph, CallableName(contract_id, ClarityName::try_from(user_function).map_err(|_| Error::Invalid("Invalid function name {user_function}".into()))?)))
}

/// NOTE: This prints out continuations as they arrive.
fn cli_eval_user_function(argv: &[String]) -> (i32, String) {
    let Some(contract_id_str) = argv.get(0) else {
        return (1, "Missing contract ID".into());
    };
    let Some(code_path_or_stdin) = argv.get(1) else {
        return (1, "Missing code".into());
    };
    let Some(user_function) = argv.get(2) else {
        return (1, "Missing user function".into())
    };
    let Ok(contract_id) = QualifiedContractIdentifier::parse(&contract_id_str) else {
        return (1, format!("Failed to parse {contract_id_str}"));
    };
    let src = match cli::load_from_file_or_stdin(code_path_or_stdin) {
        Ok(s) => match str::from_utf8(&s) {
            Ok(src) => {
                debug!("Loaded {}-byte source code from {}", src.len(), &code_path_or_stdin);
                src.to_string()
            }
            Err(_) => {
                return (1, format!("Code is not UTF-8"));
            }
        }
        Err(e) => {
            return (1, format!("Failed to load source code from {code_path_or_stdin}: {e:?}"));
        }
    };
   
    let mut remaining_args = argv.to_vec();

    let tx_sender_res = cli::consume_arg(&mut remaining_args, &["--tx-sender", "--tx_sender", "-t"], true);
    let contract_caller_res = cli::consume_arg(&mut remaining_args, &["--contract-caller", "--contract_caller", "-c"], true);
    let tx_sponsor_res = cli::consume_arg(&mut remaining_args, &["--tx-sponsor", "--tx_sponsor", "-s"], true);
    let contract_tx_sponsor_res = cli::consume_arg(&mut remaining_args, &["--contract-tx-sponsor", "--contract_tx_sponsor", "-c"], true);
    let Ok(full_explore_opt) = cli::consume_arg(&mut remaining_args, &["--full", "-f"], false) else {
        return (1, format!("Could not parse --full"));
    };

    let Ok(no_explore_opt) = cli::consume_arg(&mut remaining_args, &["--no-explore-functions"], false) else {
        return (1, format!("Could not parse --no-explore-functions"));
    };

    let mut skip_functions = vec![];
    while let Ok(Some(func_name_s)) = cli::consume_arg(&mut remaining_args, &["--skip-function"], true) {
        let Ok(name) = ClarityName::try_from(func_name_s.clone()) else {
            return (1, format!("Invalid function name '{func_name_s}'"));
        };
        skip_functions.push(name);
    }

    let tx_sender = match tx_sender_res {
        Ok(Some(tx_sender_s)) => {
            let Ok(tx_sender) = PrincipalData::parse_standard_principal(&tx_sender_s) else {
                return (1, format!("Failed to parse tx-sender {tx_sender_s}"));
            };
            Some(tx_sender)
        }
        Ok(None) => {
            None
        }
        Err(e_str) => {
            return (1, e_str);
        }
    };
    debug!("tx-sender is {tx_sender:?}");

    let tx_sponsor = match tx_sponsor_res {
        Ok(Some(tx_sponsor_s)) => {
            let Ok(tx_sponsor) = PrincipalData::parse_standard_principal(&tx_sponsor_s) else {
                return (1, format!("Failed to parse tx-sponsor {tx_sponsor_s}"));
            };
            Some(tx_sponsor)
        },
        Ok(None) => {
            None
        }
        Err(e_str) => {
            return (1, e_str);
        }
    };
    if let Some(ts) = &tx_sponsor {
        debug!("tx-sponsor is {ts:?}");
    }
    else {
        debug!("tx-sponsor is none");
    }
    
    let contract_tx_sponsor = match contract_tx_sponsor_res {
        Ok(Some(contract_tx_sponsor_s)) => {
            let Ok(contract_tx_sponsor) = PrincipalData::parse_standard_principal(&contract_tx_sponsor_s) else {
                return (1, format!("Failed to parse contract tx-sponsor {contract_tx_sponsor_s}"));
            };
            Some(contract_tx_sponsor)
        },
        Ok(None) => {
            None
        }
        Err(e_str) => {
            return (1, e_str);
        }
    };
    if let Some(ts) = &contract_tx_sponsor {
        debug!("contract tx-sponsor is {ts:?}");
    }
    else {
        debug!("contract tx-sponsor is none");
    }

    let contract_caller = match contract_caller_res {
        Ok(Some(contract_caller_s)) => {
            let Ok(contract_caller) = PrincipalData::parse(&contract_caller_s) else {
                return (1, format!("Failed to parse contract-caller {contract_caller_s}"));
            };
            Some(contract_caller)
        }
        Ok(None) => {
            None
        }
        Err(e_str) => {
            return (1, e_str);
        }
    };
    debug!("contrat-caller is {contract_caller:?}");

    let continuations = match exec_user_function(contract_id, &src, user_function, tx_sender, contract_caller, tx_sponsor, contract_tx_sponsor, no_explore_opt.is_some(), skip_functions, full_explore_opt.is_some()) {
        Ok(c) => c,
        Err(e) => {
            return (2, format!("Failed to evaluate user function {user_function} loaded from {code_path_or_stdin}: {e:?}"));
        }
    };

    let mut sbuf = "".to_string();
    for cont in continuations.into_iter() {
        sbuf.push_str(">>>>>>>>>>>>>>>>>>>> Terminating state:\n");
        sbuf.push_str(&format!("{}\n", &cont));
        let trace = cont.trace();
        sbuf.push_str(&format!("Stack trace:\n{}", &trace));
    }

    (0, sbuf)
}

fn cli_reachability_graph(argv: &[String]) -> (i32, String) {
    let Some(code_path_or_stdin) = argv.get(0) else {
        return (1, "Missing code".into());
    };
    let Some(user_function) = argv.get(1) else {
        return (1, "Missing user function".into())
    };
    let src = match cli::load_from_file_or_stdin(code_path_or_stdin) {
        Ok(s) => match str::from_utf8(&s) {
            Ok(src) => {
                debug!("Loaded {}-byte source code from {}", src.len(), &code_path_or_stdin);
                src.to_string()
            }
            Err(_) => {
                return (1, format!("Code is not UTF-8"));
            }
        }
        Err(e) => {
            return (1, format!("Failed to load source code from {code_path_or_stdin}: {e:?}"));
        }
    };

    let (callgraph, user_function) = match cli_get_callgraph(&src, user_function) {
        Ok((cg, uf)) => (cg, uf),
        Err(e) => {
            return (2, format!("Failed to build callgraph for function {user_function}: {e:?}"));
        }
    };

    let Some(view) = callgraph.view(&user_function) else {
        return (1, format!("No such function: {user_function}"));
    };
    return (0, view.to_string());
}

pub fn run_cli_sym(argv: &mut Vec<String>) -> (i32, String) {
    if argv.len() == 0 {
        return (1, "Missing subcommand".into());
    }

    let subcommand = argv.remove(0);
    match subcommand.as_str() {
        "exec-func" => {
            cli_eval_user_function(&argv)
        }
        "reachable" => {
            cli_reachability_graph(&argv)
        }
        _ => {
            (1, format!("Unrecognized sym comand '{subcommand}'.  Try `sym help` for details"))
        }
    }
}
