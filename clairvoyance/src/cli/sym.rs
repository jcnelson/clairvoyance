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
// (at your option) any later version.

use std::path::Path;

use std::collections::HashMap;
use std::collections::BTreeMap;
use std::collections::HashSet;

use clarity_types::types::{PrincipalData, StandardPrincipalData, QualifiedContractIdentifier, TraitIdentifier};
use clarity_types::ClarityName;

use crate::sym::Symbex;
use crate::sym::Continuation;
use crate::sym::Callgraph;
use crate::sym::FullName;
use crate::sym::command::Halt;
use crate::core::Error;
use crate::cli;
use crate::cli::{
    load_contract_id,
    load_tx_sender,
    load_tx_sponsor,
    load_contract_caller,
    load_contract_tx_sponsor
};
use stacks_common::address::C32_ADDRESS_VERSION_MAINNET_SINGLESIG;

fn exec_user_function(
    contract_id: QualifiedContractIdentifier,
    src: &str,
    user_function: &str,
    deps: &[(QualifiedContractIdentifier, String)],
    concretized_traits: HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>,
    default_concretized_traits: HashMap<TraitIdentifier, QualifiedContractIdentifier>,
    drop_early_returns: HashSet<FullName>,
    tx_sender: Option<StandardPrincipalData>,
    contract_caller: Option<PrincipalData>,
    tx_sponsor: Option<StandardPrincipalData>,
    contract_tx_sponsor: Option<StandardPrincipalData>,
    skip_functions: bool,
    skip_function_list: Vec<FullName>,
    explore_all: bool
) -> Result<Vec<Continuation>, Error> {
    let mut contracts : Vec<_> = deps 
        .iter()
        .map(|(contract_id, src)| {
            (
                contract_id.clone(),
                src.clone(),
                None
            )
        })
        .collect();

    contracts.push((contract_id, src.to_string(), contract_tx_sponsor));
    let target_contract_idx = contracts.len() - 1;

    let mut symbex = Symbex::from_contracts(contracts, target_contract_idx)?
        .with_tx_sender(tx_sender)
        .with_tx_sponsor(tx_sponsor)
        .with_contract_caller(contract_caller)
        .with_function_call_exploration(!skip_functions)
        .skip_pure(!explore_all)
        .skip_causally_independent(!explore_all);

    for (func_name, traits) in concretized_traits.iter() {
        for (var_name, contract_id) in traits.iter() {
            symbex = symbex
                .concretize_trait(func_name.clone(), var_name.clone(), contract_id.clone());
        }
    }

    for (trait_id, contract_id) in default_concretized_traits.iter() {
        symbex = symbex
            .default_trait(trait_id.clone(), contract_id.clone());
    }

    for func_name in drop_early_returns.into_iter() {
        symbex = symbex
            .drop_early_return(func_name);
    }

    for name in skip_function_list.into_iter() {
        symbex = symbex
            .with_skipped_function_call(name);
    }

    trace!("Symbolic execution begins on function '{user_function}'");
    symbex.eval_user_function(user_function)
}

fn cli_get_callgraph(
    contract_id: QualifiedContractIdentifier,
    src: &str,
    user_function: &str,
    deps: &[(QualifiedContractIdentifier, String)],
    concretized_traits: HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>,
    default_concretized_traits: HashMap<TraitIdentifier, QualifiedContractIdentifier>,
) -> Result<(Callgraph, FullName), Error> {
    let mut contracts : Vec<_> = deps
        .iter()
        .map(|(contract_id, src)| {
            (
                contract_id.clone(),
                src.clone(),
                None
            )
        })
        .collect();

    contracts.push((contract_id.clone(), src.to_string(), None));
    let target_contract_idx = contracts.len() - 1;

    let mut symbex = Symbex::from_contracts(contracts, target_contract_idx)?;
    for (func_name, traits) in concretized_traits.iter() {
        for (var_name, contract_id) in traits.iter() {
            symbex = symbex
                .concretize_trait(func_name.clone(), var_name.clone(), contract_id.clone());
        }
    }

    for (trait_id, contract_id) in default_concretized_traits.iter() {
        symbex = symbex
            .default_trait(trait_id.clone(), contract_id.clone());
    }
    symbex = symbex.init()?;

    Ok((
        symbex.callgraph().clone(),
        FullName(contract_id, ClarityName::try_from(user_function).map_err(|_| Error::Invalid("Invalid function name {user_function}".into()))?)
    ))
}

/// Load the dependent contracts
/// format is `--dep CONTRACT_ID:/PATH/TO/CLARITY/CODE`
/// Contracts will be instantiated in the order given
fn load_deps(remaining_args: &mut Vec<String>) -> Result<Vec<(QualifiedContractIdentifier, String)>, (i32, String)> {
    let mut deps = vec![];
    loop {
        let contract_id_and_file = cli::consume_arg(remaining_args, &["--dep", "-c"], true);
        let (contract_id, src) = match contract_id_and_file {
            Ok(Some(contract_id_and_file)) => {
                let mut parts = contract_id_and_file.split(":");
                let Some(contract_id) = parts.next() else {
                    return Err((1, format!("dependency '{contract_id_and_file}' missing ':' delimiter")));
                };
                let Some(src_file) = parts.next() else {
                    return Err((1, format!("dependency '{contract_id_and_file}' missing source file")));
                };
                let Ok(contract_id) = QualifiedContractIdentifier::parse(&contract_id) else {
                    return Err((1, format!("Invalid dependency contract ID '{contract_id}'")));
                };
                let src = match cli::load_from_file_or_stdin(src_file) {
                    Ok(s) => match str::from_utf8(&s) {
                        Ok(src) => {
                            trace!("Loaded {}-byte source code from {}", src.len(), &src_file);
                            src.to_string()
                        }
                        Err(_) => {
                            return Err((1, format!("Dependency code in '{src_file}' is not UTF-8")));
                        }
                    }
                    Err(e) => {
                        return Err((1, format!("Failed to load source code from {src_file}: {e:?}")));
                    }
                };
                (contract_id, src)
            },
            Ok(None) => {
                break;
            }
            Err(e_str) => {
                return Err((1, e_str));
            }
        };
        trace!("Dependency: {contract_id}");
        deps.push((contract_id, src));
    }
    Ok(deps)
}

/// Load concretized traits
/// format is `--concretized-trait CONTRACT_ID.FUNCTION_NAME.VARIABLE_NAME:TRAIT_IMPL_CONTRACT_ID
fn load_concretized_traits(remaining_args: &mut Vec<String>) -> Result<HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>, (i32, String)> {
    let mut concretized_traits : HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>> = HashMap::new();
    loop {
        let trait_binding = cli::consume_arg(remaining_args, &["--concretized-trait"], true);
        match trait_binding {
            Ok(Some(trait_binding)) => {
                let mut parts = trait_binding.split(":");
                let Some(fq_var_name) = parts.next() else {
                    return Err((1, format!("Failed to parse fully-qualified variable name from {trait_binding}")));
                };
                let Some(impl_contract_id) = parts.next() else {
                    return Err((1, format!("Failed to parse trait implementation contract from {trait_binding}")));
                };
                if parts.next().is_some() {
                    return Err((1, format!("Invalid value {trait_binding}: too many `:` separators")));
                };

                let Ok(impl_contract_id) = QualifiedContractIdentifier::parse(&impl_contract_id) else {
                    return Err((1, format!("Invalid contract ID {impl_contract_id}")));
                };

                // parse contract, function, variable
                let mut parts = fq_var_name.split(".");
                let Some(contract_address_str) = parts.next() else {
                    return Err((1, format!("Missing contract address in {fq_var_name}")));
                };
                let Some(contract_name_str) = parts.next() else {
                    return Err((1, format!("Missing contract name in {fq_var_name}")));
                };
                let Some(func_name_str) = parts.next() else {
                    return Err((1, format!("Missing function name in {fq_var_name}")));
                };
                let Some(var_name_str) = parts.next() else {
                    return Err((1, format!("Missing var name in {fq_var_name}")));
                };

                let Ok(contract_id) = QualifiedContractIdentifier::parse(&format!("{}.{}", contract_address_str, contract_name_str)) else {
                    return Err((1, format!("Could not parse `{contract_address_str}.{contract_name_str}`")));
                };
                let Ok(func_name) = ClarityName::try_from(func_name_str) else {
                    return Err((1, format!("Could not parse `{func_name_str}` -- invalid Clarity name")));
                };
                let fq_name = FullName(contract_id, func_name);
                let Ok(var_name) = ClarityName::try_from(var_name_str) else {
                    return Err((1, format!("Could not parse `{var_name_str}` -- invalid Clarity name")));
                };

                if let Some(traits) = concretized_traits.get_mut(&fq_name) {
                    traits.insert(var_name, impl_contract_id);
                }
                else {
                    let mut traits = HashMap::new();
                    traits.insert(var_name, impl_contract_id);
                    concretized_traits.insert(fq_name, traits);
                }
            }
            Ok(None) => {
                break;
            }
            Err(e_str) => {
                return Err((1, e_str));
            }
        }
    }
    Ok(concretized_traits)
}

/// Load default concretized traits
/// format is `--default-trait TRAIT_ID:TRAIT_IMPL_CONTRACT_ID`
fn load_default_concretized_traits(remaining_args: &mut Vec<String>) -> Result<HashMap<TraitIdentifier, QualifiedContractIdentifier>, (i32, String)> {
    let mut default_traits : HashMap<TraitIdentifier, QualifiedContractIdentifier> = HashMap::new();
    loop {
        let trait_binding = cli::consume_arg(remaining_args, &["--default-trait"], true);
        match trait_binding {
            Ok(Some(trait_binding)) => {
                let mut parts = trait_binding.split(":");
                let Some(trait_id_str) = parts.next() else {
                    return Err((1, format!("Failed to parse `{trait_binding}`")));
                };
                let Some(impl_contract_id) = parts.next() else {
                    return Err((1, format!("Missing contract name in `{trait_binding}`")));
                };

                let Ok(trait_id) = TraitIdentifier::parse_fully_qualified(trait_id_str) else {
                    return Err((1, format!("Failed to parse `{trait_id_str}`")));
                };
                let Ok(impl_contract_id) = QualifiedContractIdentifier::parse(&impl_contract_id) else {
                    return Err((1, format!("Invalid contract ID `{impl_contract_id}`")));
                };

                default_traits.insert(trait_id, impl_contract_id);
            }
            Ok(None) => {
                break;
            }
            Err(e_str) => {
                return Err((1, e_str));
            }
        }
    }
    Ok(default_traits)
}

/// Load the list of functions whose early-return continuations will not be explored
fn load_drop_early_returns(remaining_args: &mut Vec<String>) -> Result<HashSet<FullName>, (i32, String)> {
    let mut drop_early_returns : HashSet<FullName> = HashSet::new();
    loop {
        let early_return = cli::consume_arg(remaining_args, &["--drop-early-returns", "--drop-early-return"], true);
        match early_return {
            Ok(Some(func_name_s)) => {
                let Ok(func_name) = FullName::try_from(func_name_s.as_str()) else {
                    return Err((1, format!("Failed to parse full function name `{func_name_s}`")));
                };
                drop_early_returns.insert(func_name);
            }
            Ok(None) => {
                break;
            }
            Err(e_str) => {
                return Err((1, e_str));
            }
        }
    }
    Ok(drop_early_returns)
}


/// NOTE: This prints out continuations as they arrive.
fn cli_eval_user_function(argv: &[String]) -> (i32, String) {
    let mut remaining_args = argv.to_vec();

    let tx_sender = match load_tx_sender(&mut remaining_args) {
        Ok(p) => p,
        Err(x) => {
            return x;
        }
    };

    let tx_sponsor = match load_tx_sponsor(&mut remaining_args) {
        Ok(p) => p,
        Err(x) => {
            return x;
        }
    };
    
    let contract_caller = match load_contract_caller(&mut remaining_args) {
        Ok(p) => p,
        Err(x) => {
            return x;
        }
    };
    
    let contract_tx_sponsor = match load_contract_tx_sponsor(&mut remaining_args) {
        Ok(p) => p,
        Err(x) => {
            return x;
        }
    };

    let Ok(full_explore_opt) = cli::consume_arg(&mut remaining_args, &["--full", "-f"], false) else {
        return (1, format!("Could not parse --full"));
    };

    let Ok(no_explore_opt) = cli::consume_arg(&mut remaining_args, &["--no-explore-functions"], false) else {
        return (1, format!("Could not parse --no-explore-functions"));
    };

    let mut skip_functions = vec![];
    while let Ok(Some(fq_func_name_s)) = cli::consume_arg(&mut remaining_args, &["--skip-function"], true) {
        let Ok(name) = FullName::try_from(&fq_func_name_s) else {
            return (1, format!("Invalid function name '{fq_func_name_s}'"));
        };
        skip_functions.push(name);
    }

    let deps = match load_deps(&mut remaining_args) {
        Ok(deps) => deps,
        Err(x) => {
            return x;
        }
    };

    let concretized_traits = match load_concretized_traits(&mut remaining_args) {
        Ok(concretized_traits) => concretized_traits,
        Err(x) => {
            return x;
        }
    };

    let default_concretized_traits = match load_default_concretized_traits(&mut remaining_args) {
        Ok(concretized_traits) => concretized_traits,
        Err(x) => {
            return x;
        }
    };

    let drop_early_returns = match load_drop_early_returns(&mut remaining_args) {
        Ok(early_returns) => early_returns,
        Err(x) => {
            return x;
        }
    };
    
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
        return (1, format!("Failed to parse contract ID {contract_id_str}"));
    };
    let src = match cli::load_from_file_or_stdin(code_path_or_stdin) {
        Ok(s) => match str::from_utf8(&s) {
            Ok(src) => {
                trace!("Loaded {}-byte source code from {}", src.len(), &code_path_or_stdin);
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
    

    let continuations = match exec_user_function(
        contract_id,
        &src,
        user_function,
        &deps,
        concretized_traits,
        default_concretized_traits,
        drop_early_returns,
        tx_sender,
        contract_caller,
        tx_sponsor,
        contract_tx_sponsor,
        no_explore_opt.is_some(),
        skip_functions,
        full_explore_opt.is_some()
    ) {
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
        return (1, format!("Failed to parse contract ID {contract_id_str}"));
    };
    let src = match cli::load_from_file_or_stdin(code_path_or_stdin) {
        Ok(s) => match str::from_utf8(&s) {
            Ok(src) => {
                trace!("Loaded {}-byte source code from {}", src.len(), &code_path_or_stdin);
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

    let deps = match load_deps(&mut remaining_args) {
        Ok(deps) => deps,
        Err(x) => {
            return x;
        }
    };

    let concretized_traits = match load_concretized_traits(&mut remaining_args) {
        Ok(concretized_traits) => concretized_traits,
        Err(x) => {
            return x;
        }
    };

    let default_concretized_traits = match load_default_concretized_traits(&mut remaining_args) {
        Ok(concretized_traits) => concretized_traits,
        Err(x) => {
            return x;
        }
    };

    let (callgraph, user_function) = match cli_get_callgraph(contract_id, &src, user_function, &deps, concretized_traits, default_concretized_traits) {
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
