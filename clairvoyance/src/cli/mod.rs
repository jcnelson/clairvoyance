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

use std::process;
use std::env;
use std::io::stdin;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::collections::{BTreeMap, HashMap};

use clarity_types::ClarityName;
use clarity_types::types::{PrincipalData, StandardPrincipalData, QualifiedContractIdentifier, TraitIdentifier};

pub mod ast;
pub mod sym;

use crate::core::Error;
use crate::sym::{Symbex, Continuation, FullName};
use crate::sym::command::Halt;
use crate::sym::Callgraph;

/// Consume a string and an optional argument (if `has_optarg` is true) from `args`.
/// `argnames` contains the list of argument names to search for
pub fn consume_arg(
    args: &mut Vec<String>,
    argnames: &[&str],
    has_optarg: bool,
) -> Result<Option<String>, String> {
    if let Some(ref switch) = args
        .iter()
        .find(|ref arg| argnames.iter().find(|ref argname| argname == arg).is_some())
    {
        let idx = args
            .iter()
            .position(|ref arg| arg == switch)
            .expect("BUG: did not find the thing that was just found");
        let argval = if has_optarg {
            // following argument is the argument value
            if idx + 1 < args.len() {
                Some(args[idx + 1].clone())
            } else {
                // invalid usage -- expected argument
                return Err("Expected argument".to_string());
            }
        } else {
            // only care about presence of this option
            Some("".to_string())
        };

        args.remove(idx);
        if has_optarg {
            // also clear the argument
            args.remove(idx);
        }
        Ok(argval)
    } else {
        // not found
        Ok(None)
    }
}

/// get data from stdin or a file
pub fn load_from_file_or_stdin(path: &str) -> Result<Vec<u8>, Error> {
    let data = if path == "-" {
        let mut fd = stdin();
        let mut bytes = vec![];
        fd.read_to_end(&mut bytes)
            .map_err(|e| {
                Error::Failed(format!("Failed to load from stdin: {e:?}"))
            })?;
        bytes
    } else {
        if let Err(e) = fs::metadata(path) {
            return Err(Error::Failed(format!("Failed to open '{path}': {e:?}")))
        }
        fs::read(path)
            .map_err(|e| {
                Error::Failed(format!("Failed to read from '{path}': {e:?}"))
            })?
    };
    Ok(data)
}

/// Load a standard principal from CLI args
pub fn load_standard_principal(remaining_args: &mut Vec<String>, arg_names: &[&str]) -> Result<Option<StandardPrincipalData>, (i32, String)> {
    let Some(principal) = load_principal(remaining_args, arg_names)? else {
        return Ok(None);
    };

    if let PrincipalData::Standard(data) = principal {
        Ok(Some(data))
    }
    else {
        Err((1, format!("Failed to parse principal {principal} as standard principal")))
    }
}

/// Load a contract principal from CLI args
pub fn load_contract_principal(remaining_args: &mut Vec<String>, arg_names: &[&str]) -> Result<Option<QualifiedContractIdentifier>, (i32, String)> {
    let Some(principal) = load_principal(remaining_args, arg_names)? else {
        return Ok(None);
    };

    if let PrincipalData::Contract(data) = principal {
        Ok(Some(data))
    }
    else {
        Err((1, format!("Failed to parse principal {principal} as contract principal")))
    }
}

/// Load a contract principal from CLI args
pub fn load_principal(remaining_args: &mut Vec<String>, arg_names: &[&str]) -> Result<Option<PrincipalData>, (i32, String)> {
    let principal_res = consume_arg(remaining_args, arg_names, true);
    let principal = match principal_res {
        Ok(Some(principal_s)) => {
            let Ok(principal) = PrincipalData::parse(&principal_s) else {
                return Err((1, format!("Failed to parse principal `{principal_s}`")));
            };
            Some(principal)
        }
        Ok(None) => {
            None
        }
        Err(e_str) => {
            return Err((1, e_str));
        }
    };
    trace!("Loaded {principal:?} from arguments {arg_names:?}");
    Ok(principal)
}

pub fn load_contract_id(remaining_args: &mut Vec<String>) -> Result<Option<QualifiedContractIdentifier>, (i32, String)> {
    load_contract_principal(remaining_args, &["--contract-id"])
}

pub fn load_tx_sender(remaining_args: &mut Vec<String>) -> Result<Option<StandardPrincipalData>, (i32, String)> {
    load_standard_principal(remaining_args, &["--tx-sender"])
}

pub fn load_tx_sponsor(remaining_args: &mut Vec<String>) -> Result<Option<StandardPrincipalData>, (i32, String)> {
    load_standard_principal(remaining_args, &["--tx-sponsor"])
}

pub fn load_contract_caller(remaining_args: &mut Vec<String>) -> Result<Option<PrincipalData>, (i32, String)> {
    load_principal(remaining_args, &["--contract-caller"])
}

pub fn load_contract_tx_sponsor(remaining_args: &mut Vec<String>) -> Result<Option<StandardPrincipalData>, (i32, String)> {
    load_standard_principal(remaining_args, &["--contract-tx-sponsor"])
}

/// Load the dependent contracts
/// format is `--dep CONTRACT_ID:/PATH/TO/CLARITY/CODE`
/// Contracts will be instantiated in the order given
pub fn load_deps(remaining_args: &mut Vec<String>) -> Result<Vec<(QualifiedContractIdentifier, String)>, (i32, String)> {
    let mut deps = vec![];
    loop {
        let contract_id_and_file = consume_arg(remaining_args, &["--dep", "-c"], true);
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
                let src = match load_from_file_or_stdin(src_file) {
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
pub fn load_concretized_traits(remaining_args: &mut Vec<String>) -> Result<HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>>, (i32, String)> {
    let mut concretized_traits : HashMap<FullName, HashMap<ClarityName, QualifiedContractIdentifier>> = HashMap::new();
    loop {
        let trait_binding = consume_arg(remaining_args, &["--concretized-trait"], true);
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
pub fn load_default_concretized_traits(remaining_args: &mut Vec<String>) -> Result<HashMap<TraitIdentifier, QualifiedContractIdentifier>, (i32, String)> {
    let mut default_traits : HashMap<TraitIdentifier, QualifiedContractIdentifier> = HashMap::new();
    loop {
        let trait_binding = consume_arg(remaining_args, &["--default-trait"], true);
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

pub fn usage(msg: &str, code: i32) {
    let args: Vec<_> = env::args().collect();
    if msg.len() > 0 {  
        eprintln!("{}", msg);
    }
    else {
        eprintln!("Usage: {} command [options]", &args[0]);
    }
    process::exit(code);
}

fn run_symbex_on_functions(mut symbex: Symbex, mut func_names: Vec<String>) -> Result<BTreeMap<String, Vec<Continuation>>, Error> {
    if func_names.len() == 0 {
        let contract_funcs = symbex.callgraph().get_contract_functions(&symbex.contract_context(&symbex.target_contract)?.contract_identifier);
        func_names.extend(contract_funcs.into_iter().map(|fname| fname.to_string()));
    }

    // TODO: only pre-evaluate reachable functions!
    let mut ret = BTreeMap::new();
    for func_name in func_names.iter() {
        let conts = symbex.eval_user_function(&func_name)?;
        ret.insert(func_name.clone(), conts);
    }
    Ok(ret)
}

fn explore(
    src: &str,
    function_names: Vec<String>,
    search_paths: Vec<String>,
) -> Result<BTreeMap<String, Vec<Continuation>>, Error> {
    let symbex = Symbex::from_contract_comments(src, search_paths)?
        .check_proofs(false)
        .init()?;

    run_symbex_on_functions(symbex, function_names)
}

fn check(src: &str, function_names: Vec<String>, search_paths: Vec<String>) -> Result<BTreeMap<String, Vec<Continuation>>, Error> {
    let symbex = Symbex::from_contract_comments(src, search_paths)?
        .check_proofs(true)
        .init()?;

    run_symbex_on_functions(symbex, function_names)
}


fn callgraph(src: &str, search_paths: Vec<String>, func_name: String) -> Result<(Callgraph, FullName), Error> {
    let (contract_id, mut symbex) = Symbex::from_contract_comments_ex(src, search_paths)?;
    symbex = symbex
        .check_proofs(false)
        .init()?;

    let fullname = FullName(contract_id, ClarityName::try_from(func_name).map_err(|_| Error::Invalid("Invalid function name {user_function}".into()))?);

    Ok((symbex.callgraph().clone(), fullname))
}


fn get_code_search_paths(code_path_or_stdin: String, argv: &mut Vec<String>) -> Result<Vec<String>, String> { 
    let mut search_paths = vec![];
    if code_path_or_stdin != "-" {
        let path = Path::new(&code_path_or_stdin);
        if let Some(parent) = path.parent() && let Some(parent_str) = parent.to_str() {
            search_paths.push(parent_str.to_string());
        }
    }

    while let Some(path) = consume_arg(argv, &["-I", "--include-dir"], true)? {
        search_paths.push(path);
    }
    Ok(search_paths)
}

fn cli_explore(argv: &mut Vec<String>) -> (i32, String) { 
    let verbose = match consume_arg(argv, &["-v", "--verbose"], false) {
        Ok(v) => v.is_some(),
        Err(s) => {
            return (1, s);
        }
    };

    let Some(code_path_or_stdin) = argv.get(0) else {
        return (1, "Missing code path".into());
    };

    let src = match load_from_file_or_stdin(code_path_or_stdin) {
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

    let mut func_names = vec![];
    for i in 1..argv.len() {
        func_names.push(argv[i].clone());
    }

    let search_paths = match get_code_search_paths(code_path_or_stdin.clone(), argv) {
        Ok(paths) => paths,
        Err(e) => {
            return (1, e);
        }
    };
    
    match explore(&src, func_names, search_paths) {
        Ok(conts) => {
            let mut sbuf = "".to_string();
            for (func_name, conts) in conts.into_iter() {
                for cont in conts.into_iter() {
                    if verbose {
                        sbuf.push_str(&format!("\n>>>>>>>>>>>>>>>>>>>> Terminating state for {func_name}:\n"));
                        sbuf.push_str(&format!("{}\n", &cont));
                        let trace = cont.trace();
                        sbuf.push_str(&format!("Symbolic stack trace:\n{}\n", &trace));
                    }

                    let halts = Halt::from(cont).to_comment_block();
                    sbuf.push_str(&format!("Halting description for {func_name}:\n{halts}\n\n"));
                }
            }
            return (0, sbuf);
        }
        Err(e) => {
            return (2, format!("Failed to explore contract: {e:?}"));
        }
    }
}


fn cli_check(argv: &mut Vec<String>) -> (i32, String) {
    let Some(code_path_or_stdin) = argv.get(0) else {
        return (1, "Missing code path".into());
    };

    let src = match load_from_file_or_stdin(code_path_or_stdin) {
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
    
    let mut func_names = vec![];
    for i in 1..argv.len() {
        func_names.push(argv[i].clone());
    }
    
    let search_paths = match get_code_search_paths(code_path_or_stdin.clone(), argv) {
        Ok(paths) => paths,
        Err(e) => {
            return (1, e);
        }
    };
    
    match check(&src, func_names, search_paths) {
        Ok(_conts) => {
            return (0, "checks passed".to_string())
        }
        Err(e) => {
            return (2, format!("Failed to check contract:\n{e}"));
        }
    }
}

fn cli_callgraph(argv: &mut Vec<String>) -> (i32, String) {
    let Some(code_path_or_stdin) = argv.get(0) else {
        return (1, "Missing code path".into());
    };

    let src = match load_from_file_or_stdin(code_path_or_stdin) {
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
    
    let mut func_name = None;
    for i in 1..argv.len() {
        func_name = Some(argv[i].clone());
        break;
    }
    let Some(func_name) = func_name.take() else {
        return (1, format!("Missing function name"));
    };
    
    let search_paths = match get_code_search_paths(code_path_or_stdin.clone(), argv) {
        Ok(paths) => paths,
        Err(e) => {
            return (1, e);
        }
    };

    let (callgraph, fullname) = match callgraph(&src, search_paths, func_name) {
        Ok(x) => x,
        Err(e) => {
            return (2, format!("Failed to compute callgraph:\n{e}"));
        }
    };

    let Some(view) = callgraph.view(&fullname) else {
        return (1, format!("No such function: {fullname}"));
    };
    return (0, view.to_string());
}

pub fn run_subcommand(argv: &mut Vec<String>) -> (i32, String) {
    if argv.len() == 0 {
        return (1, format!("Missing subcommand"));
    }

    let subcommand = argv.remove(0);
    match subcommand.as_str() {
        "contract" => {
            ast::run_cli_contract(argv)
        }
        "sym" => {
            sym::run_cli_sym(argv)
        }
        "callgraph" => {
            cli_callgraph(argv)
        }
        "explore" => {
            cli_explore(argv)
        }
        "check" => {
            cli_check(argv)
        }
        _ => {
            return (1, format!("Unrecognized subcommand '{subcommand}'"))
        }
    }
}
