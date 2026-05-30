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

pub mod ast;

use crate::core::Error;

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

pub fn run_subcommand(argv: &mut Vec<String>) -> (i32, String) {
    if argv.len() == 0 {
        return (1, format!("Missing subcommand"));
    }

    let subcommand = argv.remove(0);
    match subcommand.as_str() {
        "contract" => {
            ast::run_cli_contract(argv)
        }
        _ => {
            return (1, format!("Unrecognized subcommand '{subcommand}'"))
        }
    }
}
