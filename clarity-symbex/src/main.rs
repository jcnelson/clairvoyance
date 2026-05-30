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

#![allow(deprecated)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

#[macro_use]
extern crate stacks_common;

#[macro_use]
extern crate clarity;
extern crate clarity_types;

extern crate serde;
extern crate serde_json;

pub mod cli;
pub mod core;
pub mod sym;

#[cfg(test)]
pub mod tests;

use std::env;
use std::process;

fn main() {
    let mut argv : Vec<_> = std::env::args().collect();

    let _prog_name = argv.remove(0);
    let (exit_code, message) = cli::run_subcommand(&mut argv);
    if exit_code != 0 {
        eprintln!("{}", &message);
    }
    else {
        println!("{}", &message);
    }
    process::exit(exit_code);
}

