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

use std::fs;

use crate::sym::Symbex;

use crate::sym::command::{Command, CommandContext};
use crate::core::BackingStore;
use crate::core::Error;
use crate::core::ast;
use crate::tests::default_contract_id;

use clarity_types::types::QualifiedContractIdentifier;
use clarity_types::types::StandardPrincipalData;
use clarity_types::types::PrincipalData;
use clarity_types::types::signatures::{TypeSignature as TS};

use crate::tests::*;

#[test]
fn test_extract_command_programs() {
    let tests = vec![
        (
            "this is a normal comment",
            vec![]
        ),
        (
            "(@clairvoyance (test \"this is a program\"))",
            vec!["( test \"this is a program\" )"],
        ),
        (
            "this is a normal comment (@clairvoyance (test \"with a program\")) and a trailer",
            vec!["( test \"with a program\" )"]
        ),
        (
            "(@clairvoyance )",
            vec![]
        ),
        (
            "(@clairvoy-this-is-a-normal-comment)",
            vec![]
        ),
        (
            "(this is a normal comment (@clairvoyance (test \"and this is a program\")))",
            vec!["( test \"and this is a program\" )"],
        ),
        (
            "(@clairvoyance (test \"can nest (@clairvoyance (test \"programs and quotes\"))\")) and have trailers",
            vec!["( test \"can nest (@clairvoyance (test \"programs and quotes\"))\" )"]
        ),
        (
            r#"
            (@clairvoyance (test "drop end-of-file comments")) ;; this is a comment
            "#,
            vec!["( test \"drop end-of-file comments\" )"]
        ),
        (
            r#"
            (@clairvoyance
                (test "drop end-of-line comments") ;; this is a comment
            )"#,
            vec!["( test \"drop end-of-line comments\" )"]
        ),
        (
            r#"
            ;; this is a comment
            (@clairvoyance (test "comments do not break end-of-program) ;; )
            ")) ;; this is a comment
            ;; this is a comment
            "#,
            vec!["( test \"comments do not break end-of-program) ;; )\n            \" )"]
        ), 
        (
            r#"
            (@clairvoyance
                (test
                    ;; this is a comment!
                    "can nest comments"))
            "#,
            vec!["( test \"can nest comments\" )"]
        ),
        (
            r#"
            ((((((((@clairvoyance (test "this is processed"))
            "#,
            vec!["( test \"this is processed\" )"],
        ),
        (
            r#"
            " (@clairvoyance (test "this is processed"))
            "#,
            vec!["( test \"this is processed\" )"],
        ),
        (
            // comments are only ignored _within_ (@clairvoyance ..) s-exps
            r#"
            ;; (@clairvoyance (test "this is processed"))
            "#,
            vec!["( test \"this is processed\" )"],
        ),
    ];

    for (inp, out) in tests.into_iter() {
        let out : Vec<_> = out.into_iter().map(|s| s.to_string()).collect();
        let progs = CommandContext::extract_command_programs(&inp);
        assert_eq!(out, progs, "Failed to parse `{inp}`");
    }
}

#[test]
fn test_eval_program() {
    let tests : Vec<(&str, Result<Vec<Command>, &str>)> = vec![
        (
            r#"(test "hello world!")"#,
            Ok(vec![Command::Test("\"hello world!\"".to_string())]),
        ),
        (
            r#"
                (test "foo")
                (test "bar")
            "#,
            Ok(vec![
               Command::Test("\"foo\"".to_string()),
               Command::Test("\"bar\"".to_string()),
            ])
        ),
        (
            r#"
                (test u1)
                (test true)
                (test tx-sender)
            "#,
            Ok(vec![
               Command::Test("u1".to_string()),
               Command::Test("true".to_string()),
               Command::Test("(tx-sender principal)".to_string()),
            ]),
        ),
        (
            r#"
                (halt
                    (result (ok (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (modulus uint))))
                    (condition (is-eq (len (items (list 5 uint))) u0)))
            "#,
            Ok(vec![
                Halt::new(
                   *ok(fq_map_get(&QualifiedContractIdentifier::parse("SP8H248H248H248H248H248H248H248H24ARTQ82.contract").unwrap(), "m", vu("modulus"))),
                   eq(llen(vl("items", TS::UIntType, 5)), cu(0)).try_as_predicate().unwrap()
                ).into()
            ])
        ),
        (
            r#"(test "force-failure!")"#,
            Err("`test` command forced to fail"),
        )
    ];

    let mut ctx = CommandContext::new();
    for (prog, expected_events) in tests.into_iter() {
        match ctx.eval_program(&prog, 0, None) {
            Ok(events) => {
                let Ok(expected_events) = expected_events else {
                    panic!("Evaluating program `{prog}` was supposed to fail (got Ok event `{events:?}`)");
                };
                assert_eq!(events, expected_events, "Failed to run program {prog}");
            }
            Err(Error::Program(program_error)) => {
                let msg = &program_error.cause;
                let Err(expected_msg) = expected_events else {
                    panic!("Evaluating program `{prog}` was not supposed to fail (got msg `{msg}`)");
                };
                assert!(msg.find(expected_msg).is_some(), "Failed to find expected message `{expected_msg}` in `{msg}`");
            }
            Err(e) => {
                panic!("Unexpected error: `{e:?}`");
            }
        }
    }
}

#[test]
fn test_symop_from_symbolic_expression() {
    let contract_id = QualifiedContractIdentifier::parse("SP8H248H248H248H248H248H248H248H24ARTQ82.foo").unwrap();

    let tests : Vec<(&str, Result<SymOp, Error>)> = vec![
        (
            "true",
            Ok(*t()),
        ),
        (
            "u0",
            Ok(*cu(0)),
        ),
        (
            "0",
            Ok(*ci(0)),
        ),
        (
            "(list u5)",
            Ok(*lcons(vec![cu(5)])),
        ),
        (
            "(tuple (x u3))",
            Ok(*tcons(vec![("x", cu(3))])),
        ),
        (
            "{ y: u4 }",
            Ok(*tcons(vec![("y", cu(4))])),
        ),
        (
            "'SP8H248H248H248H248H248H248H248H24ARTQ82",
            Ok(*cp(PrincipalData::parse("SP8H248H248H248H248H248H248H248H24ARTQ82").unwrap())),
        ),
        (
            "'SP8H248H248H248H248H248H248H248H24ARTQ82.foo",
            Ok(*cp(PrincipalData::parse("SP8H248H248H248H248H248H248H248H24ARTQ82.foo").unwrap())),
        ),
        (
            "(ok true)",
            Ok(*ok(cb(true))),
        ),
        (
            "(err false)",
            Ok(*err(cb(false))),
        ),
        (
            "(some true)",
            Ok(*some(cb(true))),
        ),
        (
            "0x112233",
            Ok(*csb(vec![0x11, 0x22, 0x33])),
        ),
        (
            "\"hello world\"",
            Ok(*cssa("hello world")),
        ),
        (
            "u\"hello world\"",
            Ok(*cssu("hello world")),
        ),
        (
            "(x uint)",
            Ok(*vu("x")),
        ),
        (
            "(x int)",
            Ok(*vi("x")),
        ),
        (
            "(x bool)",
            Ok(*vb("x")),
        ),
        (
            "(x (optional uint))",
            Ok(*vo("x", TS::UIntType)),
        ),
        (
            "(loaded-var 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.x (x uint))",
            Ok(*fqlv(&contract_id, "x", vu("x"))),
        ),
        (
            "(loaded-var-const 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.x u1)",
            Ok(*fqlv(&contract_id, "x", cu(1))),
        ),
        (
            "(loaded-var-type 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.x uint)",
            Ok(*fqlv(&contract_id, "x", vu("x"))),
        ),
        (
            "(loaded-var-sym 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.x (x uint))",
            Ok(*fqlv(&contract_id, "x", vu("x"))),
        ),
        (
            "(+ (x uint) (y uint) (z uint))",
            Ok(*add(vec![vu("x"), vu("y"), vu("z")])),
        ),
        (
            "(- (x uint) (y uint) (z uint))",
            Ok(*sub(vec![vu("x"), vu("y"), vu("z")])),
        ),
        (
            "(* (x uint) (y uint) (z uint))",
            Ok(*mul(vec![vu("x"), vu("y"), vu("z")])),
        ),
        (
            "(/ (x uint) (y uint) (z uint))",
            Ok(*div(vec![vu("x"), vu("y"), vu("z")])),
        ),
        (
            "(mod (x uint) (y uint))",
            Ok(*rem(vu("x"), vu("y"))),
        ),
        (
            "(and (x bool) (y bool) (z bool))",
            Ok(*and(vec![vb("x"), vb("y"), vb("z")])),
        ),
        (
            "(or (x bool) (y bool) (z bool))",
            Ok(*or(vec![vb("x"), vb("y"), vb("z")])),
        ),
        (
            "(map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.m (x uint))",
            Ok(*fq_map_get(&contract_id, "m", vu("x"))),
        ),
        (
            "(map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.m (x uint) (y bool))",
            Ok(*fqlm(&contract_id, "m", vu("x"), vb("y"))),
        ),
        (
            "(map-entry-const 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.m (x uint) true)",
            Ok(*fqlm(&contract_id, "m", vu("x"), cb(true))),
        ),
        (
            "(map-entry-type 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.m (x uint) (y bool) bool)",
            Ok(*fqlm(&contract_id, "m", vu("x"), vb("y"))),
        ),
        (
            "(map-entry-sym 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.m (x uint))",
            Ok(*fq_map_get(&contract_id, "m", vu("x"))),
        ),
        (
            "(map-entry-sym 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.m (x uint) (y bool))",
            Ok(*fqlm(&contract_id, "m", vu("x"), vb("y"))),
        ),
    ];

    for (prog, expected_symop_res) in tests.into_iter() {
        let ast = ast::parse_ast(&contract_id, prog).unwrap();
        match SymOp::try_from(&ast.expressions[0]) {
            Ok(symop) => {
                let Ok(expected_symop) = expected_symop_res else {
                    panic!("Evaluating program `{prog}` was supposed to fail (got `{expected_symop_res:?}`)");
                };
                assert_eq!(symop, expected_symop, "Failed to run program {prog}");
            }
            Err(Error::Program(program_error)) => {
                let msg = &program_error.cause;
                let Err(Error::Program(expected_program_error)) = expected_symop_res else {
                    panic!("Evaluating program `{prog}` was not supposed to fail (got msg `{msg}`)");
                };
                let expected_msg = &expected_program_error.cause;
                assert!(msg.find(expected_msg).is_some(), "Failed to find expected message `{expected_msg}` in `{msg}`");
            }
            Err(e) => {
                panic!("Unexpected error: `{e:?}`");
            }
        }
    }
} 

#[test]
fn test_command_halt_pass() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map m uint uint)

        ;; (@clairvoyance
        ;;      (halt
        ;;          (result (ok false))
        ;;          (condition
        ;;              (and
        ;;                  (is-eq (mod (x uint) u2) u0)
        ;;                  (is-some (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint))))))
        ;;
        ;;      (halt
        ;;          (result (ok true))
        ;;          (condition
        ;;              (and
        ;;                  (is-eq (mod (x uint) u2) u0)
        ;;                  (is-none (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint)))))
        ;;          (map-write
        ;;              'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m
        ;;              (x uint)
        ;;              (x uint)))
        ;;
        ;;      (halt
        ;;          (result (err u0))
        ;;          (condition
        ;;              (not (is-eq (mod (x uint) u2) u0)))))
        ;;
        (define-public (set-if-odd (x uint))
            (if (is-eq (mod x u2) u0)
                (ok (map-insert m x x))
                (err u0)))
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let termination_states = match symbex.eval_user_function("set-if-odd") {
        Ok(ts) => ts,
        Err(e) => {
            error!("symbex.eval_user_function: {e}");
            panic!()
        }
    };
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_command_halt_syntax_error() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map m uint uint)

        ;; (@clairvoyance
        ;;      (halt
        ;;          (result (ok false))
        ;;          (condition
        ;;              (and
        ;;                  (is-eq (mod (x uint) u2) u0)
        ;;                  (is-some (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint))))))
        ;;
        ;;      (halt
        ;;          (result (ok true))
        ;;          (condition
        ;;              (and
        ;;                  (is-eq (mod (x uint) u2) u0)
        ;;                  (is-none (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint)))))
        ;;          (map-write
        ;;              'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m
        ;;              (x uint)
        ;;              (x uint)))
        ;;
        ;;      (halt
        ;;          (result (err u0))
        ;;          (condition
        ;;              ;; oops
        ;;              (not (is-eq (mod (x uint)) u2)))))
        ;;
        (define-public (set-if-odd (x uint))
            (if (is-eq (mod x u2) u0)
                (ok (map-insert m x x))
                (err u0)))
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    match symbex.eval_user_function("set-if-odd") {
        Ok(termination_states) => {
            for t in termination_states.iter() {
                info!("{}", t.trace());
                info!("termination state: ==================================\n{}\n", &t.clone().rollup());
            }
            panic!("Did not encounter expected clairvoyance program syntax error");
        }
        Err(Error::Program(program_error)) => {
            info!("Program error:\n{program_error}\n");
            assert!(program_error.cause.find("has unexpected length 1 (expected at least 2)").is_some());
        }
        Err(e) => {
            error!("Unexpected error: {e:?}");
            panic!();
        }
    };
}

#[test]
fn test_command_halt_unchecked_continuation() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map m uint uint)

        ;; (@clairvoyance
        ;;      (halt
        ;;          (result (ok false))
        ;;          (condition (and
        ;;              (is-eq (mod (x uint) u2) u0)
        ;;              (is-some (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint))))))
        ;;
        ;;      (halt
        ;;          (result (err u0))
        ;;          (condition (not (is-eq (mod (x uint) u2) u0)))))
        (define-public (set-if-odd (x uint))
            (if (is-eq (mod x u2) u0)
                (ok (map-insert m x x))
                (err u0)))
        "#,
    )
    .unwrap()
    .init()
    .unwrap();
    
    match symbex.eval_user_function("set-if-odd") {
        Ok(termination_states) => {
            for t in termination_states.iter() {
                info!("{}", t.trace());
                info!("termination state: ==================================\n{}\n", &t.clone().rollup());
            }
            panic!("Did not encounter expected clairvoyance proof failure error");
        }
        Err(Error::ProofFailure(proof_failure)) => {
            info!("proof failure:\n{proof_failure}\n");
            assert_eq!(proof_failure.unchecked_continuations.len(), 1);
            assert_eq!(proof_failure.unmatched_halting_conditions.len(), 0);
        }
        Err(e) => {
            error!("Unexpected error: {e:?}");
            panic!();
        }
    }
}

#[test]
fn test_command_halt_unmatched_halt() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map m uint uint)

        ;; (@clairvoyance
        ;;      (halt
        ;;          (result (ok false))
        ;;          (condition (and
        ;;              (is-eq (mod (x uint) u2) u0)
        ;;              (is-some (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint))))))
        ;;
        ;;      (halt
        ;;          (result (ok true))
        ;;          (condition
        ;;              (and
        ;;                  (is-eq (mod (x uint) u2) u0)
        ;;                  (is-none (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint)))))
        ;;          (map-write
        ;;              'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m
        ;;              (x uint)
        ;;              (x uint)))
        ;;
        ;;      ;; oops
        ;;      (halt
        ;;          (result (err u1))
        ;;          (condition (is-eq (x uint) u3)))
        ;;
        ;;      (halt
        ;;          (result (err u0))
        ;;          (condition (not (is-eq (mod (x uint) u2) u0)))))
        (define-public (set-if-odd (x uint))
            (if (is-eq (mod x u2) u0)
                (ok (map-insert m x x))
                (err u0)))
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    match symbex.eval_user_function("set-if-odd") {
        Ok(termination_states) => {
            for t in termination_states.iter() {
                info!("{}", t.trace());
                info!("termination state: ==================================\n{}\n", &t.clone().rollup());
            }
            panic!("Did not encounter expected clairvoyance proof failure error");
        }
        Err(Error::ProofFailure(proof_failure)) => {
            info!("proof failure:\n{proof_failure}\n");
            assert_eq!(proof_failure.unchecked_continuations.len(), 0);
            assert_eq!(proof_failure.unmatched_halting_conditions.len(), 1);
        }
        Err(e) => {
            error!("Unexpected error: {e:?}");
            panic!();
        }
    }
}

#[test]
fn test_command_define_formula() {
    let contract_id = default_contract_id();
    let mut symbex = Symbex::from_contract(contract_id.clone(), r#"
        (define-map m uint uint)

        ;; (@clairvoyance
        ;;      (define-symbol x-is-even (is-eq (mod (x uint) u2) u0))
        ;;      (define-symbol x-is-odd (not (x-is-even bool)))
        ;;      (define-symbol map-get-x (map-entry 'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m (x uint)))
        ;;
        ;;      (halt
        ;;          (result (ok false))
        ;;          (condition (and
        ;;              (x-is-even bool)
        ;;              (is-some (map-get-x (optional uint))))))
        ;;
        ;;      (halt
        ;;          (result (ok true))
        ;;          (condition
        ;;              (and
        ;;                  (x-is-even bool)
        ;;                  (is-none (map-get-x (optional uint)))))
        ;;          (map-write
        ;;              'SP8H248H248H248H248H248H248H248H24ARTQ82.contract.m
        ;;              (x uint)
        ;;              (x uint)))
        ;;
        ;;      (halt
        ;;          (result (err u0))
        ;;          (condition (x-is-odd bool))))
        ;;
        (define-public (set-if-odd (x uint))
            (if (is-eq (mod x u2) u0)
                (ok (map-insert m x x))
                (err u0)))
        "#,
    )
    .unwrap()
    .init()
    .unwrap();

    let termination_states = match symbex.eval_user_function("set-if-odd") {
        Ok(ts) => ts,
        Err(e) => {
            error!("symbex.eval_user_function: {e}");
            panic!()
        }
    };
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }
}

#[test]
fn test_command_trait_contract_call() {
    let test_dir = "/tmp/clairvoyance-test/test_command_trait_contract_call/";
    let library_path = format!("{test_dir}/library.clar");
    let library_trait_path = format!("{test_dir}/library-trait.clar");

    if fs::metadata(&test_dir).is_ok() {
        fs::remove_dir_all(&test_dir).unwrap();
    }
    fs::create_dir_all(&test_dir).unwrap();
    fs::write(&library_trait_path, r#"
        (define-trait calc
            (
                (add (uint uint) (response uint uint))
            )
        )
    "#).unwrap();
    fs::write(&library_path, r#"
        (impl-trait .library-trait.calc)

        (define-public (add (x uint) (y uint))
            (ok (+ x y)))
    "#).unwrap();

    let mut symbex = Symbex::from_contract_comments(&format!("
    ;; (@clairvoyance
    ;;
    ;;      (contract-id 'SP8H248H248H248H248H248H248H248H24ARTQ82.client)
    ;;
    ;;      (dependency
    ;;          'SP8H248H248H248H248H248H248H248H24ARTQ82.library-trait
    ;;          \"{library_trait_path}\")
    ;;
    ;;      (dependency
    ;;          'SP8H248H248H248H248H248H248H248H24ARTQ82.library
    ;;          \"{library_path}\")
    ;; )
    
    (use-trait calc-trait .library-trait.calc)

    (define-constant OP_ADD u0)

    (define-constant ERR_NO_SUCH_OP u2000)

    ;; (@clairvoyance
    ;;
    ;;      (concretize-trait
    ;;          calc
    ;;          'SP8H248H248H248H248H248H248H248H24ARTQ82.library)
    ;;
    ;;      (halt
    ;;          (result (ok (+ (a uint) (b uint))))
    ;;          (condition (is-eq (op uint) u0)))
    ;;
    ;;      (halt
    ;;          (result (err u2000))
    ;;          (condition (not (is-eq (op uint) u0))))
    ;; )
    (define-public (compute (calc <calc-trait>) (op uint) (a uint) (b uint))
        (if (is-eq op OP_ADD)
            (contract-call? calc add a b)
            (err ERR_NO_SUCH_OP)))
    ", vec![]))
    .unwrap()
    .skip_causally_independent(false)
    .skip_pure(false) 
    .init()
    .unwrap();

    let termination_states = symbex.eval_user_function("compute").unwrap();
    for t in termination_states.iter() {
        info!("{}", t.trace());
        info!("termination state: ==================================\n{}\n", &t.clone().rollup());
    }

    assert_halts(termination_states, vec![
        Halt::new_test()
            .pred(peq(vu("op"), cu(0)))
            .formula(ok(add2(vu("a"), vu("b")))),
        
        Halt::new_test()
            .pred(pnot(peq(vu("op"), cu(0))))
            .formula(cerr(valu(2000)))
    ]);
}

