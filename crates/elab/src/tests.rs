// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Eval` in Lean: each operator with its boundary cases,
//! the fit rule, the static faults, the table of constants, the calls, and the exact charges
//! of the cost model at the budget limits. The cases of the top selection come with `cost`.

use crate::int::Int;
use crate::ops::{int_text, str_text};
use crate::value::Evaluated;
use crate::{Budget, eval};
use std::fmt::Write;

/// The value with its types and the used fuel, or the code and the position of the first
/// error of any pass.
fn evaluated(src: &str, expr: &str, fuel: u64, depth: u64) -> Result<(Evaluated, u64), String> {
    let depth_n = parse::DEFAULT_SYNTAX_DEPTH;
    let at = |code: &dyn std::fmt::Display, pos: parse::ast::Pos| {
        Err(format!("{code} {}:{}", pos.line, pos.col))
    };
    let parsed = parse::parse_with_depth(src, depth_n).unwrap();
    if let Some(e) = parsed.errors().first() {
        return at(&e.code, e.pos);
    }
    let file = match resolve::resolve(parsed) {
        Ok(file) => file,
        Err(resolve::Failed::Names(e)) => return at(&e[0].code, e[0].pos),
        Err(resolve::Failed::Parse(_)) => panic!("the source must parse"),
        Err(resolve::Failed::Stack(e)) => panic!("{e}"),
    };
    let file = match typeck::check(file) {
        Ok(file) => file,
        Err(typeck::Failed::Errors(e)) => return at(&e[0].code, e[0].pos),
        Err(typeck::Failed::Stack(e)) => panic!("{e}"),
    };
    let e = match parse::parse_expr(expr, depth_n).unwrap() {
        Ok(e) => e,
        Err(e) => return at(&e[0].code, e[0].pos),
    };
    let e = match resolve::resolve_expr(&file, e).unwrap() {
        Ok(e) => e,
        Err(e) => return at(&e[0].code, e[0].pos),
    };
    let e = match typeck::check_expr(&file, e) {
        Ok(e) => e,
        Err(typeck::Failed::Errors(e)) => return at(&e[0].code, e[0].pos),
        Err(typeck::Failed::Stack(e)) => panic!("{e}"),
    };
    match eval(&file, &e, Budget { fuel, depth }).unwrap() {
        Ok(done) => Ok(done),
        Err(e) => at(&e.code, e.pos),
    }
}

/// The result of `eval`: the serialization, or the code and the position of the first error
/// of any pass. The second value is the used fuel.
fn run(src: &str, expr: &str, fuel: u64, depth: u64) -> (String, u64) {
    match evaluated(src, expr, fuel, depth) {
        Ok((v, used)) => (v.serialize(), used),
        Err(error) => (error, 0),
    }
}

/// The work of the table of types for `expr`: for each lookup of a type, 1 plus the number
/// of its parts. A copy of a type costs none of it, so the work follows the types that the
/// program builds, not the values that it copies.
pub(crate) fn type_work(src: &str, expr: &str) -> u64 {
    let budget = Budget::default();
    match evaluated(src, expr, budget.fuel, budget.depth) {
        Ok((done, _)) => done.types.work,
        Err(error) => panic!("{error}"),
    }
}

/// The steps of the walks along paths into values for `expr`: 1 for each container that a
/// walk enters. The tests count the steps and not the time.
pub(crate) fn path_steps(src: &str, expr: &str) -> u64 {
    let budget = Budget::default();
    match evaluated(src, expr, budget.fuel, budget.depth) {
        Ok((done, _)) => done.steps,
        Err(error) => panic!("{error}"),
    }
}

pub(crate) fn out(src: &str, expr: &str, fuel: u64, depth: u64) -> String {
    run(src, expr, fuel, depth).0
}

/// The fuel that `eval` uses with the default budgets, or 0 for an error.
pub(crate) fn cost(src: &str, expr: &str) -> u64 {
    let budget = Budget::default();
    run(src, expr, budget.fuel, budget.depth).1
}

/// The cost is `units`. This fuel passes, and one unit less gives `S015`.
pub(crate) fn exact(src: &str, expr: &str, units: u64) {
    assert_eq!(cost(src, expr), units, "{expr}");
    assert!(!out(src, expr, units, 1000).starts_with('S'), "{expr}");
    assert!(
        out(src, expr, units - 1, 1000).starts_with("S015"),
        "{expr}"
    );
}

const ASSERTS: &str = "comptime fn check(n: Nat) -> Nat {\n\
    \x20   static_assert(n < 4, \"n is small\");\n\
    \x20   comptime if (n == 3) { error(\"three\"); }\n\
    \x20   return n;\n\
    }";

const PROGRAM: &str = "comptime fn fact(n: Nat) -> Nat {\n\
    \x20   comptime if (n == 0) { return 1; }\n\
    \x20   return n * fact(n - 1);\n\
    }\n\
    comptime fn sum(n: Nat) -> Int {\n\
    \x20   let mut s = 0;\n\
    \x20   comptime for i in 0..n { s = s + i; }\n\
    \x20   return s;\n\
    }\n\
    comptime fn fib(n: Nat) -> Nat {\n\
    \x20   comptime if (n < 2) { return n; } else { return fib(n - 1) + fib(n - 2); }\n\
    }\n\
    comptime fn mask(comptime w: Nat) -> UInt[w] {\n\
    \x20   let x: UInt[w] = 0;\n\
    \x20   return ~x;\n\
    }\n\
    comptime fn bad(n: Nat) -> Nat {\n\
    \x20   let x = n;\n\
    \x20   x = 1;\n\
    \x20   return n - 5;\n\
    }\n\
    comptime fn none(n: Nat) -> Nat {\n\
    \x20   comptime if (n == 0) { return 0; }\n\
    }\n\
    fn wraps(x: UInt[8]) -> UInt[8] { return x +% 1; }";

const CONSTS: &str = "const A: Nat = 2;\n\
    const B: UInt[8] = A + 250;\n\
    const C: Nat = C + 1;\n\
    const D: Nat = E;\n\
    const E: Nat = D;\n\
    const F: Nat = 1 / 0;\n\
    const G: Nat = A - 3;";

const BIGFOR: &str =
    "comptime fn f() -> Int { let a = 1 << 64000000; comptime for i in a..a + 10000 {} return 0; }";

const WIDEFOR: &str =
    "comptime fn f() -> Int { let a = 1 << 6400; comptime for i in a..a + 3 {} return 0; }";

const DEEP: &str = "comptime fn d(n: Nat) -> Nat {\n\
    \x20   comptime if (n == 0) { return 0; }\n\
    \x20   return d(n - 1);\n\
    }";

/// A frame holds only the bindings that run. `f` and `r` declare `locals` locals in a branch
/// that does not run.
fn skipped(locals: usize) -> String {
    let mut dead = String::new();
    for i in 0..locals {
        write!(dead, "let x{i} = 0; ").unwrap();
    }
    format!(
        "comptime fn f() -> Int {{ comptime if (false) {{ {dead}}} let y = 0; return y; }}\n\
         comptime fn g(n: Nat) -> Int {{ comptime for i in 0..n {{ let z = f(); }} return 0; }}\n\
         comptime fn r(n: Nat) -> Int {{ comptime if (false) {{ {dead}}}\n\
         \x20 comptime if (n == 0) {{ return 0; }} return r(n - 1); }}\n"
    )
}

/// A chain of 300 acyclic constants.
fn chain() -> String {
    let mut s = "const C0: Nat = 0;\n".to_owned();
    for k in 1..300 {
        writeln!(s, "const C{k}: Nat = C{} + 1;", k - 1).unwrap();
    }
    s + "module Top(comptime x: UInt[C299 + 1]) {\n}\n"
}

#[test]
#[allow(clippy::too_many_lines)]
fn the_cases_of_lean() {
    assert_eq!(out("", "1 + 2", 100_000_000, 1000), "(int 3)");
    assert_eq!(out("", "1 - 2", 100_000_000, 1000), "(int -1)");
    assert_eq!(
        out("", "18446744073709551615 + 1", 100_000_000, 1000),
        "(int 18446744073709551616)"
    );
    assert_eq!(
        out("", "4294967296 * 4294967296", 100_000_000, 1000),
        "(int 18446744073709551616)"
    );
    assert_eq!(out("", "7 / 2", 100_000_000, 1000), "(int 3)");
    assert_eq!(out("", "-7 / 2", 100_000_000, 1000), "(int -3)");
    assert_eq!(out("", "7 / -2", 100_000_000, 1000), "(int -3)");
    assert_eq!(out("", "-7 % 2", 100_000_000, 1000), "(int -1)");
    assert_eq!(out("", "7 % -2", 100_000_000, 1000), "(int 1)");
    assert_eq!(out("", "-(-5)", 100_000_000, 1000), "(int 5)");
    assert_eq!(
        out("", "UInt[8](250) +% 10", 100_000_000, 1000),
        "(uint 8 4)"
    );
    assert_eq!(
        out("", "UInt[8](0) -% 1", 100_000_000, 1000),
        "(uint 8 255)"
    );
    assert_eq!(
        out("", "UInt[8](16) *% 16", 100_000_000, 1000),
        "(uint 8 0)"
    );
    assert_eq!(
        out("", "SInt[8](127) +% 1", 100_000_000, 1000),
        "(sint 8 -128)"
    );
    assert_eq!(
        out("", "SInt[8](-128) -% 1", 100_000_000, 1000),
        "(sint 8 127)"
    );
    assert_eq!(out("", "1 +% UInt[1](1)", 100_000_000, 1000), "(uint 1 0)");
    assert_eq!(out("", "-UInt[8](1)", 100_000_000, 1000), "(uint 8 255)");
    assert_eq!(
        out("", "-SInt[8](-128)", 100_000_000, 1000),
        "(sint 8 -128)"
    );
    assert_eq!(out("", "UInt[8](12) & 10", 100_000_000, 1000), "(uint 8 8)");
    assert_eq!(
        out("", "UInt[8](12) | 10", 100_000_000, 1000),
        "(uint 8 14)"
    );
    assert_eq!(out("", "UInt[8](12) ^ 10", 100_000_000, 1000), "(uint 8 6)");
    assert_eq!(out("", "~UInt[8](0)", 100_000_000, 1000), "(uint 8 255)");
    assert_eq!(out("", "~SInt[8](0)", 100_000_000, 1000), "(sint 8 -1)");
    assert_eq!(out("", "~5", 100_000_000, 1000), "(int -6)");
    assert_eq!(out("", "~-1", 100_000_000, 1000), "(int 0)");
    assert_eq!(out("", "-6 & 3", 100_000_000, 1000), "(int 2)");
    assert_eq!(out("", "-6 | 3", 100_000_000, 1000), "(int -5)");
    assert_eq!(out("", "-6 ^ 3", 100_000_000, 1000), "(int -7)");
    assert_eq!(out("", "-6 & -3", 100_000_000, 1000), "(int -8)");
    assert_eq!(out("", "-6 | -3", 100_000_000, 1000), "(int -1)");
    assert_eq!(out("", "-6 ^ -3", 100_000_000, 1000), "(int 7)");
    assert_eq!(out("", "12 & 10", 100_000_000, 1000), "(int 8)");
    assert_eq!(out("", "!true", 100_000_000, 1000), "(bool false)");
    assert_eq!(out("", "true && false", 100_000_000, 1000), "(bool false)");
    assert_eq!(out("", "false || true", 100_000_000, 1000), "(bool true)");
    assert_eq!(
        out("", "false && 1 / 0 == 0", 100_000_000, 1000),
        "(bool false)"
    );
    assert_eq!(
        out("", "true || 1 / 0 == 0", 100_000_000, 1000),
        "(bool true)"
    );
    assert_eq!(out("", "true && 1 / 0 == 0", 100_000_000, 1000), "S013 1:9");
    assert_eq!(
        out("", "if (true) { 1 } else { 1 / 0 }", 100_000_000, 1000),
        "(int 1)"
    );
    assert_eq!(out("", "3 == 3", 100_000_000, 1000), "(bool true)");
    assert_eq!(out("", "true != false", 100_000_000, 1000), "(bool true)");
    assert_eq!(out("", "\"a\" == \"a\"", 100_000_000, 1000), "(bool true)");
    assert_eq!(
        out("", "UInt[8] == UInt[8]", 100_000_000, 1000),
        "(bool true)"
    );
    assert_eq!(
        out("", "UInt[8] == SInt[8]", 100_000_000, 1000),
        "(bool false)"
    );
    assert_eq!(
        out("", "UInt[8](255) > 1", 100_000_000, 1000),
        "(bool true)"
    );
    assert_eq!(out("", "SInt[8](-1) < 1", 100_000_000, 1000), "(bool true)");
    assert_eq!(
        out("", "SInt[8](-128) <= SInt[8](-128)", 100_000_000, 1000),
        "(bool true)"
    );
    assert_eq!(out("", "-1 >= 0", 100_000_000, 1000), "(bool false)");
    assert_eq!(
        out("", "UInt[8](300 - 45) == 255", 100_000_000, 1000),
        "(bool true)"
    );
    assert_eq!(out("", "1 << 8", 100_000_000, 1000), "(int 256)");
    assert_eq!(out("", "-3 >> 1", 100_000_000, 1000), "(int -2)");
    assert_eq!(out("", "-3 >> 100", 100_000_000, 1000), "(int -1)");
    assert_eq!(out("", "3 >> 100", 100_000_000, 1000), "(int 0)");
    assert_eq!(
        out("", "1 << 64", 100_000_000, 1000),
        "(int 18446744073709551616)"
    );
    assert_eq!(
        out("", "UInt[8](1) << 7", 100_000_000, 1000),
        "(uint 8 128)"
    );
    assert_eq!(out("", "UInt[8](1) << 8", 100_000_000, 1000), "(uint 8 0)");
    assert_eq!(
        out("", "UInt[8](128) >> 7", 100_000_000, 1000),
        "(uint 8 1)"
    );
    assert_eq!(
        out("", "SInt[8](-128) >> 7", 100_000_000, 1000),
        "(sint 8 -1)"
    );
    assert_eq!(
        out("", "SInt[8](-128) >> 1000", 100_000_000, 1000),
        "(sint 8 -1)"
    );
    assert_eq!(
        out("", "SInt[8](64) >> 1000", 100_000_000, 1000),
        "(sint 8 0)"
    );
    assert_eq!(
        out("", "UInt[8](1) << UInt[2](3)", 100_000_000, 1000),
        "(uint 8 8)"
    );
    assert_eq!(out("", "1 << -1", 100_000_000, 1000), "S013 1:1");
    assert_eq!(out("", "UInt[8](1) << -1", 100_000_000, 1000), "S013 1:1");
    assert_eq!(
        out("", "UInt[8](1) << SInt[2](1)", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(out("", "1 << UInt[2](1)", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "true << 1", 100_000_000, 1000), "S010 1:1");
    assert_eq!(
        out("", "resize(UInt[16], UInt[8](255))", 100_000_000, 1000),
        "(uint 16 255)"
    );
    assert_eq!(
        out("", "resize(SInt[16], SInt[8](-1))", 100_000_000, 1000),
        "(sint 16 -1)"
    );
    assert_eq!(
        out("", "resize(UInt[4], UInt[8](250))", 100_000_000, 1000),
        "(uint 4 10)"
    );
    assert_eq!(
        out("", "resize(SInt[4], SInt[8](-7))", 100_000_000, 1000),
        "(sint 4 -7)"
    );
    assert_eq!(
        out("", "resize(SInt[16], UInt[8](1))", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(
        out("", "resize(UInt[16], 1)", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(
        out("", "reinterpret(SInt[8], UInt[8](255))", 100_000_000, 1000),
        "(sint 8 -1)"
    );
    assert_eq!(
        out("", "reinterpret(UInt[8], SInt[8](-128))", 100_000_000, 1000),
        "(uint 8 128)"
    );
    assert_eq!(
        out("", "reinterpret(UInt[4], SInt[8](1))", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(out("", "UInt[8](255)", 100_000_000, 1000), "(uint 8 255)");
    assert_eq!(out("", "UInt[8](256)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "UInt[8](-1)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "SInt[8](-128)", 100_000_000, 1000), "(sint 8 -128)");
    assert_eq!(out("", "SInt[8](127)", 100_000_000, 1000), "(sint 8 127)");
    assert_eq!(out("", "SInt[8](-129)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "SInt[8](128)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "SInt[1](-1)", 100_000_000, 1000), "(sint 1 -1)");
    assert_eq!(out("", "SInt[1](1)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "Nat(0)", 100_000_000, 1000), "(int 0)");
    assert_eq!(out("", "Nat(-1)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "UInt[8](1) +% 256", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "UInt[0]", 100_000_000, 1000), "S012 1:1");
    assert_eq!(
        out("", "UInt[65536]", 100_000_000, 1000),
        "(type (uint 65536))"
    );
    assert_eq!(out("", "UInt[65537]", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out("", "UInt[8](1) + 1", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "1 +% 1", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "true + 1", 100_000_000, 1000), "S010 1:1");
    assert_eq!(
        out("", "UInt[8](1) +% SInt[8](1)", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(
        out("", "UInt[8](1) == UInt[4](1)", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(out("", "true < false", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "!1", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "\"a\" + \"b\"", 100_000_000, 1000), "S010 1:1");
    assert_eq!(
        out("", "if (1) { 1 } else { 2 }", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(out("", "UInt[true]", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "Bool(1)", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out("", "1 / 0", 100_000_000, 1000), "S013 1:1");
    assert_eq!(out("", "1 % 0", 100_000_000, 1000), "S013 1:1");
    assert_eq!(out(ASSERTS, "check(2)", 100_000_000, 1000), "(int 2)");
    assert_eq!(out(ASSERTS, "check(3)", 100_000_000, 1000), "S014 3:28");
    assert_eq!(out(ASSERTS, "check(4)", 100_000_000, 1000), "S014 2:5");
    assert_eq!(
        out(ASSERTS, "static_assert(true, \"x\")", 100_000_000, 1000),
        "S010 1:1"
    );
    assert_eq!(
        out(PROGRAM, "fact(20)", 100_000_000, 1000),
        "(int 2432902008176640000)"
    );
    assert_eq!(out(PROGRAM, "fact(0)", 100_000_000, 1000), "(int 1)");
    assert_eq!(out(PROGRAM, "sum(10)", 100_000_000, 1000), "(int 45)");
    assert_eq!(out(PROGRAM, "sum(0)", 100_000_000, 1000), "(int 0)");
    assert_eq!(out(PROGRAM, "fib(15)", 100_000_000, 1000), "(int 610)");
    assert_eq!(
        out(PROGRAM, "mask(12)", 100_000_000, 1000),
        "(uint 12 4095)"
    );
    assert_eq!(out(PROGRAM, "wraps(255)", 100_000_000, 1000), "(uint 8 0)");
    assert_eq!(out(PROGRAM, "wraps(256)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out(PROGRAM, "fact(-1)", 100_000_000, 1000), "S012 1:1");
    assert_eq!(out(PROGRAM, "bad(1)", 100_000_000, 1000), "S010 19:5");
    assert_eq!(out(PROGRAM, "none(0)", 100_000_000, 1000), "(int 0)");
    assert_eq!(out(PROGRAM, "none(1)", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out(PROGRAM, "fact", 100_000_000, 1000), "S010 1:1");
    assert_eq!(out(PROGRAM, "resize", 100_000_000, 1000), "S010 1:1");
    assert_eq!(
        out(
            "comptime fn f(n: Int) -> Nat {\n    return n;\n}",
            "f(-1)",
            100_000_000,
            1000
        ),
        "S012 2:5"
    );
    assert_eq!(
        out(
            "comptime fn f(n: Int) -> Bool {\n    return n;\n}",
            "f(1)",
            100_000_000,
            1000
        ),
        "S010 2:5"
    );
    assert_eq!(
        out(
            "comptime fn f(n: Int) -> Int {\n    let x: Nat = n;\n    return x;\n}",
            "f(-2)",
            100_000_000,
            1000
        ),
        "S012 2:5"
    );
    assert_eq!(
        out(
            "fn f(x: Bool) -> Bool {\n    x := x;\n    return x;\n}",
            "f(true)",
            100_000_000,
            1000
        ),
        "S011 2:5"
    );
    assert_eq!(out(CONSTS, "A", 100_000_000, 1000), "(int 2)");
    assert_eq!(out(CONSTS, "B", 100_000_000, 1000), "(uint 8 252)");
    assert_eq!(out(CONSTS, "B +% B", 100_000_000, 1000), "(uint 8 248)");
    assert_eq!(out(CONSTS, "C", 100_000_000, 1000), "S019 3:16");
    assert_eq!(out(CONSTS, "D", 100_000_000, 1000), "S019 5:16");
    assert_eq!(out(CONSTS, "E", 100_000_000, 1000), "S019 4:16");
    assert_eq!(out(CONSTS, "F", 100_000_000, 1000), "S013 6:16");
    assert_eq!(out(CONSTS, "G", 100_000_000, 1000), "S012 7:1");
    exact("", "1 + 2", 7);
    exact("", "true", 2);
    exact("", "\"abc\"", 5);
    exact("", "-5", 4);
    exact("", "UInt[8]", 6);
    exact("", "UInt[8](3)", 12);
    exact("", "3 * 4", 6);
    exact("", "18446744073709551616 * 18446744073709551616", 11);
    exact("", "1 << 64", 7);
    exact("", "1 << 63", 6);
    exact("", "true && false", 5);
    exact("", "false && true", 3);
    exact("", "if (true) { 1 } else { 2 }", 5);
    exact("const A: Nat = 2;", "A + A", 8);
    exact("const A: Nat = 2;\nconst B: Nat = A;", "B", 7);
    exact("comptime fn f(n: Nat) -> Nat { return n; }", "f(1)", 11);
    exact(
        "comptime fn s() -> Int { comptime for i in 0..3 {} return 0; }",
        "s()",
        21,
    );
    exact(
        "comptime fn s() -> Int { let x = 1; let y = x; return y; }",
        "s()",
        13,
    );
    exact("comptime fn s() -> Int { { } return 0; }", "s()", 9);
    exact("comptime fn s() -> Int { return 0; }", "s()", 8);
    exact("", "resize(UInt[16], UInt[8](1))", 25);
    exact(
        "comptime fn s() -> Int { static_assert(true, \"abc\"); return 0; }",
        "s()",
        23,
    );
    exact(PROGRAM, "fact(10)", cost(PROGRAM, "fact(10)"));
    exact(PROGRAM, "sum(100)", cost(PROGRAM, "sum(100)"));
    assert_eq!(out("", "1 << 100000000000", 100_000_000, 1000), "S015 1:1");
    assert_eq!(out("", "1 << 6400000000", 100_000_000, 1000), "S015 1:1");
    assert_eq!(out("", "0 << 100000000000", 20, 1000), "(int 0)");
    assert_eq!(out("", "0 << 18446744073709551616", 20, 1000), "(int 0)");
    assert_eq!(out("", "-1 << 100000000000", 20, 1000), "S015 1:1");
    assert_eq!(out("", "0 >> 100000000000", 20, 1000), "(int 0)");
    assert_eq!(out("", "1 >> 100000000000", 20, 1000), "(int 0)");
    assert_eq!(out("", "-1 >> 100000000000", 20, 1000), "(int -1)");
    assert_eq!(out(BIGFOR, "f()", 4_000_000, 1000), "S015 1:49");
    exact(WIDEFOR, "f()", cost(WIDEFOR, "f()"));
    assert_eq!(out(&skipped(2000), "g(100)", 100_000_000, 1000), "(int 0)");
    assert_eq!(out(&skipped(2000), "r(500)", 100_000_000, 1000), "(int 0)");
    assert_eq!(out("", "UInt[1 << 6400000]", 100_008, 1000), "S012 1:1");
    assert_eq!(out("", "Nat(-(1 << 6400000))", 400_000, 1000), "S012 1:1");
    assert_eq!(out("", "UInt[8](1 << 6400000)", 400_000, 1000), "S012 1:1");
    assert_eq!(out("", "1 << -(1 << 6400000)", 300_000, 1000), "S013 1:1");
    assert_eq!(out("", "1 << (1 << 6400)", 1000, 1000), "S015 1:1");
    exact("", "-(1 << 6400) >> 6399", 312);
    assert_eq!(
        out("", "UInt[8](1) << 100000000000", 20, 1000),
        "(uint 8 0)"
    );
    assert_eq!(
        out("", "SInt[8](-1) >> 100000000000", 20, 1000),
        "(sint 8 -1)"
    );
    assert_eq!(
        out("", "UInt[65536](1) << 100000000000", 20, 1000),
        "S015 1:1"
    );
    assert_eq!(
        out("", "resize(UInt[65536], UInt[8](1))", 20, 1000),
        "S015 1:1"
    );
    assert_eq!(out(DEEP, "d(5)", 100_000_000, 6), "(int 0)");
    assert_eq!(out(DEEP, "d(5)", 100_000_000, 5), "S015 3:12");
    assert_eq!(out(DEEP, "d(0)", 100_000_000, 0), "S015 1:1");
    assert_eq!(out(DEEP, "d(2000)", 100_000_000, 1000), "S015 3:12");
    assert_eq!(out(&chain(), "C299", 100_000_000, 300), "(int 299)");
    exact(&chain(), "C299", 2097);
    assert_eq!(out(&chain(), "C299", 100_000_000, 299), "S015 2:17");
    assert_eq!(out("const A: Nat = ;", "1", 100_000_000, 1000), "S001 1:16");
    assert_eq!(out("", "x", 100_000_000, 1000), "S003 1:1");
    assert_eq!(out("", "1 +", 100_000_000, 1000), "S001 1:4");
    assert_eq!(out("", "UInt[8, 9]", 100_000_000, 1000), "S007 1:1");
    assert_eq!(
        out(
            "module M() { reg r: Bool = false; }",
            "M",
            100_000_000,
            1000
        ),
        "S003 1:1"
    );
}

#[test]
fn costs() {
    assert_eq!(cost("", "1 << 64000"), 1006);
    assert_eq!(cost(WIDEFOR, "f()"), 731);
    assert_eq!(cost(&skipped(2000), "g(100)"), cost(&skipped(1), "g(100)"));
}

#[test]
fn bounded_messages() {
    let two = Int::from_u64(2);
    let pow = |k: u64| Int::from_u64(1).shl(k);
    assert_eq!(
        int_text(&pow(256).sub(&Int::from_u64(1))),
        pow(256).sub(&Int::from_u64(1)).to_string()
    );
    assert_eq!(int_text(&pow(256)), "an integer of 257 bits");
    assert_eq!(
        int_text(&pow(6_400_000).neg()),
        "a negative integer of 6400001 bits"
    );
    assert_eq!(int_text(&two), "2");
    assert_eq!(str_text("abc"), "abc");
    assert_eq!(
        str_text(&"a".repeat(100)),
        format!("{}... (100 characters)", "a".repeat(64))
    );
    assert_eq!(str_text(&"ä".repeat(64)), "ä".repeat(64));
}

/// A deep recursion runs a group of levels on each thread, so a large nesting depth needs no
/// large stack.
#[test]
fn deep_recursion() {
    assert_eq!(out(DEEP, "d(100000)", 100_000_000, 200_000), "(int 0)");
    assert_eq!(out(DEEP, "d(100000)", 100_000_000, 100_000), "S015 3:12");
}

/// A use of a local refers to its value: a read that the cost model does not charge copies
/// nothing. The loop reads a value of 100,000 words 20,000 times.
#[test]
fn a_read_copies_nothing() {
    let src = "comptime fn f() -> Int {\n\
        \x20   let a = 1 << 6400000;\n\
        \x20   comptime for i in 0..20000 { a; let b = if (true) { i } else { a }; }\n\
        \x20   return 0;\n\
        }";
    let start = std::time::Instant::now();
    assert_eq!(out(src, "f()", 1_000_000, 1000), "(int 0)");
    assert!(start.elapsed() < std::time::Duration::from_secs(5));
}

/// A call binds its arguments before the caller frame ends: a local argument, a parameter
/// forwarded through calls and recursion, a returned local, a conditional, and a loop value.
#[test]
fn arguments_bind_in_the_caller_frame() {
    let id = "comptime fn id(x: Int) -> Int { return x; }\n";
    let fwd = |src: &str| format!("{id}{src}");
    assert_eq!(
        out(
            "comptime fn id(x: Bool) -> Bool { return x; }\n\
             comptime fn f() -> Bool { let x = true; return id(x); }",
            "f()",
            100_000_000,
            1000
        ),
        "(bool true)"
    );
    let int = fwd("comptime fn f() -> Int { let x = 5; return id(x); }");
    assert_eq!(out(&int, "f()", 100_000_000, 1000), "(int 5)");
    exact(&int, "f()", 19);
    let two = fwd("comptime fn g(y: Int) -> Int { return id(y); }\n\
         comptime fn f() -> Int { let x = 7; return g(x); }");
    assert_eq!(out(&two, "f()", 100_000_000, 1000), "(int 7)");
    let rec = "comptime fn f(n: Int, acc: Int) -> Int {\n\
        \x20   comptime if (n == 0) { return acc; } return f(n - 1, acc + n); }\n\
        comptime fn h(n: Int, acc: Int) -> Int {\n\
        \x20   comptime if (n == 0) { return acc; } return h(n - 1, acc); }";
    assert_eq!(out(rec, "f(4, 0)", 100_000_000, 1000), "(int 10)");
    assert_eq!(out(rec, "h(3, 5)", 100_000_000, 1000), "(int 5)");
    let ret = fwd("comptime fn g() -> Int { let x = 9; return x; }\n\
         comptime fn f() -> Int { return id(g()); }");
    assert_eq!(out(&ret, "f()", 100_000_000, 1000), "(int 9)");
    let cond = fwd("comptime fn f(c: Bool) -> Int {\n\
         \x20   let a = 3; let b = 4; return id(if (c) { a } else { b }); }");
    assert_eq!(out(&cond, "f(true)", 100_000_000, 1000), "(int 3)");
    assert_eq!(out(&cond, "f(false)", 100_000_000, 1000), "(int 4)");
    let lp = fwd("comptime fn f() -> Int {\n\
         \x20   let mut s = 0; comptime for i in 0..4 { s = s + id(i); } return s; }");
    assert_eq!(out(&lp, "f()", 100_000_000, 1000), "(int 6)");
}

/// Each pass over a standalone expression runs on a stack for the depth of its own parse, also
/// when the file has a smaller depth. The test thread has a normal stack.
#[test]
fn a_deep_expression_keeps_the_depth_of_its_parse() {
    let file = resolve::resolve(parse::parse_with_depth("", 1).unwrap())
        .ok()
        .unwrap();
    let file = typeck::check(file).ok().unwrap();
    let depth = parse::DEFAULT_SYNTAX_DEPTH;
    for (text, value) in [
        (format!("{}1", "-".repeat(depth - 1)), "(int -1)"),
        (
            format!("{}1{}", "(".repeat(depth), ")".repeat(depth)),
            "(int 1)",
        ),
    ] {
        let e = parse::parse_expr(&text, depth).unwrap().ok().unwrap();
        let e = resolve::resolve_expr(&file, e).unwrap().ok().unwrap();
        let e = typeck::check_expr(&file, e).ok().unwrap();
        let (v, _) = eval(&file, &e, Budget::default()).unwrap().unwrap();
        assert_eq!(v.serialize(), value);
    }
}

/// A number literal pays the size of its value before it copies the value, and the pass
/// before the evaluation converts its digits. A literal of 19,000 digits has 987 words.
#[test]
fn a_literal_pays_before_its_copy() {
    let lit = "9".repeat(19_000);
    assert_eq!(out("", &lit, 1, 1000), "S015 1:1");
    exact("", &lit, 988);
    let src = format!("comptime fn f() -> Int {{ return {lit}; }}");
    assert_eq!(out(&src, "f()", 10, 1000), "S015 1:33");
}
