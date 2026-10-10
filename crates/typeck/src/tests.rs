//! The cases come from the `#guard` lines of `Silicon.Source.Test.Check` in Lean.

use crate::{Code, Failed, check};
use std::fmt::Write;

type Found = Option<(Code, usize, usize)>;

/// The first error of passes 1 to 4 as code, line, and column. The codes of passes 1 to 3 are
/// reported as the name of their pass.
fn run(src: &str) -> Result<Found, String> {
    let parsed = parse::parse(src).map_err(|e| e.to_string())?;
    let resolved = match resolve::resolve(parsed) {
        Ok(r) => r,
        Err(resolve::Failed::Names(e)) => {
            return Err(format!("{} {}:{}", e[0].code, e[0].pos.line, e[0].pos.col));
        }
        Err(resolve::Failed::Parse(p)) => {
            return Err(format!("parse {:?}", p.errors().first().map(|e| e.pos)));
        }
        Err(resolve::Failed::Stack(e)) => return Err(e.to_string()),
    };
    match check(resolved) {
        Ok(_) => Ok(None),
        Err(Failed::Errors(e)) => Ok(Some((e[0].code, e[0].pos.line, e[0].pos.col))),
        Err(Failed::Stack(e)) => Err(e.to_string()),
    }
}

fn ok(src: &str) {
    assert_eq!(run(src), Ok(None), "{src}");
}

fn fails(src: &str, code: Code, line: usize, col: usize) {
    assert_eq!(run(src), Ok(Some((code, line, col))), "{src}");
}

fn message(src: &str) -> String {
    let resolved = resolve::resolve(parse::parse(src).unwrap()).ok().unwrap();
    match check(resolved) {
        Err(Failed::Errors(e)) => e[0].message.clone(),
        _ => String::new(),
    }
}

/// The body of a function. The body starts on line 2.
fn fn_body(s: &str) -> String {
    format!("fn f(p: Bool) -> Bool {{\n{s}\n}}")
}

/// The body of a module. The body starts on line 2.
fn mod_body(s: &str) -> String {
    format!("module M(comptime W: Nat) {{\n{s}\n}}")
}

use Code::{S005, S006, S007};

#[test]
fn valid_files_pass() {
    ok("");
    ok(
        "module Counter(comptime W: Nat) {\ninput enable: Bool;\noutput value: UInt[W];\n\
        output full: Bool;\nreg count: UInt[W] = 0;\n\
        count := if (enable) { count +% 1 } else { count };\nvalue := count;\n\
        full := count == UInt[W]((1 << W) - 1);\n}\n\
        module Main() {\ninput enable: Bool;\noutput value: UInt[4];\n\
        instance counter = Counter(4);\ncounter.enable := enable;\nvalue := counter.value;\n}",
    );
    ok("comptime fn g(n: Nat) -> Nat {\ncomptime if (n == 0) { return 1; }\nreturn g(n - 1);\n}");
    ok(&mod_body(
        "input a: UInt[W];\noutput b: UInt[W];\nreg r: UInt[W] = 0;\n\
         r := a +% r;\nb := resize(UInt[W], r);\nlet x = reinterpret(SInt[W], a);",
    ));
    ok("fn g(comptime N: Nat, x: Bool) -> Bool { return x; }\n\
        module M() {\ninput a: Bool;\nlet y = g(1, a);\n}");
    ok(&mod_body(
        "input a: Bool;\nlet y = if (a) { 1 } else { 2 };",
    ));
}

#[test]
fn an_alias_and_a_domain_name_are_left_to_elab() {
    ok(&mod_body("input a: Bool;\nlet x = a;\ncomptime if (x) {}"));
    ok("module M() {\ncomptime if (clock) {}\n}");
}

#[test]
fn s005_a_static_position_names_a_resource() {
    fails(
        &mod_body("reg r: UInt[W] = 0;\ncomptime if (r == 0) {}"),
        S005,
        3,
        14,
    );
    assert_eq!(
        message(&mod_body("reg r: UInt[W] = 0;\ncomptime if (r == 0) {}")),
        "`r` is a register; a static position needs a static value"
    );
    fails(
        "module A(comptime N: Nat) {\ninput a: UInt[8];\ninstance u = A(a);\n}",
        S005,
        3,
        16,
    );
    fails(&mod_body("wire w: Bool;\nlet x: UInt[w] = 0;"), S005, 3, 13);
    fails(&mod_body("input a: Bool;\nreg r: Bool = a;"), S005, 3, 15);
    fails(
        &mod_body("wire w: Bool;\ncomptime for i in 0..w {}"),
        S005,
        3,
        22,
    );
    fails(&mod_body("reg r: Bool = false;\nlet x = r(1);"), S005, 3, 9);
}

#[test]
fn s005_the_arguments_of_a_static_call() {
    fails(
        "fn g(comptime N: Nat, x: Bool) -> Bool { return x; }\n\
         module M() {\ninput a: Bool;\nlet y = g(a, a);\n}",
        S005,
        4,
        11,
    );
    fails(
        "comptime fn g(x: Nat) -> Nat { return x; }\nmodule M() {\ninput a: Bool;\nlet y = g(a);\n}",
        S005,
        4,
        11,
    );
    fails(
        &mod_body("input a: UInt[W];\nlet y = resize(a, a);"),
        S005,
        3,
        16,
    );
    fails(
        &mod_body("input a: Bool;\nstatic_assert(a, \"m\");"),
        S005,
        3,
        15,
    );
    fails(
        &mod_body("input a: UInt[W];\nlet y = UInt[W](a);"),
        S005,
        3,
        17,
    );
    fails(&mod_body("output b: Bool;\nlet y = Bool(b);"), S005, 3, 14);
    assert_eq!(
        message(&mod_body("instance u = M(1);\ncomptime if (u.x == 1) {}")),
        "`u` is an instance; a static position needs a static value"
    );
}

#[test]
fn s005_each_part_of_a_static_expression_is_static() {
    fails(
        &mod_body("input a: UInt[W];\nlet y = UInt[W](if (true) { 1 } else { a });"),
        S005,
        3,
        40,
    );
    fails(
        &mod_body("input a: UInt[W];\nlet y = UInt[W](resize(UInt[W], a));"),
        S005,
        3,
        33,
    );
}

#[test]
fn s006_a_module_body_has_no_return() {
    fails(&mod_body("return;"), S006, 2, 1);
    fails(
        &mod_body("comptime if (true) {\n{ return; }\n}"),
        S006,
        3,
        3,
    );
    assert_eq!(
        message(&mod_body("return;")),
        "a module body has no `return`"
    );
    ok(&fn_body("comptime if (p) { return p; }\nreturn p;"));
}

#[test]
fn s006_a_comptime_fn_declares_no_hardware() {
    for stmt in [
        "reg r: Bool = false;",
        "wire w: Bool;",
        "input a: Bool;",
        "output a: Bool;",
    ] {
        fails(
            &format!("comptime fn g() -> Nat {{\n{stmt}\nreturn 1;\n}}"),
            S006,
            2,
            1,
        );
    }
    fails(
        "module A() {}\ncomptime fn g() -> Nat {\n{ instance u = A(); }\nreturn 1;\n}",
        S006,
        3,
        3,
    );
    fails(
        "comptime fn g(x: Nat) -> Nat {\nx := 1;\nreturn x;\n}",
        S006,
        2,
        1,
    );
    assert_eq!(
        message("comptime fn g(x: Nat) -> Nat {\nx := 1;\nreturn x;\n}"),
        "a `comptime fn` has no `:=`"
    );
    ok("comptime fn g(x: Nat) -> Nat {\nlet mut y = x;\ny = 1;\nreturn y;\n}");
}

#[test]
fn s007_a_call_has_the_arguments_of_its_declaration() {
    let g = "fn g(x: Nat) -> Nat { return x; }\n";
    fails(&format!("{g}const N: Nat = g(1, 2);"), S007, 2, 16);
    fails(&format!("{g}const N: Nat = g();"), S007, 2, 16);
    assert_eq!(
        message(&format!("{g}const N: Nat = g();")),
        "`g` takes 1 argument(s), but it has 0"
    );
    fails(&fn_body("return resize(UInt[8]);"), S007, 2, 8);
    fails(&fn_body("return reinterpret(UInt[8], p, p);"), S007, 2, 8);
    fails(&fn_body("static_assert(p);\nreturn p;"), S007, 2, 1);
    fails(&fn_body("error();\nreturn p;"), S007, 2, 1);
    fails(&fn_body("error(\"a\", \"b\");\nreturn p;"), S007, 2, 1);
}

#[test]
fn s007_a_call_through_a_local_or_a_const_is_not_checked() {
    ok(&fn_body("let g = p;\nreturn g(1, 2);"));
    ok("const N: Nat = 1;\nconst M: Nat = N(1, 2);");
}

#[test]
fn s007_a_constructor_has_one_argument() {
    fails(&fn_body("return Bool(true, false);"), S007, 2, 8);
    fails(&fn_body("return UInt[8]();"), S007, 2, 8);
    ok(&fn_body("return Bool(true);"));
}

#[test]
fn s007_an_instance_has_the_arguments_of_its_module() {
    fails(
        "module A(comptime N: Nat) {}\nmodule B() {\ninstance u = A();\n}",
        S007,
        3,
        1,
    );
    fails(
        "module A(comptime N: Nat) {}\nmodule B() {\ninstance u = A(1, 2);\n}",
        S007,
        3,
        1,
    );
    ok("module A(comptime N: Nat, comptime B: Bool) {}\nmodule B() {\ninstance u = A(1, true);\n}");
}

#[test]
fn s007_a_type_family_has_its_index_arguments() {
    fails("const A: UInt = 0;", S007, 1, 10);
    fails("const A: SInt[1, 2] = 0;", S007, 1, 10);
    fails("const A: Bool[1] = true;", S007, 1, 10);
    fails("const A: UInt[8][2] = 0;", S007, 1, 10);
    assert_eq!(
        message("const A: UInt[8][2] = 0;"),
        "a complete type takes 0 argument(s), but it has 1"
    );
    fails("fn g(x: Nat) -> UInt { return 0; }", S007, 1, 17);
    fails(&fn_body("return resize(SInt, p);"), S007, 2, 15);
    fails(&fn_body("return UInt(3);"), S007, 2, 8);
    fails(&fn_body("return resize(Nat[1], p);"), S007, 2, 15);
    fails(&fn_body("return resize(UInt[8][1], p);"), S007, 2, 15);
    ok(&fn_body("let x: Nat = 1;\nreturn resize(Bool, p);"));
}

#[test]
fn the_check_runs_on_an_item_that_nothing_uses() {
    fails("module Top() {}\nmodule Unused() {\nreturn;\n}", S006, 3, 1);
    fails(
        "module Top() {}\ncomptime fn unused() -> Nat {\nwire w: Bool;\nreturn 1;\n}",
        S006,
        3,
        1,
    );
    fails("fn unused(x: Nat) -> Nat { return unused(); }", S007, 1, 35);
}

#[test]
fn the_check_runs_on_both_branches_of_a_comptime_if() {
    fails(
        &mod_body("comptime if (true) {} else {\nreturn;\n}"),
        S006,
        3,
        1,
    );
    fails(
        &mod_body("comptime if (false) {\nlet x = resize(1);\n}"),
        S007,
        3,
        9,
    );
}

#[test]
fn earlier_passes_come_first() {
    let name = |src: &str, expected: &str| assert_eq!(run(src), Err(expected.to_owned()), "{src}");
    name(
        "module M() {\ninput a: Bool;\ncomptime if (a) {}\nlet x = q;\n}",
        "S003 4:9",
    );
    name(
        "module M() {\ninput a: Bool;\ncomptime if (a) {}\nlet x = 1;\nlet x = 2;\n}",
        "S002 5:5",
    );
    name("module M() {\nreturn;\nlet x = resize(q);\n}", "S003 3:16");
}

#[test]
fn errors_compete_by_position() {
    fails(
        &mod_body("return;\ninput a: Bool;\ncomptime if (a) {}"),
        S006,
        2,
        1,
    );
    fails(
        &mod_body("input a: Bool;\ncomptime if (a) {}\nreturn;"),
        S005,
        3,
        14,
    );
    fails(&mod_body("let x = resize(1);\nreturn;"), S007, 2, 9);
    fails(
        &mod_body("input a: Bool;\nlet x = resize(1, 2, 3) + UInt[W](a);"),
        S007,
        3,
        9,
    );
    fails(
        &mod_body("input a: Bool;\nlet x = UInt[W](a) + resize(1, 2, 3);"),
        S005,
        3,
        17,
    );
    fails(
        "comptime fn g() -> Nat {\nreturn 1;\n}\nmodule M() {\nreturn;\n}\nfn h() -> Nat { return g(1); }",
        S006,
        5,
        1,
    );
}

#[test]
fn deep_and_wide_inputs_pass_on_a_test_thread() {
    let mut regs = String::new();
    for i in 0..10000 {
        writeln!(regs, "reg r{i}: UInt[W] = 0;\nr{i} := r{i};").ok();
    }
    ok(&mod_body(&regs));
    fails(
        &mod_body(&format!("{regs}comptime if (r9999 == 0) {{}}")),
        S005,
        20002,
        14,
    );
    let n = 3000;
    ok(&mod_body(&format!(
        "{}comptime if (W > 0) {{}}{}",
        "{".repeat(n),
        "}".repeat(n)
    )));
    let chain = vec!["W"; n].join(" + ");
    ok(&mod_body(&format!("comptime if ({chain} > 0) {{}}")));
    ok(&mod_body(&"{ let a = W; }\n".repeat(20000)));
}
