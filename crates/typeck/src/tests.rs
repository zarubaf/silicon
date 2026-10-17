// SPDX-License-Identifier: Apache-2.0
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

use Code::{S005, S006, S007, S008};

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
fn s005_a_static_position_names_a_memory() {
    ok(&mod_body("mem m: [UInt[W]; W + 1];\nlet x = m;"));
    let cases = [
        ("mem m: [Bool; 4];\nlet x: [Bool; m] = 0;", 3, 15),
        ("mem m: [Bool; 4];\nlet x = [Bool; m]();", 3, 16),
        ("mem m: [Bool; 4];\nlet x: UInt[m] = 0;", 3, 13),
        ("mem m: [Bool; 4];\ncomptime if (m) {}", 3, 14),
        ("mem m: [Bool; 4];\ninstance u = M(m);", 3, 16),
        ("wire w: UInt[8];\nmem m: [Bool; w];", 3, 15),
        ("mem m: [Bool; 4];\nmem k: [UInt[m]; 4];", 3, 14),
    ];
    for (body, line, col) in cases {
        fails(&mod_body(body), S005, line, col);
    }
    assert_eq!(
        message(&mod_body("mem m: [Bool; 4];\ncomptime if (m) {}")),
        "`m` is a memory; a static position needs a static value"
    );
}

#[test]
fn s006_a_comptime_fn_has_no_mem() {
    let fn_with = |body: &str| format!("comptime fn g() -> Nat {{\n{body}\nreturn 1;\n}}");
    fails(&fn_with("mem m: [Bool; 4];"), S006, 2, 1);
    fails(&fn_with("{ mem m: [Bool; 4]; }"), S006, 2, 3);
    fails(
        &fn_with("mem m: [Bool; 4];\ncomptime if (m) {}"),
        S006,
        2,
        1,
    );
    assert_eq!(
        message(&fn_with("mem m: [Bool; 4];")),
        "a `comptime fn` has no memory"
    );
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
    assert_eq!(
        message(&fn_body("return Bool(true, false);")),
        "a constructor takes 0 or 1 argument(s), but it has 2"
    );
    // The zero `T()` has no argument.
    ok(&fn_body("return UInt[8]();"));
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

#[test]
fn a_nested_index_chain_at_the_default_depth_checks() {
    let n = 4000;
    let chain = format!("x{}", "[0]".repeat(n));
    ok(&format!("fn f(x: Nat) -> Nat {{ return {chain}; }}"));
    let types = format!("UInt{}", "[1]".repeat(n));
    // The first index takes the one argument, and each further index is `S007`.
    fails(&format!("const A: Nat = {types};"), S007, 1, 16);
}

/// The first error of the check of `expr` in the file scope of `src`.
fn run_expr(src: &str, expr: &str) -> Found {
    let resolved = check(resolve::resolve(parse::parse(src).unwrap()).ok().unwrap())
        .ok()
        .unwrap();
    let expr = parse::parse_expr(expr, parse::DEFAULT_SYNTAX_DEPTH)
        .unwrap()
        .ok()
        .unwrap();
    let expr = resolve::resolve_expr(&resolved, expr)
        .unwrap()
        .ok()
        .unwrap();
    match crate::check_expr(&resolved, expr) {
        Ok(_) => None,
        Err(Failed::Errors(e)) => Some((e[0].code, e[0].pos.line, e[0].pos.col)),
        Err(Failed::Stack(e)) => panic!("{e}"),
    }
}

#[test]
fn an_expression_is_checked_as_a_static_position() {
    let src = "comptime fn f(n: Nat) -> Nat { return n; }\nconst A: Nat = 1;";
    assert_eq!(run_expr(src, "f(A) + UInt[8](1)"), None);
    assert_eq!(run_expr(src, "UInt[8, 9]"), Some((Code::S007, 1, 1)));
    assert_eq!(run_expr(src, "1 + f(1, 2)"), Some((Code::S007, 1, 5)));
    assert_eq!(run_expr(src, "UInt"), Some((Code::S007, 1, 1)));
    assert_eq!(run_expr(src, "Bool(1, 2)"), Some((Code::S007, 1, 1)));
    // The arity check reads the targets of the expression, not of the file at 1:1.
    assert_eq!(run_expr(src, "f(1, 2)"), Some((Code::S007, 1, 1)));
}

#[test]
fn s007_len_has_one_argument() {
    fails(&fn_body("return len();"), S007, 2, 8);
    fails(&fn_body("return len([p], [p]);"), S007, 2, 8);
    assert_eq!(
        message(&fn_body("return len([p], [p]);")),
        "`len` takes 1 argument(s), but it has 2"
    );
    ok(&fn_body("let n = len([p, p]);\nreturn p;"));
}

#[test]
fn s007_container_types_take_no_index() {
    fails("const A: Unit[1] = ();", S007, 1, 10);
    fails(&fn_body("return Unit[1];"), S007, 2, 8);
    fails("const A: [Bool; 2][1] = [true, true];", S007, 1, 10);
    fails("const A: (Bool,)[0] = (true,);", S007, 1, 10);
    assert_eq!(
        message("const A: (Bool,)[0] = (true,);"),
        "a complete type takes 0 argument(s), but it has 1"
    );
    ok("const A: Unit = ();\nconst B: ((), [Unit; 0]) = ((), []);");
}

#[test]
fn s007_a_part_of_a_container_has_its_index_arguments() {
    fails("const A: (UInt, Bool) = (0, true);", S007, 1, 11);
    fails("const A: [UInt; 2] = [0, 0];", S007, 1, 11);
    fails("const A: [[Bool; 1][1]; 2] = [];", S007, 1, 11);
    fails(&fn_body("return (p, SInt);"), S007, 2, 12);
    fails(&fn_body("return [resize(p)].0;"), S007, 2, 9);
}

#[test]
fn s005_the_container_index_and_the_array_length_are_static() {
    fails(
        &mod_body("reg r: UInt[W] = 0;\ncomptime if ((r, 1).0 == 0) {}"),
        S005,
        3,
        15,
    );
    fails(
        &mod_body("reg r: UInt[W] = 0;\ncomptime if ([r][0] == 0) {}"),
        S005,
        3,
        15,
    );
    fails(
        &mod_body("wire w: Nat;\nlet x: [Bool; w] = [];"),
        S005,
        3,
        15,
    );
    fails(
        &mod_body("input a: UInt[W];\nlet y = [1, 2][a];"),
        S005,
        3,
        16,
    );
    fails(
        &mod_body("input a: UInt[W];\nlet y = (1, 2)[a];"),
        S005,
        3,
        16,
    );
}

#[test]
fn the_rules_that_need_static_values_are_left_to_elab() {
    ok(&mod_body(
        "input a: Bool;\nlet t = (a, ());\nlet n = len([a, a]);\nlet x = t.0;",
    ));
    ok(&fn_body(
        "let t = (1, 2);\nlet x = t[0, 1];\nlet y = t < t;\nreturn [1] == [1, 2];",
    ));
}

// The struct and type forms of slice 2, phase 3.

/// The struct `P` with one parameter and two fields, the struct `S` without parameters, and the
/// struct `E` without fields.
const STRUCTS: &str =
    "\nstruct P(comptime W: Nat) { a: UInt[W], b: Bool }\nstruct S { a: Bool }\nstruct E {}";

fn with_structs(src: &str) -> String {
    format!("{src}{STRUCTS}")
}

#[test]
fn structs_zero_and_type_items_pass() {
    ok(&with_structs(
        "const A: P[8] = P[8](1, true);\nconst B: S = S(true);\nconst C: P[2] = P[2]();\n\
         const D: E = E();\nconst N: Nat = data_bits(P[8]);",
    ));
    ok("type A = UInt[8];\nconst B: A = A(3);\nconst C: Type = A;\nconst D: A = A();");
    ok(&fn_body(
        "type T = (Bool, [UInt[8]; 2]);\nlet x: T = T();\nreturn p;",
    ));
    ok("fn f(comptime T: Type, x: T) -> T { return T(x); }");
}

#[test]
fn s007_a_struct_specialization_has_one_argument_per_parameter() {
    fails(&with_structs("const A: P[8, 9] = 0;"), S007, 1, 10);
    fails(&with_structs("const A: S[1] = 0;"), S007, 1, 10);
    assert_eq!(
        message(&with_structs("const A: S[1] = 0;")),
        "`S` takes 0 argument(s), but it has 1"
    );
    fails(&with_structs("const A: P[8][1] = 0;"), S007, 1, 10);
    fails(
        &with_structs(&fn_body("let t = P[1, 2];\nreturn p;")),
        S007,
        2,
        9,
    );
    fails(
        &with_structs(&fn_body("let t = E[0];\nreturn p;")),
        S007,
        2,
        9,
    );
}

#[test]
fn s007_a_struct_with_parameters_is_not_bare() {
    fails(&with_structs("const A: P = 0;"), S007, 1, 10);
    assert_eq!(
        message(&with_structs("const A: P = 0;")),
        "`P` takes 1 argument(s), but it has 0"
    );
    for body in [
        "let t = P;\nreturn p;",
        "let t = P(1, true);\nreturn p;",
        "let t = P();\nreturn p;",
    ] {
        fails(&with_structs(&fn_body(body)), S007, 2, 9);
    }
    fails("struct Q(comptime W: Nat) { a: Q }", S007, 1, 32);
}

#[test]
fn s007_a_struct_constructor_has_one_argument_per_field_or_none() {
    for body in [
        "let t = S(true, false);\nreturn p;",
        "let t = P[8](1);\nreturn p;",
        "let t = E(1);\nreturn p;",
    ] {
        fails(&with_structs(&fn_body(body)), S007, 2, 9);
    }
    assert_eq!(
        message(&with_structs(&fn_body("let t = P[8](1);\nreturn p;"))),
        "a struct constructor takes 0 or 2 argument(s), but it has 1"
    );
}

#[test]
fn s007_type_and_type_items_take_no_index() {
    fails("const A: Type[1] = Bool;", S007, 1, 10);
    fails("type A = UInt[8];\nconst B: A[2] = 0;", S007, 2, 10);
    fails("type A = UInt[8];\nconst B: Nat = A[2];", S007, 2, 16);
    // Only elaboration knows the type of a `type` item, so it checks the constructor.
    ok("type A = UInt[8];\nconst B: Nat = A(1, 2);");
    fails(&fn_body("return data_bits();"), S007, 2, 8);
    fails(&fn_body("return data_bits(Bool, Bool);"), S007, 2, 8);
}

#[test]
fn s007_in_the_parts_of_the_type_forms() {
    fails("struct Q(comptime W: UInt) { a: Bool }", S007, 1, 22);
    fails("struct Q { a: UInt }", S007, 1, 15);
    fails("type A = SInt;", S007, 1, 10);
    fails(&fn_body("type T = UInt;\nreturn p;"), S007, 2, 10);
    fails(&fn_body("let t = [UInt; 2];\nreturn p;"), S007, 2, 10);
    fails(&fn_body("let t = [Bool; 2][1];\nreturn p;"), S007, 2, 9);
    fails(
        &fn_body("let t = [Bool; 2](true, false);\nreturn p;"),
        S007,
        2,
        9,
    );
    ok(&fn_body(
        "let t = [Bool; 2]();\nlet u = [Bool; 2]([p, p]);\nreturn p;",
    ));
}

#[test]
fn s005_struct_arguments_and_array_lengths_are_static_positions() {
    fails(
        &with_structs(&mod_body("input a: Nat;\nlet x: P[a] = 0;")),
        S005,
        3,
        10,
    );
    fails(
        &with_structs(&mod_body("input a: Nat;\nlet t = P[a];")),
        S005,
        3,
        11,
    );
    fails(&mod_body("wire w: Nat;\nlet t = [Bool; w];"), S005, 3, 16);
    fails(&mod_body("wire w: Nat;\ntype T = [Bool; w];"), S005, 3, 17);
    fails(&mod_body("input a: Bool;\nlet t = Bool(a);"), S005, 3, 14);
    // The arguments of a struct constructor are no static positions.
    ok(&with_structs(&mod_body(
        "input a: Bool;\nlet t = S(a);\nlet u = P[W](0, a);",
    )));
}

// Receiver calls, `mut` formals, and `S008`. The cases come from the guards of
// `Silicon.Source.Test.Check` in Lean.

/// The body `s` of `f` starts on line 6. `xs` is a `let mut` local, `ys` a `mut` formal, and
/// `zs` a formal without a mark.
fn lists(s: &str) -> String {
    format!(
        "fn helper(comptime n: Int, mut xs: List[Int]) -> () {{}}\n\
         fn two(mut a: List[Int], mut b: List[Int]) -> () {{}}\n\
         fn pair(a: Int, b: Int) -> Int {{ return a; }}\n\
         fn f(zs: List[Int], mut ys: List[Int]) -> () {{\n\
         let mut xs = list(Int);\n{s}\n}}"
    )
}

#[test]
fn a_receiver_call_binds_its_receiver_to_the_first_parameter_without_comptime() {
    ok(&lists(
        "xs.push(1);\nlet n = xs.pop() + xs.len();\nlet s = n.str();",
    ));
    ok(&lists("xs.helper(1);\nys.helper(2);\nxs.two(ys);"));
    ok(&lists(
        "let a = 1.resize(UInt[8]);\nlet b = a.reinterpret(SInt[8]);",
    ));
    ok(&lists(
        "let c = (1 == 1).static_assert(\"m\");\n\"m\".error();",
    ));
    ok("comptime fn h(x: Nat, comptime y: Nat) -> Nat { return x; }\nconst A: Nat = 1.h(2);");
    ok(&lists("let t = Int.data_bits();"));
}

#[test]
fn s007_a_receiver_call_has_a_parameter_for_the_receiver_and_the_arity() {
    fails(&lists("let t = Int.list();"), S007, 6, 9);
    assert_eq!(
        message(&lists("let t = Int.list();")),
        "`list` has no parameter without `comptime` for the receiver"
    );
    fails(
        "fn c(comptime n: Nat) -> Nat { return n; }\nfn g(k: Nat) -> Nat { return k.c(); }",
        S007,
        2,
        30,
    );
    fails(&lists("xs.push();"), S007, 6, 1);
    assert_eq!(
        message(&lists("xs.push();")),
        "`push` takes 2 argument(s), but it has 1"
    );
    for (body, col) in [
        ("let a = xs.pop(1);", 9),
        ("let a = xs.len(1);", 9),
        ("let a = 1.pair(2, 3);", 9),
        ("let a = str(1, 2);", 9),
        ("let t = list();", 9),
    ] {
        fails(&lists(body), S007, 6, col);
    }
    fails(&lists("xs.helper();"), S007, 6, 1);
    fails(&lists("xs.helper(1, 2);"), S007, 6, 1);
    fails(&lists("push(xs);"), S007, 6, 1);
    fails("const L: List = 1;", S007, 1, 10);
    fails("const S: String[1] = 1;", S007, 1, 10);
}

/// The module body `s` starts on line 6.
fn regs2(s: &str) -> String {
    format!(
        "fn g(comptime n: Nat, x: Bool) -> Bool {{ return x; }}\n\
         comptime fn h(x: Nat) -> Nat {{ return x; }}\n\
         module M() {{\ninput a: Bool;\nreg r: UInt[4] = 0;\n{s}\n}}"
    )
}

#[test]
fn a_comptime_parameter_is_a_static_position_also_for_a_receiver_call() {
    ok(&regs2(
        "let y = a.g(1);\nlet z = str(r);\nlet w = r.resize(UInt[8]);",
    ));
    fails(&regs2("let y = a.g(r);"), S005, 6, 13);
    fails(&regs2("let y = a.h();"), S005, 6, 9);
    fails(&regs2("let y = a.resize(r);"), S005, 6, 18);
    fails(&regs2("let l = list(r);"), S005, 6, 14);
}

#[test]
fn s008_a_mut_actual_is_a_place_with_a_mutable_root() {
    ok(&lists(
        "push(xs, 1);\npush(ys, 2);\nlet mut t = (list(Int), 1);\nt.0.push(1);",
    ));
    ok(&lists(
        "let mut a = [list(Int)];\na[0].push(1);\nhelper(1, a[0]);",
    ));
    fails(&lists("zs.push(1);"), S008, 6, 1);
    assert_eq!(
        message(&lists("zs.push(1);")),
        "a `mut` actual has a `let mut` local or a `mut` formal as its root"
    );
    fails(&lists("push(zs, 1);"), S008, 6, 6);
    fails(&lists("let l = list(Int);\nl.push(1);"), S008, 7, 1);
    fails(&lists("list(Int).push(1);"), S008, 6, 1);
    assert_eq!(
        message(&lists("list(Int).push(1);")),
        "a `mut` actual is a place"
    );
    fails(&lists("helper(1, list(Int));"), S008, 6, 11);
    fails(
        &format!("const L: List[Int] = list(Int);\n{}", lists("L.push(1);")),
        S008,
        7,
        1,
    );
    fails(
        &lists("let a = (xs.pop() + 1).str();\npush(xs.len(), 1);"),
        S008,
        7,
        6,
    );
}

#[test]
fn s008_no_mutation_of_a_pending_root_in_its_window() {
    for (body, line, col) in [
        ("xs.helper(xs.pop());", 6, 11),
        ("xs[0] = xs.pop();", 6, 9),
        ("xs.push(xs.pop());", 6, 9),
        ("push(xs, xs.pop());", 6, 10),
        ("xs.push(pair(1, xs.pop()));", 6, 17),
        ("two(xs, xs);", 6, 9),
        ("xs.two(xs);", 6, 8),
        ("ys.two(ys);", 6, 8),
        ("xs[xs.pop()] = 1;", 6, 4),
        ("let mut a = [list(Int)];\na[a[0].pop()].push(1);", 7, 3),
        ("let mut t = (list(Int), 1);\nt.0.push(t.0.pop());", 7, 10),
    ] {
        fails(&lists(body), S008, line, col);
    }
    assert_eq!(
        message(&lists("xs.helper(xs.pop());")),
        "the root of this `mut` actual is pending in its window"
    );
}

#[test]
fn a_root_is_pending_only_in_its_window() {
    for body in [
        "helper(xs.pop(), xs);",
        "let a = pair(xs.pop(), xs.pop());",
        "xs.push(xs.len());",
        "xs[0] = xs.len();",
        "xs.push(ys.pop());\nys.push(xs.pop());",
        "xs.two(ys);\nys.two(xs);",
        "push(xs, 1);\npush(xs, 2);",
        "let mut a = [list(Int)];\na[a.len()].push(1);",
        "let h = push;\nh(zs, 1);",
    ] {
        ok(&lists(body));
    }
}

#[test]
fn a_mut_actual_changes_only_the_counter_of_its_root() {
    // A call with many `mut` actuals of distinct roots and a long run of calls on one root
    // pass in linear time: the check reads and changes one counter for each actual.
    let n = 20_000;
    let params: Vec<String> = (0..n).map(|i| format!("mut p{i}: List[Int]")).collect();
    let locals = (0..n).fold(String::new(), |mut text, i| {
        writeln!(text, "let mut l{i} = list(Int);").ok();
        text
    });
    let actuals: Vec<String> = (0..n).map(|i| format!("l{i}")).collect();
    ok(&format!(
        "fn big({}) -> () {{}}\nfn f() -> () {{\n{locals}big({});\n}}",
        params.join(", "),
        actuals.join(", ")
    ));
    let pushes = "xs.push(1);\n".repeat(n);
    ok(&lists(&pushes));
    // The last actual repeats the first root.
    let mut repeated = actuals.clone();
    repeated[n - 1] = "l0".to_owned();
    let col = 5 + actuals[..n - 1].iter().map(|a| a.len() + 2).sum::<usize>();
    let src = format!(
        "fn big({}) -> () {{}}\nfn f() -> () {{\n{locals}big({});\n}}",
        params.join(", "),
        repeated.join(", ")
    );
    assert_eq!(run(&src), Ok(Some((S008, n + 3, col))));
}

#[test]
fn at_one_position_s007_comes_before_s008_and_s005() {
    // The receiver `r` is a register: S005 in a static position. `mut` actual: S008.
    // The tie order is the walk order: the binding and the arity, the `mut` actual, then the
    // parts of the receiver.
    fails(
        "fn m(comptime n: Nat, mut x: Nat) -> () {}\nmodule M() {\nreg r: UInt[4] = 0;\nr.m();\n}",
        S007,
        4,
        1,
    );
    fails(
        "fn m(mut x: Nat) -> () {}\nmodule M() {\nreg r: UInt[4] = 0;\nr.m();\n}",
        S008,
        4,
        1,
    );
    fails(
        "fn m(comptime x: Nat, y: Nat) -> () {}\nmodule M() {\nreg r: UInt[4] = 0;\nr.m();\n}",
        S007,
        4,
        1,
    );
    fails(
        "fn m(comptime x: Nat, y: Nat) -> () {}\nmodule M() {\nreg r: UInt[4] = 0;\nm(r);\n}",
        S007,
        4,
        1,
    );
}

#[test]
fn a_window_that_reported_s008_still_ends_with_its_call() {
    let src = lists("two(xs, xs);\npush(xs, 1);\nxs.push(xs.pop());\nxs.push(2);");
    let resolved = resolve::resolve(parse::parse(&src).unwrap()).ok().unwrap();
    let Err(Failed::Errors(errors)) = check(resolved) else {
        panic!("expected errors");
    };
    let at: Vec<_> = errors.iter().map(|e| (e.code, e.pos.line)).collect();
    assert_eq!(at, [(S008, 6), (S008, 8)]);
}

#[test]
fn a_function_type_takes_no_index() {
    fails(
        &fn_body("let h = (fn () -> UInt)[8];\nreturn p;"),
        S007,
        2,
        9,
    );
    assert_eq!(
        message(&fn_body("let h = (fn () -> UInt)[8];\nreturn p;")),
        "a function type takes 0 argument(s), but it has 1"
    );
    fails("const A: (fn () -> UInt)[8] = 1;", S007, 1, 10);
    assert_eq!(
        message("const A: (fn () -> UInt)[8] = 1;"),
        "a function type takes 0 argument(s), but it has 1"
    );
    fails(
        &fn_body("let h = (fn () -> Bool)[1][2];\nreturn p;"),
        S007,
        2,
        9,
    );
    // A suffix after a function type belongs to its result type.
    ok(&fn_body("let h = fn () -> UInt[8];\nreturn p;"));
    ok("const A: fn () -> UInt[8] = 1;");
}

#[test]
fn the_parts_of_a_function_type_follow_the_rules_of_a_type() {
    fails("const A: fn (UInt) -> Bool = 1;", S007, 1, 14);
    fails("const A: fn () -> UInt = 1;", S007, 1, 19);
    fails(
        &fn_body("let h = fn (Bool, UInt) -> Bool;\nreturn p;"),
        S007,
        2,
        19,
    );
    fails(&fn_body("let h = fn () -> UInt;\nreturn p;"), S007, 2, 18);
    fails(
        &mod_body("reg r: UInt[8] = 0;\nlet h = fn (UInt[r]) -> Bool;"),
        S005,
        3,
        18,
    );
    fails(
        &mod_body("reg r: UInt[8] = 0;\nlet h: fn () -> UInt[r] = 1;"),
        S005,
        3,
        22,
    );
    fails(
        &mod_body("reg r: UInt[8] = 0;\ncomptime if (fn () -> UInt[r] == r) {}"),
        S005,
        3,
        28,
    );
}

#[test]
fn pass_5_decides_the_other_rules_of_function_values() {
    ok("fn g(mut x: Bool) -> Bool { return x; }\nfn f() -> Bool { let h = g; return h(true); }");
    ok(&fn_body("let h = f;\nreturn h(1, 2, 3);"));
    ok(&fn_body("let h = (fn () -> Bool)(1, 2, 3);\nreturn p;"));
    ok("fn f() -> Nat { let h = g; return 1; }\nfn g(comptime N: Nat) -> Nat { return N; }");
    ok(&fn_body("let h = len;\nreturn p;"));
    ok(&fn_body("let h = -fn () -> Bool;\nreturn p;"));
    ok(&fn_body("let h = f == f;\nreturn p;"));
    ok(&fn_body("return p == (fn () -> Bool == f);"));
}

/// The body of a `comptime fn`. The body starts on line 2.
fn ct_body(s: &str) -> String {
    format!("comptime fn f(x: Nat) -> Nat {{\n{s}\nreturn x;\n}}")
}

#[test]
fn s006_a_comptime_fn_has_no_memory_port_call() {
    fails(&ct_body("let r = read_port(x, 1, true);"), S006, 2, 9);
    fails(&ct_body("x.write_port(1, 2, true);"), S006, 2, 1);
    // The rule comes before the `S007` of the call at that position.
    fails(&ct_body("let r = read_port(x, 1);"), S006, 2, 9);
    fails(&ct_body("x.write_port(1, 2);"), S006, 2, 1);
    assert_eq!(
        message(&ct_body("x.write_port(1, 2);")),
        "a `comptime fn` has no memory port call"
    );
    ok(&mod_body(
        "mem m: [UInt[8]; 4];\nlet r = read_port(m, 0, true);\nm.write_port(0, 1, true);",
    ));
    ok(&fn_body("return read_port(p, p, p).valid;"));
}

#[test]
fn a_user_function_named_as_a_port_function_gets_no_memory_rule() {
    ok(&format!(
        "{}\ncomptime fn read_port(a: Nat) -> Nat {{ return a; }}",
        ct_body("let r = read_port(x);")
    ));
    ok(&format!(
        "{}\nfn write_port(a: Nat) -> Nat {{ return a; }}",
        ct_body("let r = x.write_port();")
    ));
    fails(
        &format!(
            "{}\nfn write_port(a: Nat) -> Nat {{ return a; }}",
            ct_body("let r = x.write_port(1);")
        ),
        S007,
        2,
        9,
    );
}

#[test]
fn s007_the_memory_port_functions_have_three_and_four_arguments() {
    let mem = |s: &str| mod_body(&format!("mem m: [UInt[8]; 4];\n{s}"));
    fails(&mem("let r = read_port(m, 0);"), S007, 3, 9);
    assert_eq!(
        message(&mem("let r = read_port(m, 0);")),
        "`read_port` takes 3 argument(s), but it has 2"
    );
    fails(&mem("write_port(m, 0, 1, true, 4);"), S007, 3, 1);
    fails(&mem("let r = m.read_port(0, true, 1);"), S007, 3, 9);
    fails(&mem("m.write_port(0, true);"), S007, 3, 1);
    ok(&mem(
        "let r = m.read_port(0, true);\nm.write_port(0, 1, true);",
    ));
}

#[test]
fn s007_the_prelude_struct_has_one_index_and_two_constructor_arguments() {
    ok(&fn_body(
        "let r: ReadResponse[Bool] = ReadResponse[Bool](p, p);\nreturn r.valid;",
    ));
    ok(&fn_body("return ReadResponse[Bool]().valid;"));
    fails(&fn_body("let r: ReadResponse = p;\nreturn p;"), S007, 2, 8);
    fails(&fn_body("let r = ReadResponse;\nreturn p;"), S007, 2, 9);
    fails(
        &fn_body("let r: ReadResponse[Bool, Bool] = p;\nreturn p;"),
        S007,
        2,
        8,
    );
    fails(
        &fn_body("let r = ReadResponse[Bool, Bool];\nreturn p;"),
        S007,
        2,
        9,
    );
    fails(
        &fn_body("let r = ReadResponse[Bool](p);\nreturn p;"),
        S007,
        2,
        9,
    );
    assert_eq!(
        message(&fn_body("let r = ReadResponse[Bool](p);\nreturn p;")),
        "a struct constructor takes 0 or 2 argument(s), but it has 1"
    );
    fails(
        &fn_body("let r = ReadResponse(p, p);\nreturn p;"),
        S007,
        2,
        9,
    );
}

#[test]
fn the_walk_skips_the_prelude_struct_and_a_user_struct_gets_the_check() {
    ok("");
    ok("fn f() -> Nat { return 1; }");
    // The same forms in a user struct give the error at their position.
    fails("struct ReadResponse { data: UInt }", S007, 1, 29);
}

#[test]
fn s007_diagnostic_takes_two_arguments() {
    ok(&fn_body("diagnostic(\"m\", p);\nreturn p;"));
    ok(&fn_body("p.diagnostic(p);\nreturn p;"));
    fails(&fn_body("diagnostic(\"m\");\nreturn p;"), S007, 2, 1);
    fails(&fn_body("diagnostic(\"m\", p, p);\nreturn p;"), S007, 2, 1);
    fails(&fn_body("p.diagnostic();\nreturn p;"), S007, 2, 1);
    assert_eq!(
        message(&fn_body("diagnostic(\"m\");\nreturn p;")),
        "`diagnostic` takes 2 argument(s), but it has 1"
    );
    // A user function of that name has its own arity.
    ok(&format!(
        "{}\nfn diagnostic(a: Bool) -> Bool {{ return a; }}",
        fn_body("diagnostic(p);\nreturn p;")
    ));
}

const OPS: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n";

#[test]
fn s007_a_variant_constructor_has_one_value_for_each_payload_type() {
    ok(&format!(
        "{OPS}fn f(x: UInt[8]) -> Op {{ let a = Op::Add(); return Op::Load(x); }}"
    ));
    ok(&format!("{OPS}fn f(x: UInt[8]) -> Op {{ return Op(x); }}"));
    let two = format!("{OPS}fn f(x: UInt[8]) -> Op {{ return Op::Load(x, x); }}");
    fails(&two, S007, 2, 33);
    assert_eq!(
        message(&two),
        "the variant `Op::Load` has 1 payload value(s), but the constructor has 2; pass one \
         value for each payload type"
    );
    fails(
        &format!("{OPS}fn f() -> Op {{ return Op::Load; }}"),
        S007,
        2,
        23,
    );
    fails(
        &format!("{OPS}fn f() -> Op {{ return Op::Add(1); }}"),
        S007,
        2,
        23,
    );
    fails(
        &format!("{OPS}fn f() -> Op[1] {{ return Op(); }}"),
        S007,
        2,
        11,
    );
    fails(
        "enum E: UInt[1] { A = 0 }\nconst C: E = E::A(E::A);",
        S007,
        2,
        14,
    );
}

#[test]
fn a_payload_value_in_a_static_position_is_static() {
    fails(
        &format!("{OPS}module M() {{\ninput a: UInt[8];\nreg q: Op = Op::Load(a);\n}}"),
        S005,
        4,
        22,
    );
    ok(&format!(
        "{OPS}module M() {{\ninput a: UInt[8];\nlet q = Op::Load(a);\n}}"
    ));
}

#[test]
fn the_tag_value_of_a_variant_is_a_static_position_also_in_an_unused_enum() {
    fails("enum E: UInt[2] { A = UInt[2][1] }", S007, 1, 23);
}

// Patterns (slice 3, section 5.6). The cases come from the `#guard` lines of
// `Silicon.Source.Test.Check` in Lean.

const PAIR: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n";

/// A function `f` whose `return` is a `match` with the arms `arms`, on line 3 from column 20.
fn arms(arms: &str) -> String {
    format!("{PAIR}fn f(x: Op) -> UInt[8] {{\nreturn match (x) {{ {arms} }};\n}}")
}

#[test]
fn s007_a_variant_pattern_has_a_binder_for_each_payload_value() {
    ok(&arms(
        "Op::Add() => 0, Op::Load(_) => 0, Op::Pair(b, w) => 0, _ => 0",
    ));
    let src = arms("Op::Add => 0, Op::Pair(a) => 0, _ => 0");
    fails(&src, S007, 3, 34);
    assert_eq!(
        message(&src),
        "the variant `Pair` has 2 payload value(s), but the pattern has 1; write one binder or \
         `_` for each payload value"
    );
    fails(&arms("Op::Load => 0, _ => 0"), S007, 3, 20);
    let src = arms("Op::Add(_) => 0, _ => 0");
    fails(&src, S007, 3, 20);
    assert_eq!(
        message(&src),
        "the variant `Add` has 0 payload value(s), but the pattern has 1; write one binder or \
         `_` for each payload value"
    );
}

#[test]
fn s007_the_first_error_by_position_wins_in_a_match() {
    fails(&arms("Op::Load => Op::Add(1), _ => 0"), S007, 3, 20);
    fails(&arms("Op::Add => Op::Add(1), Op::Load => 0"), S007, 3, 31);
}

#[test]
fn a_match_is_a_static_position_and_a_binder_is_a_plain_local() {
    ok(&format!(
        "{PAIR}module M() {{\nreg r: UInt[8] = match (Op::Load(1)) {{ Op::Load(v) => v, _ => 0 }};\n}}"
    ));
    fails(
        &format!("{PAIR}module M() {{\ninput a: Op;\nreg r: UInt[8] = match (a) {{ _ => 0 }};\n}}"),
        S005,
        4,
        25,
    );
    fails(
        &format!(
            "{PAIR}module M() {{\ninput a: UInt[8];\nreg r: UInt[8] = match (Op::Add) {{ _ => a }};\n}}"
        ),
        S005,
        4,
        41,
    );
    ok(&format!(
        "{PAIR}module M() {{\ninput a: Op;\nlet r = match (a) {{ Op::Load(v) => v, _ => 0 }};\n}}"
    ));
    fails(
        &format!(
            "{PAIR}fn g(mut y: UInt[8]) -> UInt[8] {{ return y; }}\nfn f(x: Op) -> UInt[8] {{ return match (x) {{ Op::Load(v) => g(v), _ => 0 }}; }}"
        ),
        S008,
        3,
        62,
    );
}
