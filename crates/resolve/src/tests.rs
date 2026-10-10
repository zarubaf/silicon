use crate::{Code, Decl, Failed, Kind, Prelude, Resolved, Target, resolve};
use parse::ast::Pos;

fn pos(line: usize, col: usize) -> Pos {
    Pos { line, col }
}

fn run(src: &str) -> Result<Resolved, Failed> {
    resolve(parse::parse(src).unwrap_or_else(|e| panic!("{e}")))
}

fn ok(src: &str) -> Resolved {
    match run(src) {
        Ok(resolved) => resolved,
        Err(Failed::Names(errors)) => panic!("unexpected {errors:?}"),
        Err(Failed::Parse(_)) => panic!("the source must parse"),
        Err(Failed::Stack(e)) => panic!("{e}"),
    }
}

/// The errors as code, line, and column.
fn errors(src: &str) -> Vec<(Code, usize, usize)> {
    match run(src) {
        Err(Failed::Names(errors)) => errors
            .iter()
            .map(|e| (e.code, e.pos.line, e.pos.col))
            .collect(),
        Err(Failed::Parse(_)) => panic!("the source must parse"),
        Err(Failed::Stack(e)) => panic!("{e}"),
        Ok(_) => Vec::new(),
    }
}

fn decl_at(resolved: &Resolved, at: Pos) -> &Decl {
    match resolved.target(at) {
        Some(Target::Decl(id)) => resolved.decl(id),
        other => panic!("expected a declaration at {at:?}, got {other:?}"),
    }
}

const S002: Code = Code::S002;
const S003: Code = Code::S003;

#[test]
fn a_valid_file_resolves_every_name() {
    let r = ok("const W: Nat = 8;\n\
                fn inc(x: UInt[W]) -> UInt[W] { return x; }\n\
                module M(comptime N: Nat) {\n\
                \x20 input a: UInt[W];\n\
                \x20 output y: UInt[W];\n\
                \x20 y := inc(a);\n\
                }\n");
    assert_eq!(r.decl(r.item("W").unwrap()).kind, Kind::Const);
    assert_eq!(r.decl(r.item("inc").unwrap()).kind, Kind::Fn);
    assert_eq!(r.decl(r.item("M").unwrap()).kind, Kind::Module);
    assert!(r.item("missing").is_none());
    // `Nat` at 1:10 is the prelude. `UInt` and `W` in `UInt[W]` on line 2.
    assert_eq!(r.target(pos(1, 10)), Some(Target::Prelude(Prelude::Nat)));
    assert_eq!(r.target(pos(2, 11)), Some(Target::Prelude(Prelude::UInt)));
    assert_eq!(decl_at(&r, pos(2, 16)).name, "W");
    // The use of `inc` points to the item, and the declaration points to itself.
    assert_eq!(decl_at(&r, pos(6, 8)).kind, Kind::Fn);
    assert_eq!(decl_at(&r, pos(2, 4)).kind, Kind::Fn);
    assert_eq!(decl_at(&r, pos(6, 12)).kind, Kind::Input);
    assert_eq!(decl_at(&r, pos(6, 3)).kind, Kind::Output);
    assert_eq!(r.ast().len(), 3);
    assert_eq!(r.depth(), parse::DEFAULT_SYNTAX_DEPTH);
}

#[test]
fn items_are_visible_before_their_declaration() {
    ok("const A: Nat = f();\nfn f() -> Nat { return B; }\nconst B: Nat = 1;\n");
}

#[test]
fn a_parse_error_is_not_resolved() {
    assert!(matches!(run("const A: Nat = ;"), Err(Failed::Parse(_))));
}

// S002

#[test]
fn a_second_item_with_a_name_is_s002_at_its_name() {
    assert_eq!(
        errors("const A: Nat = 1;\nconst  A: Nat = 2;\n"),
        [(S002, 2, 8)]
    );
    assert_eq!(
        errors("fn f() -> Nat { return 1; }\nmodule f() {}\n"),
        [(S002, 2, 8)]
    );
}

#[test]
fn each_later_declaration_of_a_name_is_s002() {
    let src = "const A: Nat = 1;\nconst A: Nat = 2;\nconst A: Nat = 3;\n";
    assert_eq!(errors(src), [(S002, 2, 7), (S002, 3, 7)]);
}

#[test]
fn parameters_cannot_repeat() {
    assert_eq!(
        errors("fn f(a: Nat, b: Nat, a: Nat) -> Nat { return a; }\n"),
        [(S002, 1, 22)]
    );
}

#[test]
fn a_domain_and_a_parameter_share_a_scope() {
    assert_eq!(
        errors("module M(comptime d: Nat) domains(d) {}\n"),
        [(S002, 1, 35)]
    );
}

#[test]
fn the_body_shares_the_scope_of_the_parameters() {
    assert_eq!(
        errors("fn f(a: Nat) -> Nat {\n  let a = 1;\n  return a;\n}\n"),
        [(S002, 2, 7)]
    );
}

#[test]
fn all_kinds_of_local_declaration_share_one_namespace() {
    let src = "module M() {\n  input a: Bool;\n  output a: Bool;\n  wire a: Bool;\n  \
               reg a: Bool = false;\n  let a = 1;\n}\n";
    assert_eq!(
        errors(src),
        [(S002, 3, 10), (S002, 4, 8), (S002, 5, 7), (S002, 6, 7)]
    );
}

#[test]
fn an_instance_name_is_a_local() {
    let src = "module C() {}\nmodule M() {\n  wire u: Bool;\n  instance u = C();\n}\n";
    assert_eq!(errors(src), [(S002, 4, 12)]);
}

#[test]
fn a_loop_variable_shares_the_scope_of_its_body() {
    let src = "module M() {\n  comptime for i in 0..2 {\n    let i = 1;\n  }\n}\n";
    assert_eq!(errors(src), [(S002, 3, 9)]);
}

#[test]
fn a_block_can_shadow_an_outer_local() {
    ok(
        "fn f(a: Nat) -> Nat {\n  { let a = 1; }\n  comptime if (true) { let a = 2; } else { let a = 3; }\n  \
        comptime for a in 0..2 { let b = a; }\n  return a;\n}\n",
    );
}

#[test]
fn a_local_can_shadow_an_item() {
    let r = ok("const A: Nat = 1;\nfn f() -> Nat {\n  let A = 2;\n  return A;\n}\n");
    assert_eq!(decl_at(&r, pos(4, 10)).kind, Kind::Local);
}

#[test]
fn a_declaration_can_shadow_a_prelude_name() {
    let r = ok("const Nat: Bool = true;\nfn resize() -> Bool { return Nat; }\n");
    assert_eq!(decl_at(&r, pos(2, 30)).kind, Kind::Const);
    ok("fn f(UInt: Nat) -> Nat { let error = UInt; return error; }\n");
}

#[test]
fn a_shadowed_prelude_name_has_the_kind_of_the_declaration() {
    // The constant `Bool` is no type.
    assert_eq!(
        errors("const Bool: Nat = 1;\nconst A: Bool = true;\n"),
        [(S003, 2, 10)]
    );
    // The prelude function `resize` is no value, and the local `resize` is no callee.
    assert_eq!(
        errors("fn f() -> Nat {\n  let resize = 1;\n  return resize(UInt[8], 1);\n}\n"),
        [(S003, 3, 10)]
    );
}

// S003

#[test]
fn an_unknown_name_is_s003_at_the_name() {
    assert_eq!(errors("const A: Nat = x + 1;\n"), [(S003, 1, 16)]);
    assert_eq!(errors("const A: Natt = 1;\n"), [(S003, 1, 10)]);
}

#[test]
fn a_name_of_a_later_slice_prelude_is_s003() {
    assert_eq!(errors("const A: List = 1;\n"), [(S003, 1, 10)]);
    assert_eq!(errors("const A: Nat = len(1);\n"), [(S003, 1, 16)]);
    assert_eq!(
        errors("module M() {\n  reg r: Reg[Bool] = false;\n}\n"),
        [(S003, 2, 10)]
    );
}

#[test]
fn a_local_is_visible_only_after_its_declaration() {
    let src = "fn f() -> Nat {\n  let a = b;\n  let b = 1;\n  return a;\n}\n";
    assert_eq!(errors(src), [(S003, 2, 11)]);
    // The value of a declaration cannot use the name that it declares.
    assert_eq!(
        errors("fn f() -> Nat {\n  let a = a;\n  return a;\n}\n"),
        [(S003, 2, 11)]
    );
    assert_eq!(
        errors("module M() {\n  reg r: Bool = r;\n}\n"),
        [(S003, 2, 17)]
    );
}

#[test]
fn a_local_is_not_visible_after_its_block() {
    assert_eq!(
        errors("fn f() -> Nat {\n  { let a = 1; }\n  return a;\n}\n"),
        [(S003, 3, 10)]
    );
    assert_eq!(
        errors("fn f() -> Nat {\n  comptime for i in 0..2 { }\n  return i;\n}\n"),
        [(S003, 3, 10)]
    );
    assert_eq!(
        errors("fn f() -> Nat {\n  comptime for i in 0..i { }\n  return 1;\n}\n"),
        [(S003, 2, 24)]
    );
}

#[test]
fn a_parameter_type_sees_only_the_earlier_parameters() {
    ok("fn f(comptime W: Nat, x: UInt[W]) -> UInt[W] { return x; }\n");
    assert_eq!(
        errors("fn f(x: UInt[W], comptime W: Nat) -> Nat { return 1; }\n"),
        [(S003, 1, 14)]
    );
}

#[test]
fn a_type_position_needs_a_type() {
    assert_eq!(
        errors("const A: Nat = 1;\nconst B: A = 1;\n"),
        [(S003, 2, 10)]
    );
    assert_eq!(errors("fn f(x: Nat) -> x { return 1; }\n"), [(S003, 1, 17)]);
    assert_eq!(
        errors("module M() {\n  wire w: UInt[8];\n  wire v: w[1];\n}\n"),
        [(S003, 3, 11)]
    );
    // A type family in an expression is indexed by a type name.
    assert_eq!(
        errors("const A: Nat = 1;\nconst B: Nat = A[1];\n"),
        [(S003, 2, 16)]
    );
}

#[test]
fn a_value_position_needs_a_value() {
    assert_eq!(
        errors("fn f() -> Nat { return 1; }\nconst A: Nat = f;\n"),
        [(S003, 2, 16)]
    );
    assert_eq!(errors("const A: Nat = UInt;\n"), [(S003, 1, 16)]);
    assert_eq!(
        errors("module C() {}\nconst A: Nat = C;\n"),
        [(S003, 2, 16)]
    );
    assert_eq!(
        errors("module M() domains(d) {\n  wire w: Bool;\n  w := d;\n}\n"),
        [(S003, 3, 8)]
    );
}

#[test]
fn a_callee_needs_a_function_or_a_type() {
    ok("fn f(x: Nat) -> Nat { return x; }\n\
        const A: UInt[8] = UInt[8](f(3));\n\
        const B: Bool = Bool(true);\n\
        const C: Nat = resize(UInt[8], A);\n");
    assert_eq!(
        errors("const A: Nat = 1;\nconst B: Nat = A(2);\n"),
        [(S003, 2, 16)]
    );
}

#[test]
fn an_instance_needs_a_module() {
    let src = "fn f() -> Nat { return 1; }\nmodule M() {\n  instance u = f();\n}\n";
    assert_eq!(errors(src), [(S003, 3, 16)]);
    assert_eq!(
        errors("module M() {\n  instance u = N();\n}\n"),
        [(S003, 2, 16)]
    );
    // A module can instantiate itself or a later module: the check is for the name only.
    ok("module M() {\n  instance u = N();\n}\nmodule N() {}\n");
}

#[test]
fn an_assignment_target_needs_a_value() {
    assert_eq!(
        errors("fn f() -> Nat { return 1; }\nmodule M() {\n  f := 1;\n}\n"),
        [(S003, 3, 3)]
    );
    assert_eq!(
        errors("module M() {\n  let a = 1;\n  b = a;\n}\n"),
        [(S003, 3, 3)]
    );
}

#[test]
fn a_selected_field_is_not_a_name() {
    ok("module C() { output q: Bool; }\n\
        module M() {\n  instance u = C();\n  wire w: Bool;\n  w := u.q;\n}\n");
}

// Pass order and report order

#[test]
fn errors_are_in_position_order() {
    assert_eq!(
        errors("const A: Nat = y;\nconst B: Nat = x;\nconst C: Nat = z;\n"),
        [(S003, 1, 16), (S003, 2, 16), (S003, 3, 16)]
    );
    // A name in a type sorts with the names in the values.
    assert_eq!(
        errors("fn f(a: T, b: Nat) -> U { return c; }\n"),
        [(S003, 1, 9), (S003, 1, 23), (S003, 1, 34)]
    );
}

#[test]
fn pass_2_errors_come_before_pass_3_errors() {
    // The unknown name is earlier, but only the duplicate is reported.
    let src = "const A: Nat = x;\nconst B: Nat = 1;\nconst B: Nat = 2;\n";
    assert_eq!(errors(src), [(S002, 3, 7)]);
    // A name that follows a duplicate declaration still resolves.
    let src = "const B: Nat = 1;\nconst B: Nat = 2;\nconst C: Nat = B;\n";
    assert_eq!(errors(src), [(S002, 2, 7)]);
}

#[test]
fn pass_1_errors_come_before_pass_2_errors() {
    assert!(matches!(
        run("const A: Nat = 1;\nconst A: Nat = ;\n"),
        Err(Failed::Parse(_))
    ));
}

// Stack safety

#[test]
fn a_deep_valid_input_resolves_on_a_test_thread() {
    // The default syntax depth is 4096. The calls give the depth of brackets and of height.
    let n = 3000;
    let calls = format!("{}1{}", "f(".repeat(n), ")".repeat(n));
    let chain = vec!["a"; n].join(" + ");
    let blocks = format!("{}{}", "{ ".repeat(n - 4), "}".repeat(n - 4));
    let src = format!(
        "fn f(a: Nat) -> Nat {{ return a; }}\n\
         const A: Nat = {calls};\n\
         fn g(a: Nat) -> Nat {{ return {chain}; }}\n\
         module M() {blocks}\n"
    );
    let r = ok(&src);
    assert_eq!(r.ast().len(), 4);
    assert_eq!(r.decl(r.item("f").unwrap()).kind, Kind::Fn);
    drop(r);
}

#[test]
fn a_deep_nesting_with_shadowing_resolves_in_linear_time() {
    let n = 2000;
    let src = format!(
        "fn f(a: Nat) -> Nat {{\n{}return a;\n{}}}\n",
        "{ let a = 1;\n".repeat(n),
        "}\n".repeat(n)
    );
    ok(&src);
}
