// SPDX-License-Identifier: Apache-2.0
use crate::{Code, Decl, Failed, Kind, Prelude, Resolved, Target, resolve};
use parse::ast::{Expr, Ident, Item, NodeId, Param, Pos, Stmt, TypeExpr};
use std::collections::BTreeMap;

fn pos(line: usize, col: usize) -> Pos {
    Pos { line, col }
}

/// The id of each name node by its position, so that a test names a node by its position.
#[derive(Default)]
struct Ids(BTreeMap<Pos, NodeId>);

impl Ids {
    fn of_items(items: &[Item]) -> Ids {
        let mut ids = Ids::default();
        for item in items {
            match item {
                Item::Const {
                    name, ty, value, ..
                } => {
                    ids.ident(name);
                    ids.ty(ty);
                    ids.expr(value);
                }
                Item::Fn {
                    name,
                    params,
                    ret,
                    body,
                    ..
                } => {
                    ids.ident(name);
                    ids.params(params);
                    ids.ty(ret);
                    ids.stmts(body);
                }
                Item::Module {
                    name,
                    params,
                    domains,
                    body,
                    ..
                } => {
                    ids.ident(name);
                    ids.params(params);
                    for domain in domains.iter().flatten() {
                        ids.ident(domain);
                    }
                    ids.stmts(body);
                }
                Item::Struct {
                    name,
                    params,
                    fields,
                    ..
                } => {
                    ids.ident(name);
                    ids.params(params);
                    for field in fields {
                        ids.ident(&field.name);
                        ids.ty(&field.ty);
                    }
                }
                Item::Alias { name, ty, .. } => {
                    ids.ident(name);
                    ids.ty(ty);
                }
            }
        }
        ids
    }

    fn of_expr(expr: &Expr) -> Ids {
        let mut ids = Ids::default();
        ids.expr(expr);
        ids
    }

    /// The id of the name node at a position.
    fn at(&self, at: Pos) -> NodeId {
        *self
            .0
            .get(&at)
            .unwrap_or_else(|| panic!("no name node at {at:?}"))
    }

    fn add(&mut self, at: Pos, id: NodeId) {
        assert!(self.0.insert(at, id).is_none(), "two name nodes at {at:?}");
    }

    fn ident(&mut self, name: &Ident) {
        self.add(name.pos, name.id);
    }

    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.ident(&param.name);
            self.ty(&param.ty);
        }
    }

    fn stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            match stmt {
                Stmt::Local {
                    name, ty, value, ..
                } => {
                    self.ident(name);
                    if let Some(ty) = ty {
                        self.ty(ty);
                    }
                    self.expr(value);
                }
                Stmt::Assign { target, value, .. } | Stmt::Connect { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                Stmt::Reg { name, ty, init, .. } => {
                    self.ident(name);
                    self.ty(ty);
                    self.expr(init);
                }
                Stmt::Wire { name, ty, .. }
                | Stmt::Input { name, ty, .. }
                | Stmt::Output { name, ty, .. }
                | Stmt::Alias { name, ty, .. } => {
                    self.ident(name);
                    self.ty(ty);
                }
                Stmt::Inst {
                    name, module, args, ..
                } => {
                    self.ident(name);
                    self.ident(module);
                    self.exprs(args);
                }
                Stmt::Ret { value, .. } => {
                    if let Some(value) = value {
                        self.expr(value);
                    }
                }
                Stmt::CtIf { cond, yes, no, .. } => {
                    self.expr(cond);
                    self.stmts(yes);
                    if let Some(no) = no {
                        self.stmts(no);
                    }
                }
                Stmt::CtFor {
                    var, lo, hi, body, ..
                } => {
                    self.ident(var);
                    self.expr(lo);
                    self.expr(hi);
                    self.stmts(body);
                }
                Stmt::Block { body, .. } => self.stmts(body),
                Stmt::Expr { value, .. } => self.expr(value),
            }
        }
    }

    fn ty(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Name { pos, id, .. } => self.add(*pos, *id),
            TypeExpr::Index { base, args, .. } => {
                self.ty(base);
                self.exprs(args);
            }
            TypeExpr::Unit { .. } => {}
            TypeExpr::Tuple { elems, .. } => {
                for elem in elems {
                    self.ty(elem);
                }
            }
            TypeExpr::Array { elem, len, .. } => {
                self.ty(elem);
                self.expr(len);
            }
        }
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        for expr in exprs {
            self.expr(expr);
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } | Expr::Unit { .. } => {}
            Expr::Name { pos, id, .. } => self.add(*pos, *id),
            Expr::Unary { arg, .. } => self.expr(arg),
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(cond);
                self.expr(yes);
                self.expr(no);
            }
            Expr::Call { callee, args, .. } => {
                self.expr(callee);
                self.exprs(args);
            }
            Expr::Index { base, args, .. } => {
                self.expr(base);
                self.exprs(args);
            }
            Expr::Field { base, field, .. } => {
                self.expr(base);
                self.ident(field);
            }
            Expr::Select { base, .. } => self.expr(base),
            Expr::ArrayType { elem, len, .. } => {
                self.ty(elem);
                self.expr(len);
            }
            Expr::Tuple { elems, .. } | Expr::Array { elems, .. } => self.exprs(elems),
        }
    }
}

/// What the name node at a position of the file points to.
fn target_at(resolved: &Resolved, at: Pos) -> Option<Target> {
    resolved.target(Ids::of_items(resolved.ast()).at(at))
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
    match target_at(resolved, at) {
        Some(Target::Decl(id)) => resolved.decl(id),
        other => panic!("expected a declaration at {at:?}, got {other:?}"),
    }
}

fn decl_at_use(resolved: &Resolved, at: Pos) -> Kind {
    match target_at(resolved, at) {
        Some(Target::Decl(id)) => resolved.decl(id).kind,
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
    assert_eq!(
        target_at(&r, pos(1, 10)),
        Some(Target::Prelude(Prelude::Nat))
    );
    assert_eq!(
        target_at(&r, pos(2, 11)),
        Some(Target::Prelude(Prelude::UInt))
    );
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
fn a_shadowed_prelude_type_is_no_type() {
    // The constant `UInt` is no type.
    assert_eq!(
        errors("const UInt: Nat = 8;\nconst A: UInt[8] = 0;\n"),
        [(S003, 2, 10)]
    );
    assert_eq!(
        errors("fn f(Bool: Nat, x: Bool) -> Nat { return x; }\n"),
        [(S003, 1, 20)]
    );
    ok("fn f(p: Bool) -> Bool {\n  { let Bool = 1; }\n  let x: Bool = p;\n  return x;\n}\n");
}

#[test]
fn an_unknown_name_is_s003_at_the_name() {
    assert_eq!(errors("const A: Nat = x + 1;\n"), [(S003, 1, 16)]);
    assert_eq!(errors("const A: Natt = 1;\n"), [(S003, 1, 10)]);
}

#[test]
fn a_name_of_a_later_slice_prelude_is_s003() {
    assert_eq!(errors("const A: Wire = 1;\n"), [(S003, 1, 10)]);
    assert_eq!(errors("const A: Nat = read(1);\n"), [(S003, 1, 16)]);
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
fn only_a_module_is_wrong_in_an_expression() {
    // A function, a type, and a domain are names in an expression.
    ok(
        "fn g() -> Nat { return 1; }\nconst A: Nat = g;\nconst B: Nat = UInt;\n\
        module M() domains(d) {\n  let x = d;\n  let y = resize;\n}\n",
    );
    assert_eq!(
        errors("module A() {}\nmodule B() {\n  let x = A;\n}\n"),
        [(S003, 3, 11)]
    );
    assert_eq!(
        errors("module A() {}\nconst N: Nat = A();\n"),
        [(S003, 2, 16)]
    );
}

#[test]
fn a_type_position_needs_a_prelude_type() {
    assert_eq!(
        errors("const N: Nat = 1;\nconst M: N = 1;\n"),
        [(S003, 2, 10)]
    );
    assert_eq!(
        errors("fn g() -> Nat { return 1; }\nconst M: g[1] = 1;\n"),
        [(S003, 2, 10)]
    );
    assert_eq!(
        errors("fn f(x: resize) -> Bool { return true; }\n"),
        [(S003, 1, 9)]
    );
}

#[test]
fn the_module_of_an_instance_needs_a_module_item() {
    let g = "fn g() -> Nat { return 1; }\nmodule M() {\n  instance u = g();\n}\n";
    assert_eq!(errors(g), [(S003, 3, 16)]);
    assert_eq!(
        errors("module M() {\n  instance u = resize();\n}\n"),
        [(S003, 2, 16)]
    );
    assert_eq!(
        errors("module M() {\n  instance u = N();\n}\n"),
        [(S003, 2, 16)]
    );
    assert_eq!(
        errors("module M() {\n  let N = 1;\n  instance u = N();\n}\n"),
        [(S003, 3, 16)]
    );
    ok("module M() {\n  instance u = N();\n}\nmodule N() {}\n");
    ok("module A() { instance a = A(); }\n");
}

#[test]
fn a_module_without_a_domains_clause_has_the_domain_clock() {
    let r = ok("module M() {\n  let c = clock;\n}\n");
    assert_eq!(decl_at_use(&r, pos(2, 11)), Kind::Domain);
    assert_eq!(
        errors("module M() {\n  wire clock: Bool;\n}\n"),
        [(S002, 2, 8)]
    );
    assert_eq!(
        errors("module M(comptime clock: Nat) {}\n"),
        [(S002, 1, 19)]
    );
    // An explicit clause replaces the default.
    ok("module M() domains(clock) {\n  let c = clock;\n}\n");
    assert_eq!(
        errors("module M() domains(clock) {\n  wire clock: Bool;\n}\n"),
        [(S002, 2, 8)]
    );
    assert_eq!(
        errors("module M() domains() {\n  let c = clock;\n}\n"),
        [(S003, 2, 11)]
    );
    ok("module M() domains() {\n  wire clock: Bool;\n}\n");
}

#[test]
fn the_name_after_a_dot_is_not_looked_up() {
    ok("module B() {}\nmodule A() { instance b = B(); let y = b.zzz; }\n");
    assert_eq!(
        errors("module M(comptime W: Nat) {\n  let y = u.a;\n  instance u = M(1);\n}\n"),
        [(S003, 2, 11)]
    );
}

#[test]
fn the_message_of_a_later_slice_name_names_the_slice() {
    let message = |src: &str| match run(src) {
        Err(Failed::Names(errors)) => errors[0].message.clone(),
        _ => panic!("expected an error"),
    };
    assert_eq!(
        message("fn f(x: TypeInfo) -> Bool { return true; }\n"),
        "`TypeInfo` is not supported yet; it comes in slice 4"
    );
    assert_eq!(
        message("module M() {\n  reg r: Reg[Bool] = 0;\n}\n"),
        "`Reg` is not supported yet; it comes in slice 3"
    );
    assert_eq!(message("const A: Foo = 1;\n"), "`Foo` is not declared");
    ok("const Wire: Nat = 1;\nconst N: Nat = Wire;\n");
}

#[test]
fn a_nested_scope_shadows_as_in_lean() {
    let ret = |src: &str| {
        let r = ok(src);
        let Some(parse::ast::Item::Fn { body, .. }) = r.ast().first() else {
            panic!("expected a function");
        };
        let Some(parse::ast::Stmt::Ret {
            value: Some(parse::ast::Expr::Name { pos, .. }),
            ..
        }) = body.last()
        else {
            panic!("expected a return of a name");
        };
        let target = target_at(&r, *pos).unwrap();
        match target {
            Target::Decl(id) => (r.decl(id).kind, r.decl(id).pos),
            Target::Prelude(_) => panic!("prelude"),
        }
    };
    let fn_decl = |l, c| (Kind::Fn, pos(l, c));
    assert_eq!(
        ret("fn f() -> Nat { let x = 2; return x; }\nconst x: Nat = 1;\n"),
        (Kind::Local, pos(1, 21))
    );
    assert_eq!(
        ret("fn f() -> Nat { return x; }\nconst x: Nat = 1;\n"),
        (Kind::Const, pos(2, 7))
    );
    assert_eq!(
        ret("fn f(a: Nat) -> Nat { { let a = 1; } return a; }\n"),
        (Kind::Param, pos(1, 6))
    );
    assert_eq!(
        ret("fn f() -> Nat { return resize; }\nfn resize(x: Nat) -> Nat { return x; }\n"),
        fn_decl(2, 4)
    );
    ok(
        "fn f(p: Bool) -> Bool {\n  let x = 1;\n  comptime for x in 0..x { let y = x; }\n  return p;\n}\n",
    );
    ok(
        "fn f(p: Bool) -> Bool {\n  comptime if (p) { let x = 1; } else { let x = 2; }\n  return p;\n}\n",
    );
}

#[test]
fn a_local_has_its_own_value_out_of_scope() {
    assert_eq!(
        errors("fn f(p: Bool) -> Bool {\n  comptime if (p) { let a = 1; }\n  return a;\n}\n"),
        [(S003, 3, 10)]
    );
    assert_eq!(
        errors("module M(comptime W: Nat) {\n  w := 1;\n  wire w: Bool;\n}\n"),
        [(S003, 2, 3)]
    );
    assert_eq!(
        errors("fn f(x: UInt[x]) -> Bool { return true; }\n"),
        [(S003, 1, 14)]
    );
    assert_eq!(
        errors("module M(comptime A: UInt[B], comptime B: Nat) {}\n"),
        [(S003, 1, 27)]
    );
}

#[test]
fn an_earlier_s002_wins_over_an_earlier_s003() {
    assert_eq!(
        errors("const A: Foo = 1;\nmodule M() {\nwire a: Bool;\nwire a: Bool;\n}\n"),
        [(S002, 4, 6)]
    );
    assert_eq!(
        errors("fn f() -> Bool { return q; }\nconst f: Nat = 1;\n"),
        [(S002, 2, 7)]
    );
    assert_eq!(
        errors("fn f(p: Bool) -> Bool {\n  return a + b;\n}\n"),
        [(S003, 2, 10), (S003, 2, 14)]
    );
}

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

/// Resolves `expr` in the file scope of `src`.
fn run_expr(src: &str, expr: &str) -> Result<crate::ResolvedExpr, Vec<(Code, usize, usize)>> {
    let file = ok(src);
    let expr = parse::parse_expr(expr, parse::DEFAULT_SYNTAX_DEPTH)
        .unwrap()
        .unwrap_or_else(|e| panic!("the expression must parse: {e:?}"));
    crate::resolve_expr(&file, expr).unwrap().map_err(|errors| {
        errors
            .iter()
            .map(|e| (e.code, e.pos.line, e.pos.col))
            .collect()
    })
}

#[test]
fn an_expression_resolves_in_the_file_scope() {
    let src = "const A: Nat = 1;\ncomptime fn f(n: Nat) -> Nat { return n; }\nmodule M() { }";
    let file = ok(src);
    let resolved = run_expr(src, "f(A) + UInt[8](1)").unwrap();
    let ids = Ids::of_expr(resolved.expr());
    let kind = |at: Pos| match resolved.target(ids.at(at)) {
        Some(Target::Decl(id)) => file.decl(id).kind,
        other => panic!("{other:?}"),
    };
    assert_eq!(kind(pos(1, 1)), Kind::Fn);
    assert_eq!(kind(pos(1, 3)), Kind::Const);
    assert_eq!(
        resolved.target(ids.at(pos(1, 8))),
        Some(Target::Prelude(Prelude::UInt))
    );
    // A local of an item is not in the file scope, and a module is not a value.
    assert_eq!(run_expr(src, "n").err(), Some(vec![(S003, 1, 1)]));
    assert_eq!(run_expr(src, "1 + M").err(), Some(vec![(S003, 1, 5)]));
    assert_eq!(
        run_expr(src, "y + x").err(),
        Some(vec![(S003, 1, 1), (S003, 1, 5)])
    );
}

/// The body of a function. The body starts on line 2.
fn fn_body(s: &str) -> String {
    format!("fn f(p: Bool) -> Bool {{\n{s}\n}}")
}

#[test]
fn the_container_forms_resolve_their_parts() {
    ok(&fn_body(
        "let t = (p, [p, p], ());\nlet x: (Bool, [Bool; 2], ()) = t;\nreturn t.0;",
    ));
    ok(&fn_body(
        "let x: (Bool,) = (p,);\nlet n = len([x.0]);\nreturn x.0x0;",
    ));
    ok("const A: Unit = ();\nconst N: Nat = len([A, A]);");
}

#[test]
fn unit_and_len_are_prelude_names() {
    let r = ok("fn f() -> Nat { return len; }\nfn g() -> Nat { return Unit; }");
    assert_eq!(
        target_at(&r, pos(1, 24)),
        Some(Target::Prelude(Prelude::Len))
    );
    assert_eq!(
        target_at(&r, pos(2, 24)),
        Some(Target::Prelude(Prelude::Unit))
    );
    assert_eq!(
        target_at(&r, pos(2, 11)),
        Some(Target::Prelude(Prelude::Nat))
    );
    // A parameter shadows the prelude name.
    let r = ok("fn f(len: Nat) -> Nat { return len; }");
    assert_eq!(decl_at(&r, pos(1, 32)).kind, Kind::Param);
    assert_eq!(
        errors("const Unit: Nat = 1;\nconst A: Unit = 1;"),
        [(S003, 2, 10)]
    );
}

#[test]
fn an_unknown_name_in_a_container_form_is_s003_at_the_name() {
    for (src, line, col) in [
        (fn_body("return (p, q);"), 2, 12),
        (fn_body("return [p, q];"), 2, 12),
        (fn_body("return q.0;"), 2, 8),
        (fn_body("return [p][q];"), 2, 12),
        (fn_body("let x: [Bool; N] = [];\nreturn p;"), 2, 15),
        (fn_body("let x: [Foo; 2] = [];\nreturn p;"), 2, 9),
        (fn_body("let x: (Bool, Foo) = (p, p);\nreturn p;"), 2, 15),
        ("const N: Nat = 1;\nconst A: (N,) = (1,);".to_owned(), 2, 11),
    ] {
        assert_eq!(errors(&src), [(S003, line, col)], "{src}");
    }
}
