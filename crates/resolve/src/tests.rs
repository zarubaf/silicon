// SPDX-License-Identifier: Apache-2.0
use crate::{Code, Decl, Failed, Kind, Prelude, Resolved, Target, VariantRef, resolve};
use parse::ast::{
    Expr, FnParam, Ident, Item, NodeId, Param, ParamMode, Pattern, PortForm, Pos, Stmt, TypeExpr,
};
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
                Item::Enum { name, .. } => ids.ident(name),
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
                Stmt::Wire { name, ty, .. } | Stmt::Alias { name, ty, .. } => {
                    self.ident(name);
                    self.ty(ty);
                }
                Stmt::Input { name, form, ty, .. } | Stmt::Output { name, form, ty, .. } => {
                    self.ident(name);
                    if let PortForm::Indexed(key) | PortForm::Keyed(key) = form {
                        self.expr(key);
                    }
                    self.ty(ty);
                }
                Stmt::Mem {
                    name, word, depth, ..
                } => {
                    self.ident(name);
                    self.ty(word);
                    self.expr(depth);
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
            TypeExpr::Fn { params, ret, .. } => self.fn_type(params, ret),
            TypeExpr::Builtin { args, .. } => {
                for operand in args.operands() {
                    self.expr(operand);
                }
            }
        }
    }

    fn fn_type(&mut self, params: &[FnParam], ret: &TypeExpr) {
        for param in params {
            self.ty(&param.ty);
        }
        self.ty(ret);
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        for expr in exprs {
            self.expr(expr);
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Num { .. }
            | Expr::Bool { .. }
            | Expr::Str { .. }
            | Expr::Unit { .. }
            | Expr::Path { .. } => {}
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
            Expr::Method {
                recv, name, args, ..
            } => {
                self.expr(recv);
                self.ident(name);
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
            Expr::FnType { params, ret, .. } => self.fn_type(params, ret),
            Expr::Tuple { elems, .. } | Expr::Array { elems, .. } => self.exprs(elems),
            Expr::Builtin { args, .. } => {
                for operand in args.operands() {
                    self.expr(operand);
                }
            }
            Expr::Match { scrut, arms, .. } => {
                self.expr(scrut);
                for arm in arms {
                    if let Pattern::Variant { binders, .. } = &arm.pat {
                        for binder in binders.iter().flatten() {
                            self.ident(binder);
                        }
                    }
                    self.expr(&arm.value);
                }
            }
        }
    }
}

/// What the name node at a position of the file points to.
fn target_at(resolved: &Resolved, at: Pos) -> Option<Target> {
    let user = resolved.prelude_struct("ReadResponse").unwrap_or(0);
    resolved.target(Ids::of_items(&resolved.ast()[..user]).at(at))
}

/// The `S003` text of a receiver call whose name `n` is not a function.
fn not_a_function(n: &str) -> String {
    format!(
        "`{n}` is not a function; a receiver call `a.f()` needs a function `f`, so write \
         `{n}(a)` to call a type or a function value"
    )
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
    assert_eq!(r.ast().len(), 3 + 6);
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
    // A local in a type position can hold a type, so only elaboration checks it.
    ok("fn f(Bool: Nat, x: Bool) -> Nat { return x; }\n");
    ok("fn f(p: Bool) -> Bool {\n  { let Bool = 1; }\n  let x: Bool = p;\n  return x;\n}\n");
}

#[test]
fn an_unknown_name_is_s003_at_the_name() {
    assert_eq!(errors("const A: Nat = x + 1;\n"), [(S003, 1, 16)]);
    assert_eq!(errors("const A: Natt = 1;\n"), [(S003, 1, 10)]);
}

#[test]
fn the_prelude_structs_of_slice_4_resolve() {
    ok("const A: FieldInfo = 1;\nconst B: TypeInfo = 1;\nconst C: VariantInfo = 1;\n");
    ok("const A: PortKey = 1;\nconst B: PortInfo = 1;\n");
    ok("const A: Nat = TypeInfo(1);\n");
    ok("const A: Wire[Bool] = 1;\nconst B: Nat = read(1);\n");
    ok("module M() {\n  reg r: Reg[Bool] = false;\n}\n");
}

#[test]
fn domain_is_s003_with_its_own_text() {
    assert_eq!(
        errors("fn f(x: Domain) -> Bool { return true; }\n"),
        [(S003, 1, 9)]
    );
    assert_eq!(
        message("fn f(x: Domain) -> Bool { return true; }\n"),
        "`Domain` is not supported yet; it comes with more domains (#11); a module has one \
         domain or none, so it needs no `Domain` value"
    );
    ok("const Domain: Nat = 1;\nconst N: Nat = Domain;\n");
}

#[test]
fn the_first_argument_of_instance_is_a_module_item() {
    let counter = "module C(comptime W: Nat) {}\n";
    ok(&format!(
        "{counter}module M() {{\nlet t = Instance[C, 8];\nlet x: Instance[C, 8] = t;\n}}\n"
    ));
    ok(&format!(
        "{counter}fn f(x: Instance[C, 8]) -> Bool {{ return true; }}\n"
    ));
    let text = "the first argument of `Instance` is not a module; write the module first, for \
                example `Instance[Counter, 8]`";
    for (src, line, col) in [
        (
            "const N: Nat = 1;\nconst T: Type = Instance[N, 8];\n",
            3,
            26,
        ),
        ("fn f(x: Instance[Q, 8]) -> Bool { return true; }\n", 2, 18),
        (
            "module M() {\nlet C = 1;\nlet t = Instance[C, 8];\n}\n",
            4,
            18,
        ),
        ("const T: Type = Instance[1 + 2];\n", 2, 26),
        ("const T: Type = Instance[q::A];\n", 2, 26),
    ] {
        let src = format!("{counter}{src}");
        assert_eq!(errors(&src), [(S003, line, col)], "{src}");
        assert_eq!(message(&src), text, "{src}");
    }
    // The error replaces each `S003` of the argument; an error of another argument stays.
    let src = format!("{counter}const T: Type = (z, Instance[N]);\n");
    assert_eq!(message(&src), "`z` is not declared");
    let src = format!("{counter}const T: Type = Instance[C, C];\n");
    assert_eq!(errors(&src), [(S003, 2, 29)]);
    assert_eq!(
        message(&src),
        "`C` is not a value; a module is used only in an `instance`"
    );
    assert_eq!(
        errors(&format!("{counter}const T: Type = Reg[C];\n")),
        [(S003, 2, 21)]
    );
}

#[test]
fn the_handle_families_and_read_are_prelude_names() {
    for (name, want) in [
        ("Reg", Prelude::Reg),
        ("Wire", Prelude::Wire),
        ("Input", Prelude::Input),
        ("Mem", Prelude::Mem),
        ("Instance", Prelude::Instance),
    ] {
        let src = format!("const A: {name} = 1;\n");
        let r = ok(&src);
        assert_eq!(target_at(&r, find(&src, name)), Some(Target::Prelude(want)));
        assert!(want.is_type() && !want.is_fn());
    }
    let src = "fn f() -> Nat { return read; }";
    let r = ok(src);
    assert_eq!(
        target_at(&r, find(src, "read")),
        Some(Target::Prelude(Prelude::Read))
    );
    assert!(Prelude::Read.is_fn() && !Prelude::Read.is_type());
    assert_eq!(Prelude::Read.modes().len(), 1);
    assert_eq!(Prelude::Read.receiver(), Some(0));
    ok(
        "fn read(a: Bool, b: Bool) -> Bool { return a; }\nfn g(p: Bool) -> Bool { return read(p, p); }\n",
    );
    ok("module read() {}\nmodule M() {\ninstance read = read();\nlet x = read.q;\n}\n");
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
fn the_message_of_an_unknown_name_has_no_slice() {
    let message = |src: &str| match run(src) {
        Err(Failed::Names(errors)) => errors[0].message.clone(),
        _ => panic!("expected an error"),
    };
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

fn mem_body(body: &str) -> String {
    format!("module M(comptime W: Nat) {{\n{body}\n}}\n")
}

#[test]
fn a_mem_declares_its_name_after_its_word_and_its_depth() {
    ok(&mem_body("mem m: [UInt[W]; W + 1];\nlet x = m;"));
    let cases = [
        ("mem m: [T; 4];", S003, 2, 9),
        ("mem m: [Bool; n];", S003, 2, 15),
        ("mem m: [Bool; m];", S003, 2, 15),
        ("wire m: Bool;\nmem m: [Bool; 4];", S002, 3, 5),
        ("mem m: [Bool; 4];\nlet m = 1;", S002, 3, 5),
        ("mem W: [Bool; 4];", S002, 2, 5),
    ];
    for (body, code, line, col) in cases {
        assert_eq!(errors(&mem_body(body)), [(code, line, col)], "{body}");
    }
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
    assert_eq!(r.ast().len(), 4 + 6);
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

// The type forms of slice 2, phase 3.

#[test]
fn struct_and_alias_items_are_in_the_item_scope() {
    let r = ok(
        "struct P(comptime W: Nat) { a: UInt[W], b: Bool }\nconst A: P[8] = P[8](1, true);\n\
         type B = UInt[8];\nconst C: B = B(3);\n",
    );
    assert_eq!(r.decl(r.item("P").unwrap()).kind, Kind::Struct);
    assert_eq!(r.decl(r.item("B").unwrap()).kind, Kind::Alias);
    // `P` in the type of `A`, and `B` in the type of `C`.
    assert_eq!(decl_at_use(&r, pos(2, 10)), Kind::Struct);
    assert_eq!(decl_at_use(&r, pos(4, 10)), Kind::Alias);
    // An alias is visible before its declaration.
    ok("const A: T = 1;\ntype T = Bool;\n");
    ok("type A = A;\n");
    assert_eq!(
        errors("const A: Nat = 1;\ntype A = Bool;\n"),
        [(S002, 2, 6)]
    );
    assert_eq!(errors("struct A {}\nmodule A() {}\n"), [(S002, 2, 8)]);
    assert_eq!(errors("struct A {}\nstruct A {}\n"), [(S002, 2, 8)]);
}

#[test]
fn type_and_data_bits_are_prelude_names() {
    let r = ok("const A: Type = Bool;\nfn f() -> Nat { return data_bits; }\n");
    assert_eq!(
        target_at(&r, pos(1, 10)),
        Some(Target::Prelude(Prelude::Type))
    );
    assert_eq!(
        target_at(&r, pos(2, 24)),
        Some(Target::Prelude(Prelude::DataBits))
    );
    ok("fn f(comptime T: Type, x: T) -> T { return x; }");
    ok("fn f(comptime T: Type) -> Nat { let x: T = T(); return data_bits(T); }");
}

#[test]
fn the_parameters_of_a_struct_are_visible_in_the_later_types() {
    ok("struct P(comptime T: Type, comptime x: T) { a: T, b: [T; 2] }");
    ok("struct P(comptime a: Nat) { a: UInt[a] }");
    assert_eq!(
        errors("struct P(comptime W: UInt[W]) { a: Bool }"),
        [(S003, 1, 27)]
    );
    assert_eq!(
        errors("struct P(comptime A: UInt[B], comptime B: Nat) {}"),
        [(S003, 1, 27)]
    );
    assert_eq!(
        errors("struct P(comptime W: Nat) { a: Bool }\nconst N: Nat = W;"),
        [(S003, 2, 16)]
    );
    assert_eq!(errors("struct P { a: UInt[W] }"), [(S003, 1, 20)]);
    assert_eq!(
        errors("struct P(comptime a: Nat, comptime a: Nat) {}"),
        [(S002, 1, 36)]
    );
}

#[test]
fn a_second_field_with_a_name_is_s002_at_its_name() {
    assert_eq!(errors("struct S { a: Bool, a: Bool }"), [(S002, 1, 21)]);
    assert_eq!(
        errors("struct S {\na: Bool,\nb: Bool,\na: UInt[8],\n}"),
        [(S002, 4, 1)]
    );
    assert_eq!(
        errors("const A: Foo = 1;\nstruct S { a: Bool, a: Bool }"),
        [(S002, 2, 21)]
    );
}

#[test]
fn a_type_statement_declares_a_local() {
    ok(&fn_body("type T = Bool;\nlet x: T = p;\nreturn x;"));
    ok("type T = Bool;\nfn f() -> Nat { type T = T; let x: T = true; return 1; }");
    assert_eq!(errors(&fn_body("type T = T;\nreturn p;")), [(S003, 2, 10)]);
    assert_eq!(
        errors(&fn_body("type T = Bool;\ntype T = Bool;\nreturn p;")),
        [(S002, 3, 6)]
    );
    assert_eq!(
        errors(&fn_body("let T = 1;\ntype T = Bool;\nreturn p;")),
        [(S002, 3, 6)]
    );
    assert_eq!(
        errors(&fn_body("{ type T = Bool; }\nlet x: T = p;\nreturn p;")),
        [(S003, 3, 8)]
    );
}

#[test]
fn an_array_type_in_an_expression_resolves_its_parts() {
    ok(&fn_body(
        "let t = [Bool; 2];\nlet u = [[UInt[8]; 2]; 3]();\nreturn p;",
    ));
    assert_eq!(
        errors(&fn_body("let t = [Foo; 2];\nreturn p;")),
        [(S003, 2, 10)]
    );
    assert_eq!(
        errors(&fn_body("let t = [Bool; N];\nreturn p;")),
        [(S003, 2, 16)]
    );
    assert_eq!(
        errors("const N: Nat = 1;\nconst A: Type = [N; 2];"),
        [(S003, 2, 18)]
    );
}

#[test]
fn a_module_a_const_or_a_function_is_no_type() {
    assert_eq!(errors("module M() {}\nconst A: M = 1;"), [(S003, 2, 10)]);
    assert_eq!(
        errors("fn g() -> Nat { return 1; }\nstruct S { a: g }"),
        [(S003, 2, 15)]
    );
    assert_eq!(errors("const N: Nat = 1;\ntype A = N;"), [(S003, 2, 10)]);
    assert_eq!(
        errors("struct S {}\nmodule M() {\ninstance u = S();\n}"),
        [(S003, 3, 14)]
    );
    assert_eq!(
        errors("type A = Bool;\nmodule M() {\ninstance u = A();\n}"),
        [(S003, 3, 14)]
    );
}

// Receiver calls, the call sites, and the list prelude. The cases come from the guards of
// `Silicon.Source.Test.Resolve` in Lean.

/// The position of the first `needle` in the source, which has one line before `line`.
fn find(src: &str, needle: &str) -> Pos {
    let at = src.find(needle).unwrap();
    let before = &src[..at];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    pos(line, col)
}

/// The message of the first error.
fn message(src: &str) -> String {
    match run(src) {
        Err(Failed::Names(errors)) => errors[0].message.clone(),
        _ => panic!("expected an error"),
    }
}

#[test]
fn the_strings_and_the_lists_are_prelude_names() {
    let r = ok("const S: String = \"a\";\nconst L: List[Int] = list(Int);");
    let prelude = |src: &str, needle: &str| target_at(&r, find(src, needle));
    assert_eq!(
        prelude("const S: String = \"a\";", "String"),
        Some(Target::Prelude(Prelude::String))
    );
    assert_eq!(
        target_at(&r, pos(2, 10)),
        Some(Target::Prelude(Prelude::List))
    );
    assert_eq!(
        target_at(&r, pos(2, 22)),
        Some(Target::Prelude(Prelude::ListFn))
    );
    for (name, want) in [
        ("push", Prelude::Push),
        ("pop", Prelude::Pop),
        ("str", Prelude::Str),
    ] {
        let src = format!("fn f() -> Nat {{ return {name}; }}");
        let r = ok(&src);
        assert_eq!(
            target_at(&r, find(&src, name)),
            Some(Target::Prelude(want)),
            "{name}"
        );
    }
    // A `mut` parameter is a local.
    let src = "fn f(mut xs: List[Int]) -> Nat { return xs; }";
    let r = ok(src);
    assert_eq!(decl_at(&r, find(src, "xs;")).kind, Kind::Param);
    ok("fn f(mut xs: List[Int], x: Int) -> () { push(xs, x); let s = str(pop(xs)); }");
    ok("const List: Nat = 1;\nconst N: Nat = List;");
}

#[test]
fn the_name_of_a_receiver_call_is_a_function_of_the_items_or_the_prelude() {
    let method = |src: &str, name: &str| {
        let r = ok(src);
        // The method name is the last use of `name` after the dot.
        let at = src.find(&format!(".{name}(")).unwrap() + 1;
        let before = &src[..at];
        let line = before.matches('\n').count() + 1;
        let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
        match target_at(&r, pos(line, col)) {
            Some(Target::Decl(id)) => Err(r.decl(id).kind),
            Some(Target::Prelude(p)) => Ok(p),
            None => panic!("no target for {name}"),
        }
    };
    let g = "fn g(x: Bool) -> Bool { return x; }";
    assert_eq!(
        method(
            &format!("fn f(p: Bool) -> Bool {{ return p.g(); }}\n{g}"),
            "g"
        ),
        Err(Kind::Fn)
    );
    // A local does not hide the function.
    assert_eq!(
        method(
            &format!("fn f(g: Bool) -> Bool {{ return g.g(); }}\n{g}"),
            "g"
        ),
        Err(Kind::Fn)
    );
    assert_eq!(
        method("fn f(xs: List[Int]) -> () { return xs.push(1); }", "push"),
        Ok(Prelude::Push)
    );
    assert_eq!(
        method("fn f(p: Bool) -> Nat { return p.len(); }", "len"),
        Ok(Prelude::Len)
    );
    // An item hides a prelude function.
    assert_eq!(
        method(
            "fn f(p: Bool) -> Nat { return p.len(); }\nfn len(x: Bool) -> Nat { return 1; }",
            "len"
        ),
        Err(Kind::Fn)
    );
    assert_eq!(
        method(
            "fn f(T: Type) -> Nat { return T.data_bits(); }",
            "data_bits"
        ),
        Ok(Prelude::DataBits)
    );
    ok(&fn_body(
        "let x = p.resize(UInt[8]);\nreturn p.static_assert(\"a\");",
    ));
}

#[test]
fn s003_the_name_of_a_receiver_call_is_not_a_function_there() {
    let fails = |src: &str, line: usize, col: usize| {
        assert_eq!(errors(src), [(S003, line, col)], "{src}");
    };
    fails(&fn_body("return p.foo();"), 2, 10);
    assert_eq!(
        message(&fn_body("return p.foo();")),
        "`foo` is not declared"
    );
    // A local is no function.
    fails(&fn_body("let h = 1;\nreturn p.h();"), 3, 10);
    let c = "const g: Nat = 1;\n";
    fails(&format!("{c}{}", fn_body("return p.g();")), 3, 10);
    assert_eq!(
        message(&format!("{c}{}", fn_body("return p.g();"))),
        not_a_function("g")
    );
    fails(
        &format!("const len: Nat = 1;\n{}", fn_body("return p.len();")),
        3,
        10,
    );
    fails(
        &format!("module M() {{}}\n{}", fn_body("return p.M();")),
        3,
        10,
    );
    fails(
        &format!("struct S {{}}\n{}", fn_body("return p.S();")),
        3,
        10,
    );
    fails(&fn_body("return p.Bool();"), 2, 10);
    assert_eq!(
        message(&fn_body("return p.Bool();")),
        not_a_function("Bool")
    );
    fails(&fn_body("return p.Reg();"), 2, 10);
    assert_eq!(message(&fn_body("return p.Reg();")), not_a_function("Reg"));
    assert_eq!(
        message(&fn_body("return p.PortKey();")),
        not_a_function("PortKey")
    );
}

#[test]
fn s003_in_the_receiver_or_an_argument_of_a_receiver_call() {
    for (body, line, col) in [
        ("return q.len();", 2, 8),
        ("return q.foo();", 2, 8),
        ("return p.foo(q);", 2, 10),
        ("return p.len(q);", 2, 14),
        ("return p.len().foo();", 2, 16),
    ] {
        assert_eq!(errors(&fn_body(body))[0], (S003, line, col), "{body}");
    }
}

/// The call sites of the call nodes and the method nodes in the first item, in pre-order.
fn call_sites(r: &Resolved) -> Vec<(Pos, usize)> {
    fn expr(r: &Resolved, e: &Expr, out: &mut Vec<(Pos, usize)>) {
        match e {
            Expr::Call {
                pos,
                id,
                callee,
                args,
            } => {
                out.push((*pos, r.site(*id).unwrap()));
                expr(r, callee, out);
                for a in args {
                    expr(r, a, out);
                }
            }
            Expr::Method {
                pos,
                id,
                recv,
                args,
                ..
            } => {
                out.push((*pos, r.site(*id).unwrap()));
                expr(r, recv, out);
                for a in args {
                    expr(r, a, out);
                }
            }
            Expr::Index { base, args, .. } => {
                expr(r, base, out);
                for a in args {
                    expr(r, a, out);
                }
            }
            Expr::Builtin { args, .. } => {
                for a in args.operands() {
                    expr(r, a, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    let (Item::Fn { body, .. } | Item::Module { body, .. }) = &r.ast()[0] else {
        panic!("not a body");
    };
    for stmt in body {
        match stmt {
            Stmt::Local { value, .. } | Stmt::Expr { value, .. } => expr(r, value, &mut out),
            Stmt::Ret { value: Some(v), .. } => expr(r, v, &mut out),
            _ => {}
        }
    }
    out
}

fn sites(src: &str) -> Vec<usize> {
    call_sites(&ok(src)).iter().map(|&(_, k)| k).collect()
}

#[test]
fn the_call_sites_of_a_body_count_in_pre_order_from_zero() {
    // A node comes before its callee, its receiver, and its arguments.
    assert_eq!(
        sites(&fn_body("let a = len(p);\nreturn p.len(len(p));")),
        [0, 1, 2]
    );
    assert_eq!(sites(&fn_body("return len(p).len();")), [0, 1]);
    // The type of a parameter comes before the body, so its calls do not shift the sites.
    assert_eq!(
        sites("fn f(x: UInt[len([1])]) -> Bool {\nreturn x.f(len(x));\n}"),
        [0, 1]
    );
    assert_eq!(sites(&fn_body("return UInt[8](p)(p);")), [0, 1]);
    // A call outside the body does not shift them, and each body starts at 0.
    assert_eq!(
        sites("module M() {\nlet a = len([1]);\n}\nfn g() -> Nat { return len([1]); }"),
        [0]
    );
}

#[test]
fn the_call_sites_of_an_expression_count_from_zero() {
    let r = run_expr("const A: Nat = 1;", "len([A]).len()").unwrap();
    let Expr::Method { id, recv, .. } = r.expr() else {
        panic!("not a method");
    };
    let Expr::Call { id: inner, .. } = &**recv else {
        panic!("not a call");
    };
    assert_eq!((r.site(*id), r.site(*inner)), (Some(0), Some(1)));
}

/// The parameter that the receiver of `return x.m(...);` in the first item binds to.
fn receiver_of_return(src: &str) -> Option<usize> {
    let r = ok(src);
    let Some(Item::Fn { body, .. }) = r.ast().first() else {
        panic!("not a fn");
    };
    let Some(Stmt::Ret {
        value: Some(Expr::Method { id, .. }),
        pos: _,
    }) = body.last()
    else {
        panic!("not a method return");
    };
    r.receiver(*id)
}

#[test]
fn the_receiver_binds_to_the_first_parameter_without_a_comptime_mark() {
    assert_eq!(
        receiver_of_return("fn f(T: Type) -> Nat { return T.data_bits(); }"),
        Some(0)
    );
    assert_eq!(
        receiver_of_return("fn f(p: Bool) -> Bool { return p.resize(Bool); }"),
        Some(1)
    );
    assert_eq!(
        receiver_of_return("fn f(T: Type) -> Nat { return T.list(); }"),
        None
    );
    assert_eq!(
        receiver_of_return(
            "fn f(p: Nat) -> Nat { return p.g(1); }\ncomptime fn g(comptime a: Nat, b: Nat) -> Nat { return b; }"
        ),
        Some(1)
    );
}

#[test]
fn function_types_resolve_their_parts_in_both_forms() {
    let src = "struct S { a: Nat }\n\
               fn f(g: fn (UInt[8], mut S) -> Bool) -> fn (Nat) -> S { return g; }\n\
               const C: Nat = (fn (S) -> S)[8];\n";
    let r = ok(src);
    assert_eq!(
        target_at(&r, find(src, "UInt[8]")),
        Some(Target::Prelude(Prelude::UInt))
    );
    assert_eq!(decl_at(&r, find(src, "S) -> Bool")).kind, Kind::Struct);
    assert_eq!(
        target_at(&r, find(src, "Bool)")),
        Some(Target::Prelude(Prelude::Bool))
    );
    assert_eq!(decl_at(&r, find(src, "S { return")).kind, Kind::Struct);
    // The expression form resolves too.
    assert_eq!(decl_at(&r, find(src, "S) -> S)[")).kind, Kind::Struct);
}

#[test]
fn a_function_type_can_name_a_parameter_before_it() {
    let src = "fn f(T: Type, g: fn (T) -> T) -> Nat { return 1; }\n";
    let r = ok(src);
    assert_eq!(decl_at(&r, find(src, "T) -> T")).kind, Kind::Param);
    assert_eq!(decl_at(&r, find(src, "T) -> T")).pos, pos(1, 6));
}

#[test]
fn an_unknown_name_in_a_function_type_is_s003() {
    for (src, line, col) in [
        ("const A: fn (X) -> Nat = 0;\n", 1, 14),
        ("const A: fn (Nat) -> X = 0;\n", 1, 22),
        ("const A: fn (Nat, mut X) -> Nat = 0;\n", 1, 23),
        ("const A: Nat = fn (X) -> Nat;\n", 1, 20),
        ("const A: Nat = fn (Nat) -> X;\n", 1, 28),
        ("const A: Nat = fn (Nat) -> UInt[x];\n", 1, 33),
        ("fn f() -> fn () -> X { return 1; }\n", 1, 20),
        // A value is no type, and a function is no type.
        ("const K: Nat = 1;\nconst A: fn (K) -> Nat = 0;\n", 2, 14),
        (
            "fn g() -> Nat { return 1; }\nconst A: fn () -> g = 0;\n",
            2,
            19,
        ),
    ] {
        assert_eq!(errors(src), [(S003, line, col)], "{src}");
    }
}

#[test]
fn a_function_type_declares_no_name() {
    // The parameter types have no names, so `x` is not in scope in the result type.
    assert_eq!(
        errors("const A: fn (Nat) -> UInt[x] = 0;\n"),
        [(S003, 1, 27)]
    );
    ok("fn f(x: Nat, g: fn (Nat) -> Nat) -> Nat { return g(x); }\n");
}

#[test]
fn a_function_name_as_a_value_resolves_to_its_item() {
    let src = "fn g(x: Nat) -> Nat { return x; }\n\
               comptime fn h(comptime n: Nat) -> Nat { return n; }\n\
               const A: fn (Nat) -> Nat = g;\n\
               const B: Nat = h;\n\
               fn k(f: fn (Nat) -> Nat) -> Nat { return f(1); }\n\
               const C: Nat = k(g);\n";
    let r = ok(src);
    assert_eq!(decl_at(&r, find(src, "g;")).kind, Kind::Fn);
    assert_eq!(decl_at(&r, find(src, "h;")).name, "h");
    assert_eq!(decl_at(&r, find(src, "g);")).name, "g");
    // A parameter of a function type hides an item in the body.
    assert_eq!(decl_at(&r, find(src, "f(1)")).kind, Kind::Param);
}

#[test]
fn a_builtin_name_as_a_value_resolves_to_the_prelude() {
    let src = "const A: Nat = len;\n";
    let r = ok(src);
    assert!(matches!(
        target_at(&r, find(src, "len")),
        Some(Target::Prelude(_))
    ));
}

/// Whether the function item `name` of the source is generic.
fn generic(src: &str, name: &str) -> bool {
    let r = ok(src);
    let id = r.item(name).unwrap();
    assert_eq!(r.decl(id).kind, Kind::Fn);
    r.decl(id).generic
}

#[test]
fn a_function_is_generic_with_a_comptime_parameter() {
    assert!(generic("fn f(comptime n: Nat) -> Nat { return n; }", "f"));
    assert!(generic(
        "comptime fn f(x: Nat, comptime n: Nat) -> Nat { return n; }",
        "f"
    ));
    // A `comptime fn` without a `comptime` parameter is no generic function.
    assert!(!generic("comptime fn f(x: Nat) -> Nat { return x; }", "f"));
}

#[test]
fn a_function_is_generic_when_its_signature_names_a_parameter() {
    for src in [
        "fn f(T: Type, x: T) -> T { return x; }",
        "fn f(n: Nat) -> UInt[n] { return 0; }",
        "fn f(n: Nat, x: UInt[n]) -> Nat { return 0; }",
        "fn f(T: Type, g: fn (T) -> Nat) -> Nat { return 0; }",
        "fn f(T: Type) -> fn () -> T { return 0; }",
        "fn f(T: Type) -> (T, Nat) { return 0; }",
        "fn f(T: Type) -> [T; 2] { return 0; }",
        "fn f(n: Nat) -> [Nat; n + 1] { return 0; }",
        "fn f(n: Nat, m: Nat) -> UInt[g(n)] { return 0; }\nfn g(x: Nat) -> Nat { return x; }",
        // A parameter hides the item of its name.
        "struct S { a: Nat }\nfn f(S: Type, x: S) -> Nat { return 0; }",
        // A builtin in a type position holds the names of its operands.
        "fn f(x: UInt[8]) -> @TypeOf(x) { return x; }",
        "fn f(x: UInt[8], y: @TypeOf(x)) -> Nat { return 0; }",
        "fn f(fs: Nat) -> @Struct(fs) { return 0; }",
        "fn f(x: Nat) -> [@TypeOf(x); 2] { return 0; }",
        "fn f(x: Nat) -> fn (@TypeOf(x)) -> Nat { return 0; }",
        "fn f(x: Nat) -> @Struct([FieldInfo(\"a\", @TypeOf(x))]) { return 0; }",
    ] {
        assert!(generic(src, "f"), "{src}");
    }
}

#[test]
fn a_function_is_not_generic_for_items_and_locals() {
    for src in [
        "fn f() -> Nat { return 1; }",
        "fn f(x: Nat) -> Nat { return x; }",
        // The name of a parameter in the body is no name in the signature.
        "fn f(T: Type) -> Nat { return 1; }",
        "fn f(x: Nat, y: fn (Nat) -> Nat) -> Nat { return y(x); }",
        "struct S { a: Nat }\nfn f(x: S) -> S { return x; }",
        "const W: Nat = 8;\nfn f(x: UInt[W]) -> UInt[W] { return x; }",
        "type T = Nat;\nfn f(x: T) -> T { return x; }",
        "fn f() -> Nat { type T = Nat; let x: T = 1; return x; }",
        // A builtin in a type position that names no parameter.
        "const k: Nat = 0;\nfn f(x: UInt[8]) -> @TypeOf(k) { return x; }",
        "fn f(x: Nat) -> @Struct([]) { return 0; }",
    ] {
        assert!(!generic(src, "f"), "{src}");
    }
}

#[test]
fn a_function_type_in_the_body_does_not_change_genericity() {
    let src = "fn g(n: Nat) -> Nat { let f: fn (Nat) -> Nat = g; return n; }\n\
               fn h(n: Nat) -> Nat { return n; }\n";
    assert!(!generic(src, "g"));
    assert!(!generic(src, "h"));
}

/// The item of the prelude struct `ReadResponse`.
fn response_item(r: &Resolved) -> Option<&Item> {
    r.ast().get(r.prelude_struct("ReadResponse")?)
}

/// The targets of the names of the prelude struct item, by their node ids: the name, the
/// parameter `T`, its type, the type of `data`, and the type of `valid`.
fn response_targets(r: &Resolved) -> [Option<Target>; 4] {
    let Some(Item::Struct { params, fields, .. }) = response_item(r) else {
        panic!("the first prelude item is the prelude struct");
    };
    let ty = |t: &TypeExpr| match t {
        TypeExpr::Name { id, .. } => r.target(*id),
        _ => panic!("a type name"),
    };
    [
        r.target(params[0].name.id),
        ty(&params[0].ty),
        ty(&fields[0].ty),
        ty(&fields[1].ty),
    ]
}

#[test]
fn every_name_node_of_a_prelude_struct_has_a_target() {
    let r = ok("");
    for b in crate::prelude::build() {
        for (id, leaf) in &b.uses {
            if let crate::prelude::Leaf::Prim(name) = leaf {
                assert!(Prelude::of(name).is_some(), "`{name}` is no prelude name");
            }
            assert!(r.target(*id).is_some(), "a name node of `{}`", b.name.name);
        }
        assert!(r.target(b.name.id).is_some());
        for p in &b.params {
            assert!(r.target(p.id).is_some());
        }
    }
}

#[test]
fn the_field_types_of_the_prelude_structs_never_go_through_the_item_scope() {
    // A user `String` and a user `FieldInfo` shadow the names in the file, not in `TypeInfo`.
    let r = ok("struct String { a: Bool }\nstruct FieldInfo { a: Bool }\n");
    let item = |name: &str| &r.ast()[r.prelude_struct(name).unwrap()];
    let Item::Struct { name: info, .. } = item("FieldInfo") else {
        panic!("a struct");
    };
    let info = r.target(info.id);
    assert_ne!(info, r.item("FieldInfo").map(Target::Decl));
    let Item::Struct { fields, .. } = item("TypeInfo") else {
        panic!("a struct");
    };
    assert_eq!(fields.len(), 6);
    let TypeExpr::Name { id, .. } = &fields[0].ty else {
        panic!("a type name");
    };
    assert_eq!(r.target(*id), Some(Target::Prelude(Prelude::String)));
    let TypeExpr::Index { args, .. } = &fields[1].ty else {
        panic!("a list type");
    };
    let Expr::Name { id, .. } = &args[0] else {
        panic!("a name");
    };
    assert_eq!(
        r.target(*id),
        info,
        "the list of `FieldInfo` names the prelude struct"
    );
}

#[test]
fn the_memory_functions_are_prelude_names_without_a_comptime_mark() {
    for (name, want, arity) in [
        ("read_port", Prelude::ReadPort, 3),
        ("write_port", Prelude::WritePort, 4),
    ] {
        let src = format!("fn f() -> Nat {{ return {name}; }}");
        let r = ok(&src);
        assert_eq!(
            target_at(&r, find(&src, name)),
            Some(Target::Prelude(want)),
            "{name}"
        );
        assert!(want.is_fn() && !want.is_type());
        assert_eq!(want.modes().len(), arity);
        assert_eq!(want.receiver(), Some(0), "the receiver binds to `m`");
    }
}

#[test]
fn a_receiver_call_of_a_memory_function_binds_the_receiver_to_the_first_parameter() {
    let src = "fn f(m: Nat) -> Nat { return m.read_port(1, 2); }";
    let r = ok(src);
    assert_eq!(
        target_at(&r, find(src, "read_port")),
        Some(Target::Prelude(Prelude::ReadPort))
    );
    let src = "fn f(m: Nat) -> Nat { return m.write_port(1, 2, 3); }";
    assert_eq!(receiver_of_return(src), Some(0));
}

#[test]
fn a_user_function_shadows_a_memory_function_name() {
    let src = "comptime fn read_port(n: Nat) -> Nat { return n; }\n\
               fn f(x: Nat) -> Nat { return read_port(x) + x.read_port(); }";
    let r = ok(src);
    assert_eq!(decl_at(&r, find(src, "read_port(x)")).kind, Kind::Fn);
    assert_eq!(decl_at(&r, find(src, "read_port()")).kind, Kind::Fn);
}

#[test]
fn the_prelude_structs_follow_the_user_items_and_change_no_user_index() {
    let src = "const A: Nat = 1;\nstruct S { a: Bool }\n";
    let r = ok(src);
    assert_eq!(r.ast().len(), 2 + 6);
    assert!(!r.is_prelude_item(0) && !r.is_prelude_item(1) && r.is_prelude_item(2));
    assert!(r.is_prelude_item(7));
    assert_eq!(r.prelude_struct("ReadResponse"), Some(2));
    assert_eq!(r.prelude_struct("PortInfo"), Some(7));
    assert_eq!(r.prelude_struct("Nope"), None);
    assert_eq!(r.item("A").map(|d| r.decl(d).kind), Some(Kind::Const));
    assert!(r.item("ReadResponse").is_none(), "not in the item scope");
    let Some(Item::Struct { name, .. }) = r.ast().get(2) else {
        panic!("a struct");
    };
    assert_eq!(name.name, "ReadResponse");
    assert_eq!(name.pos, pos(0, 0));
    let Some(Target::Decl(d)) = r.target(name.id) else {
        panic!("the name points to its declaration");
    };
    assert_eq!(r.decl(d).kind, Kind::Struct);
    assert_eq!(r.decl(d).pos, pos(0, 0));
}

#[test]
fn the_prelude_struct_is_resolved_already() {
    let r = ok("fn f() -> Nat { return 1; }");
    let [t, ty, data, valid] = response_targets(&r);
    assert!(matches!(t, Some(Target::Decl(_))));
    assert_eq!(ty, Some(Target::Prelude(Prelude::Type)));
    assert_eq!(data, t, "`data: T` points to the parameter");
    assert_eq!(valid, Some(Target::Prelude(Prelude::Bool)));
}

#[test]
fn a_user_bool_or_type_does_not_change_the_prelude_struct() {
    let want = response_targets(&ok("fn f() -> Nat { return 1; }"));
    let [t, ty, data, valid] = want;
    for src in [
        "struct Bool { a: Nat }",
        "type Type = Nat;",
        "const Bool: Nat = 1;\nconst Type: Nat = 2;",
        "struct T { a: Nat }",
    ] {
        let r = ok(src);
        let [t2, ty2, data2, valid2] = response_targets(&r);
        assert_eq!(ty2, ty, "{src}");
        assert_eq!(valid2, valid, "{src}");
        assert!(matches!(t2, Some(Target::Decl(_))) && t2 == data2, "{src}");
        assert_eq!(t2.is_some(), t.is_some());
        assert_eq!(data2.is_some(), data.is_some());
    }
}

#[test]
fn the_name_read_response_resolves_to_the_prelude_struct() {
    let src = "fn f() -> ReadResponse[Bool] { return ReadResponse[Bool](); }";
    let r = ok(src);
    let Some(Item::Struct { name, .. }) = response_item(&r) else {
        panic!("a struct");
    };
    let want = r.target(name.id);
    assert_eq!(target_at(&r, find(src, "ReadResponse[Bool] {")), want);
    assert_eq!(target_at(&r, find(src, "ReadResponse[Bool](")), want);
    let file = ok("fn f() -> Nat { return 1; }");
    let e = run_expr("fn f() -> Nat { return 1; }", "ReadResponse[Bool]").unwrap();
    let ids = Ids::of_expr(e.expr());
    let Some(Target::Decl(d)) = e.target(ids.at(pos(1, 1))) else {
        panic!("a declaration");
    };
    assert_eq!(file.decl(d).name, "ReadResponse");
    assert_eq!(file.decl(d).kind, Kind::Struct);
}

#[test]
fn a_user_struct_shadows_the_prelude_struct() {
    let src = "struct ReadResponse { a: Bool }\nfn f() -> ReadResponse { return ReadResponse(); }";
    let r = ok(src);
    let user = r.item("ReadResponse").unwrap();
    assert_eq!(r.decl(user).pos, pos(1, 8));
    assert_eq!(
        target_at(&r, find(src, "ReadResponse {")),
        Some(Target::Decl(user))
    );
    assert_eq!(
        target_at(&r, find(src, "ReadResponse()")),
        Some(Target::Decl(user))
    );
    assert_eq!(
        r.ast().len(),
        2 + 6,
        "the prelude structs still follow the user items"
    );
}

#[test]
fn the_prelude_struct_is_no_function() {
    let src = fn_body("return p.ReadResponse();");
    assert_eq!(errors(&src), [(S003, 2, 10)]);
    assert_eq!(message(&src), not_a_function("ReadResponse"));
}

#[test]
fn the_prelude_struct_adds_no_error_and_no_duplicate() {
    // A user item with the name does not collide: the prelude struct is not in the item scope.
    ok("struct ReadResponse { a: Bool }");
    ok("fn read_port() -> Nat { return 1; }\nfn write_port() -> Nat { return 1; }");
    assert_eq!(
        errors("struct ReadResponse { a: Bool }\nstruct ReadResponse { b: Bool }"),
        [(S002, 2, 8)]
    );
}

#[test]
fn diagnostic_is_a_prelude_function_with_two_parameters() {
    let src = "fn f() -> Unit { return diagnostic; }";
    let r = ok(src);
    let want = Prelude::Diagnostic;
    assert_eq!(
        target_at(&r, find(src, "diagnostic")),
        Some(Target::Prelude(want))
    );
    assert!(want.is_fn() && !want.is_type());
    assert_eq!(want.modes(), &[ParamMode::None; 2]);
    assert_eq!(want.receiver(), Some(0));
    let src = "comptime fn diagnostic(n: Nat) -> Nat { return n; }\n\
               fn f(x: Nat) -> Nat { return diagnostic(x); }";
    let r = ok(src);
    assert_eq!(decl_at(&r, find(src, "diagnostic(x)")).kind, Kind::Fn);
}

// Enums (slice 3, section 5.6)

const OPS: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n";

fn first_message(src: &str) -> String {
    match run(src) {
        Err(Failed::Names(errors)) => errors[0].message.clone(),
        _ => panic!("expected a name error"),
    }
}

#[test]
fn an_enum_item_is_a_type_name_and_a_name_in_an_expression() {
    ok(&format!(
        "{OPS}fn f(x: UInt[8]) -> Op {{ let a: Op = Op::Add; return Op::Load(x); }}"
    ));
    ok("fn f() -> UInt[1] { return E::A; }\nenum E: UInt[1] { A = 0 }");
    ok("enum E: UInt[1] {}");
    let r = ok(OPS);
    assert_eq!(r.decl(r.item("Op").unwrap()).kind, Kind::Enum);
}

#[test]
fn a_variant_path_and_its_call_resolve_to_the_enum_and_the_variant() {
    let src = format!(
        "{OPS}fn f(x: UInt[8]) -> Op {{ return Op::Load(x); }}\nfn g() -> Op {{ return Op::Add; }}"
    );
    let r = ok(&src);
    let (mut seen, mut index) = (Vec::new(), 0);
    for item in r.ast() {
        if let Item::Fn { body, .. } = item
            && let [Stmt::Ret { value: Some(e), .. }] = body.as_slice()
        {
            let path = match e {
                Expr::Call { callee, .. } => &**callee,
                other => other,
            };
            if let Expr::Path { ty, .. } = path {
                seen.push(r.variant(ty.id));
                index += 1;
            }
        }
    }
    assert_eq!(index, 2);
    assert_eq!(
        seen,
        [
            Some(VariantRef { item: 0, index: 1 }),
            Some(VariantRef { item: 0, index: 0 })
        ]
    );
}

#[test]
fn a_second_variant_with_a_name_is_s002_at_its_name() {
    assert_eq!(
        errors("enum E: UInt[1] { A = 0, B = 1, A = 1 }"),
        [(S002, 1, 33)]
    );
    assert_eq!(
        first_message("enum E: UInt[1] { A = 0, A = 1 }"),
        "the variant `A` is already declared in this enum; rename one of the two variants"
    );
    ok("enum E: UInt[1] { A = 0 }\nenum F: UInt[1] { A = 0 }");
    assert_eq!(
        errors(&format!("{OPS}fn Op() -> Bool {{}}")),
        [(S002, 2, 4)]
    );
}

#[test]
fn an_unknown_variant_is_s003_at_the_second_part() {
    let src = format!("{OPS}fn f() -> Op {{ return Op::Mul; }}");
    assert_eq!(errors(&src), [(S003, 2, 27)]);
    assert_eq!(
        first_message(&src),
        "`Op` has no variant `Mul`; use a variant that `Op` declares"
    );
}

#[test]
fn a_first_part_that_is_no_enum_is_s003_at_the_path() {
    let src = format!("{OPS}fn f() -> Op {{ return std::x; }}");
    assert_eq!(errors(&src), [(S003, 2, 23)]);
    assert_eq!(
        first_message(&src),
        "`std` is not an enum, so `std::x` names no variant; use the name of an enum"
    );
    assert_eq!(
        errors("struct S { a: Bool }\nfn f() -> S { return S::a; }"),
        [(S003, 2, 22)]
    );
    assert_eq!(errors("fn f() -> Bool { return f::a; }"), [(S003, 1, 25)]);
    assert_eq!(
        errors("module M() {}\nfn f() -> Bool { return M::a; }"),
        [(S003, 2, 25)]
    );
    assert_eq!(
        errors("fn f() -> Bool { return Bool::A; }"),
        [(S003, 1, 25)]
    );
    // A `type` alias of an enum is no enum item.
    assert_eq!(
        errors(&format!(
            "{OPS}type A = Op;\nfn f() -> Op {{ return A::Add; }}"
        )),
        [(S003, 3, 23)]
    );
}

#[test]
fn a_local_or_a_parameter_shadows_an_enum_in_a_path() {
    assert_eq!(
        errors(&format!("{OPS}fn f(Op: Nat) -> Nat {{ return Op::Add; }}")),
        [(S003, 2, 31)]
    );
    assert_eq!(
        errors(&format!(
            "{OPS}fn f() -> Op {{ let Op = 1; return Op::Add; }}"
        )),
        [(S003, 2, 35)]
    );
    ok(&format!(
        "{OPS}fn f() -> Op {{ {{ let Op = 1; }} return Op::Add; }}"
    ));
}

#[test]
fn the_parts_of_an_enum_resolve_in_the_item_scope() {
    assert_eq!(errors("enum E: T { A = 0 }"), [(S003, 1, 9)]);
    assert_eq!(errors("enum E: UInt[1] { A(Q) = 0 }"), [(S003, 1, 21)]);
    assert_eq!(errors("enum E: UInt[1] { A = N }"), [(S003, 1, 23)]);
    ok("const N: Nat = 1;\nstruct S { a: Bool }\nenum E: UInt[N] { A(S, E) = N }");
}

// Patterns (slice 3, section 5.6)

const PAIR: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n";

/// A function `f` whose `return` is a `match` with the arms `arms`, on line 3 from column 20.
fn arms(arms: &str) -> String {
    format!("{PAIR}fn f(x: Op, p: UInt[8]) -> UInt[8] {{\nreturn match (x) {{ {arms} }};\n}}")
}

#[test]
fn the_arms_of_a_match_resolve() {
    ok(&arms(
        "Op::Add => p, Op::Load(v) => v, Op::Pair(_, w) => p, -1 => 0, true => 0, _ => 0",
    ));
    ok(&arms("Op::Pair(_, _) => p, Op::Add() => p, _ => 0"));
    ok(&arms("Op::Load(v) => v, Op::Pair(_, v) => p, _ => 0"));
}

#[test]
fn a_variant_pattern_names_its_variant_and_a_binder_is_a_local() {
    let r = ok(&arms("Op::Pair(_, w) => w, _ => 0"));
    let Some(Item::Fn { body, .. }) = r.ast().get(1) else {
        panic!("expected the function")
    };
    let [
        Stmt::Ret {
            value: Some(Expr::Match { arms, .. }),
            ..
        },
    ] = body.as_slice()
    else {
        panic!("expected a match")
    };
    let Pattern::Variant { ty, binders, .. } = &arms[0].pat else {
        panic!("expected a variant pattern")
    };
    assert_eq!(r.variant(ty.id), Some(VariantRef { item: 0, index: 2 }));
    assert!(binders[0].is_none());
    let binder = binders[1].as_ref().unwrap();
    let Some(Target::Decl(declared)) = r.target(binder.id) else {
        panic!("a binder declares a name")
    };
    assert_eq!(r.decl(declared).kind, Kind::Local);
    let Expr::Name { id, .. } = &arms[0].value else {
        panic!("expected a name")
    };
    assert_eq!(r.target(*id), Some(Target::Decl(declared)));
}

#[test]
fn a_binder_shadows_a_parameter_and_its_scope_ends_with_its_arm() {
    let r = ok(&arms("Op::Load(p) => p, _ => p"));
    // The `p` of the first value is the binder, and the `p` of the second is the parameter.
    assert_eq!(decl_at_use(&r, pos(3, 35)), Kind::Local);
    assert_eq!(decl_at_use(&r, pos(3, 43)), Kind::Param);
    assert_eq!(errors(&arms("Op::Load(v) => v, _ => v")), [(S003, 3, 43)]);
    assert_eq!(
        errors(&format!(
            "{PAIR}fn f(x: Op) -> UInt[8] {{\nlet a = match (x) {{ Op::Load(v) => v, _ => 0 }};\nreturn v;\n}}"
        )),
        [(S003, 4, 8)]
    );
}

#[test]
fn a_nested_match_opens_its_own_scopes() {
    ok(&arms(
        "Op::Load(v) => match (x) { Op::Load(v) => v, _ => v }, _ => 0",
    ));
}

#[test]
fn the_path_resolves_before_the_binders() {
    ok(&arms("Op::Load(Op) => Op, Op::Add => p, _ => 0"));
}

#[test]
fn two_binders_with_one_name_are_s002_at_the_second() {
    let src = arms("Op::Pair(a, a) => p, _ => 0");
    assert_eq!(errors(&src), [(S002, 3, 32)]);
    assert_eq!(first_message(&src), "`a` is already declared in this scope");
}

#[test]
fn a_pattern_path_has_the_s003_texts_of_a_variant_path() {
    let src = arms("Op::Mul => p, _ => 0");
    assert_eq!(errors(&src), [(S003, 3, 24)]);
    assert_eq!(
        first_message(&src),
        "`Op` has no variant `Mul`; use a variant that `Op` declares"
    );
    let src = arms("p::Add => 0, _ => 0");
    assert_eq!(errors(&src), [(S003, 3, 20)]);
    assert_eq!(
        first_message(&src),
        "`p` is not an enum, so `p::Add` names no variant; use the name of an enum"
    );
    assert_eq!(
        errors(&format!(
            "{PAIR}fn f(x: Op) -> UInt[8] {{\nlet Op = 1;\nreturn match (x) {{ Op::Add => 0 }};\n}}"
        )),
        [(S003, 4, 20)]
    );
    assert_eq!(errors(&arms("_ => q")), [(S003, 3, 25)]);
    assert_eq!(
        errors(&format!(
            "{PAIR}fn f(x: Op) -> UInt[8] {{\nreturn match (q) {{ _ => 0 }};\n}}"
        )),
        [(S003, 3, 15)]
    );
}

#[test]
fn pass_2_comes_before_pass_3_in_a_match() {
    assert_eq!(
        errors(&arms("Op::Mul => q, Op::Pair(a, a) => 0")),
        [(S002, 3, 46)]
    );
}

#[test]
fn a_binder_in_a_signature_does_not_make_a_function_generic() {
    let generic = |src: &str| {
        let r = ok(src);
        r.decl(r.item("g").unwrap()).generic
    };
    assert!(!generic(&format!(
        "{PAIR}fn g(y: UInt[match (Op::Load(8)) {{ Op::Load(v) => v, _ => 1 }}]) -> Bool {{ return true; }}"
    )));
    assert!(generic(&format!(
        "{PAIR}fn g(n: Nat, y: UInt[match (n) {{ _ => n }}]) -> Bool {{ return true; }}"
    )));
}

#[test]
fn a_binder_of_an_expression_has_its_own_declaration() {
    let file = ok(PAIR);
    let expr = run_expr(PAIR, "match (Op::Load(3)) { Op::Load(v) => v, _ => 0 }").unwrap();
    let Expr::Match { arms, .. } = expr.expr() else {
        panic!("expected a match")
    };
    let Pattern::Variant { binders, .. } = &arms[0].pat else {
        panic!("expected a variant pattern")
    };
    let binder = binders[0].as_ref().unwrap();
    let Some(Target::Decl(id)) = expr.target(binder.id) else {
        panic!("a binder declares a name")
    };
    assert_eq!(expr.decl(&file, id).kind, Kind::Local);
    assert_eq!(expr.decl(&file, id).name, "v");
    let Expr::Name { id: used, .. } = &arms[0].value else {
        panic!("expected a name")
    };
    assert_eq!(expr.target(*used), Some(Target::Decl(id)));
}

fn mod_body(body: &str) -> String {
    format!("module M(comptime W: Nat) {{\n{body}\n}}")
}

#[test]
fn a_port_family_has_one_binder_for_all_its_declarations() {
    let src = mod_body(
        "comptime for i in 0..2 {\ninput req[i]: Bool;\n}\noutput o: Bool;\n\
         comptime for j in 0..2 {\no := req[j];\n}",
    );
    let r = ok(&src);
    let declared = target_at(&r, find(&src, "req[i]"));
    let used = target_at(&r, find(&src, "req[j]"));
    assert!(matches!(declared, Some(Target::Decl(_))));
    assert_eq!(declared, used);
    assert_eq!(
        decl_at_use(&r, find(&src, "req[j]")),
        Kind::Family { input: true }
    );
    // Each indexed declaration of a name, at each depth, takes the one binder.
    let src = mod_body("output g[0]: Bool;\n{\noutput g[1]: Bool;\n}\noutput g[2]: Bool;");
    let r = ok(&src);
    let first = target_at(&r, find(&src, "g[0]"));
    assert_eq!(first, target_at(&r, find(&src, "g[1]")));
    assert_eq!(first, target_at(&r, find(&src, "g[2]")));
    assert_eq!(
        decl_at_use(&r, find(&src, "g[0]")),
        Kind::Family { input: false }
    );
    // A use before the first declaration resolves.
    let src = mod_body("output o: Bool;\no := req[0];\ninput req[0]: Bool;");
    let r = ok(&src);
    assert_eq!(
        decl_at_use(&r, find(&src, "req[0];\ninput")),
        Kind::Family { input: true }
    );
    ok(&mod_body("input req[0]: Bool;\ninput req[1]: Bool;"));
}

#[test]
fn a_nested_let_shadows_a_port_family() {
    let src = mod_body("input req[0]: Bool;\n{\nlet req = 1;\nlet y = req;\n}");
    let r = ok(&src);
    assert_eq!(decl_at_use(&r, find(&src, "req;\n}")), Kind::Local);
}

#[test]
fn an_indexed_port_of_a_comptime_fn_declares_a_local() {
    let src = "comptime fn f(p: Bool) -> Bool {\ninput req[0]: Bool;\nreturn p;\n}";
    let r = ok(src);
    assert_eq!(decl_at_use(&r, find(src, "req[0]")), Kind::Input);
}

/// The family walk also runs on the body of a `fn` without `comptime` (section 5.6). A family
/// of a helper has the scope of the helper body.
#[test]
fn a_helper_body_has_the_scope_of_its_port_families() {
    let src = fn_body("comptime for i in 0..2 {\ninput req[i]: Bool;\n}\nreturn req[0];");
    let r = ok(&src);
    assert_eq!(
        decl_at_use(&r, find(&src, "req[0]")),
        Kind::Family { input: true }
    );
    assert_eq!(
        target_at(&r, find(&src, "req[0]")),
        target_at(&r, find(&src, "req[i]"))
    );
    // A use before the first declaration resolves in a helper too.
    let src = fn_body("let x = req[0];\ninput req[0]: Bool;\nreturn p;");
    let r = ok(&src);
    assert_eq!(
        decl_at_use(&r, find(&src, "req[0];")),
        Kind::Family { input: true }
    );
}

#[test]
fn a_helper_body_has_the_collisions_of_a_module_body() {
    let plain = "`req` is already declared in this scope";
    let scalar =
        "`req` names a port family and a scalar port, here and at 2:7; use one form for the name";
    let src = fn_body("input req: Bool;\n{\ninput req[0]: Bool;\n}\nreturn p;");
    assert_eq!(errors(&src)[0], (S002, 4, 7));
    assert_eq!(message(&src), scalar);
    let src = fn_body("input req[0]: Bool;\noutput req[1]: Bool;\nreturn p;");
    assert_eq!(errors(&src)[0], (S002, 3, 8));
    for (src, line, col) in [
        (
            fn_body("let req = 1;\ninput req[0]: Bool;\nreturn p;"),
            3,
            7,
        ),
        (
            "fn f(req: Bool) -> Bool {\ninput req[0]: Bool;\nreturn req;\n}".to_owned(),
            2,
            7,
        ),
    ] {
        assert_eq!(errors(&src)[0], (S002, line, col), "{src}");
        assert_eq!(message(&src), plain, "{src}");
    }
}

#[test]
fn the_module_body_cannot_select_a_family_that_only_a_helper_declares() {
    let src = "fn lane() -> Nat {\ninput req[0]: Bool;\nreturn 0;\n}\n\
               module M() {\nlet x = lane();\nlet y = req[0];\n}";
    assert_eq!(errors(src), [(S003, 7, 9)]);
}

#[test]
fn a_keyed_port_is_no_port_name_of_the_family_walk() {
    let plain = "`req` is already declared in this scope";
    for (src, line, col) in [
        (
            mod_body("input req: Bool as \"x\";\ninput req[0]: Bool;"),
            3,
            7,
        ),
        (
            fn_body("input req[0]: Bool;\noutput req: Bool as \"x\";\nreturn p;"),
            3,
            8,
        ),
    ] {
        assert_eq!(errors(&src)[0], (S002, line, col), "{src}");
        assert_eq!(message(&src), plain, "{src}");
    }
    // The key resolves after the type, and its names are ordinary uses.
    let src = mod_body("input a: Bool as \"x\" + str(W);");
    let r = ok(&src);
    assert_eq!(decl_at_use(&r, find(&src, "W)")), Kind::Param);
}

#[test]
fn a_family_and_a_scalar_port_of_one_name_are_s002() {
    let scalar = |at: &str| {
        format!(
            "`req` names a port family and a scalar port, here and at {at}; use one form for the name"
        )
    };
    for (body, line, col, earlier) in [
        ("input req: Bool;\n{\ninput req[0]: Bool;\n}", 4, 7, "2:7"),
        ("{\ninput req[0]: Bool;\n}\noutput req: Bool;", 5, 8, "3:7"),
        (
            "comptime if (true) {\ninput req: Bool;\n}\noutput req[0]: Bool;",
            5,
            8,
            "3:7",
        ),
    ] {
        let src = mod_body(body);
        assert_eq!(errors(&src)[0], (S002, line, col), "{body}");
        assert_eq!(message(&src), scalar(earlier), "{body}");
    }
}

#[test]
fn a_family_with_two_directions_is_s002_at_the_second_direction() {
    let src = mod_body("input req[0]: Bool;\ncomptime if (true) {\noutput req[1]: Bool;\n}");
    assert_eq!(errors(&src), [(S002, 4, 8)]);
    assert_eq!(
        message(&src),
        "the port family `req` has an input entry and an output entry, here and at 2:7; give \
         the entries of one direction another name"
    );
}

#[test]
fn a_family_and_another_name_of_the_body_scope_is_the_ordinary_s002() {
    let plain = "`req` is already declared in this scope";
    for (src, line, col) in [
        (
            "module M(comptime req: Nat) {\ninput req[0]: Bool;\n}".to_owned(),
            2,
            7,
        ),
        (mod_body("let req = 1;\n{\ninput req[0]: Bool;\n}"), 4, 7),
        (mod_body("{\ninput req[0]: Bool;\n}\nlet req = 1;"), 5, 5),
        (mod_body("let req = 1;\ninput req[0]: Bool;"), 3, 7),
    ] {
        assert_eq!(errors(&src)[0], (S002, line, col), "{src}");
        assert_eq!(message(&src), plain, "{src}");
    }
}

#[test]
fn an_indexed_declaration_declares_its_name_in_its_own_block() {
    let plain = "`req` is already declared in this scope";
    for (body, line, col) in [
        ("{\nlet req = 1;\ninput req[0]: Bool;\n}", 4, 7),
        ("{\ninput req[0]: Bool;\nlet req = 1;\n}", 4, 5),
        ("comptime for req in 0..2 {\ninput req[req]: Bool;\n}", 3, 7),
    ] {
        let src = mod_body(body);
        assert_eq!(errors(&src)[0], (S002, line, col), "{body}");
        assert_eq!(message(&src), plain, "{body}");
    }
}

#[test]
fn the_family_walk_needs_no_recursion_for_a_deep_nest() {
    let n = parse::DEFAULT_SYNTAX_DEPTH - 8;
    let src = mod_body(&format!(
        "{}output g[0]: Bool;{}\noutput g: Bool;",
        "comptime if (true) {\n".repeat(n),
        "\n}".repeat(n)
    ));
    assert_eq!(errors(&src).first().map(|e| e.0), Some(S002));
}

#[test]
fn the_operands_of_a_builtin_resolve_as_expressions() {
    let src = "const k: Nat = 0;\nfn f(a: Nat) -> Nat {\n    let r = @field(a, k);\n    return @TypeOf(r);\n}";
    // The base and the key are names like any other, and `r` is the local of the `let`.
    let r = ok(src);
    for at in [pos(3, 20), pos(3, 23), pos(4, 20)] {
        assert!(target_at(&r, at).is_some(), "{at:?}");
    }
    assert_eq!(target_at(&r, pos(3, 23)), r.item("k").map(Target::Decl));
    // An unknown name in an operand is S003 at the name, in source order.
    let src = fn_body("let r = @field(a, b);\nreturn @TypeOf(c);");
    assert_eq!(errors(&src), [(S003, 2, 16), (S003, 2, 19), (S003, 3, 16)]);
    assert_eq!(message(&src), "`a` is not declared");
}

#[test]
fn the_operands_of_a_builtin_in_a_type_resolve_as_expressions() {
    let r = ok(&fn_body(
        "let q: Bool = p;\nlet x: @TypeOf(q) = p;\nreturn p;",
    ));
    assert!(target_at(&r, pos(3, 16)).is_some());
    // An unknown name in an operand is S003 at the name, also inside array and function types.
    for (ty, want) in [
        ("@TypeOf(c)", vec![(S003, 2, 16)]),
        ("@Struct(c)", vec![(S003, 2, 16)]),
        ("[@TypeOf(c); 2]", vec![(S003, 2, 17)]),
        (
            "fn (@TypeOf(c)) -> @Struct(d)",
            vec![(S003, 2, 20), (S003, 2, 35)],
        ),
    ] {
        let src = fn_body(&format!("let x: {ty} = p;\nreturn p;"));
        assert_eq!(errors(&src), want, "{ty}");
    }
}

#[test]
fn the_argument_of_typeinfo_resolves_as_an_expression() {
    let r = ok("const k: Nat = 0;\nfn f(a: Nat) -> Nat {\n    return @typeInfo(a + k);\n}");
    for at in [pos(3, 22), pos(3, 26)] {
        assert!(target_at(&r, at).is_some(), "{at:?}");
    }
    let src = fn_body("return @typeInfo(Q);");
    assert_eq!(errors(&src), [(S003, 2, 18)]);
}

#[test]
fn a_builtin_in_a_signature_makes_the_function_generic() {
    assert!(generic(
        "fn f(n: Nat) -> UInt[@field(n, 0)] { return 0; }",
        "f"
    ));
    assert!(generic(
        "fn f(n: Nat) -> [Nat; @field(n, 0)] { return 0; }",
        "f"
    ));
    assert!(!generic(
        "const k: Nat = 0;\nfn f(n: Nat) -> UInt[@field(k, 0)] { return 0; }",
        "f"
    ));
}

#[test]
fn a_builtin_has_no_call_site_and_its_operands_count_in_pre_order() {
    assert_eq!(
        sites(&fn_body(
            "let a = @field(len(p), len(p));\nreturn len(@field(p, len(p)));"
        )),
        [0, 1, 2, 3]
    );
}

#[test]
fn a_deep_chain_of_builtins_resolves() {
    let n = parse::DEFAULT_SYNTAX_DEPTH - 8;
    let chain = format!("{}p{}", "@field(".repeat(n), ", 0)".repeat(n));
    ok(&fn_body(&format!("let a = {chain};\nreturn p;")));
}
