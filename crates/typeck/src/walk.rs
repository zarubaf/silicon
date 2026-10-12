// SPDX-License-Identifier: Apache-2.0
//! One walk over the resolved AST in source order. It recurses over blocks and expressions,
//! so it runs on the front-end thread.

use crate::{Code, Error};
use parse::ast::{Expr, Item, NodeId, Param, Pos, Stmt, TypeExpr};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
use std::collections::BTreeMap;

/// The item whose body is open, for `S006`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Module,
    Fn,
    ComptimeFn,
}

/// The signature of an item that a call, an instance, or a type name needs.
enum Sig {
    /// A function: a flag for each parameter, true for a static one. Each parameter of a
    /// `comptime fn` is static.
    Fn(Vec<bool>),
    /// A module: its number of parameters.
    Module(usize),
    /// A struct: its number of parameters and its number of fields.
    Struct { params: usize, fields: usize },
    /// A `type` item. Only elaboration knows its type.
    Alias,
}

/// The rule of a constructor call `T(...)`.
#[derive(Clone, Copy)]
enum Ctor {
    /// A prelude type or an array type: no argument, or one static argument.
    Convert,
    /// A struct: no argument, or one argument for each field.
    Record(usize),
    /// A `type` item: elaboration checks the call.
    Unknown,
}

/// A type in an expression or a type name: its text for a message, the number of index
/// arguments it misses, and its constructor rule.
struct Head {
    text: String,
    missing: usize,
    ctor: Ctor,
}

impl Head {
    /// The head of a type that an index or an array type makes: a complete type.
    fn complete(ctor: Ctor) -> Head {
        Head {
            text: "a complete type".to_owned(),
            missing: 0,
            ctor,
        }
    }
}

/// Which arguments of a call are static positions.
enum Statics<'a> {
    /// A flag for each argument of a function item.
    Flags(&'a [bool]),
    /// Only the first argument: `resize` and `reinterpret`.
    First,
    All,
    Nobody,
}

impl Statics<'_> {
    fn at(&self, k: usize) -> bool {
        match self {
            Statics::Flags(flags) => flags.get(k).copied().unwrap_or(false),
            Statics::First => k == 0,
            Statics::All => true,
            Statics::Nobody => false,
        }
    }
}

pub(crate) fn run(resolved: &Resolved) -> Vec<Error> {
    let sigs = sigs(resolved);
    let mut walker = Walker {
        resolved,
        expr: None,
        sigs: &sigs,
        errors: Vec::new(),
        seq: 0,
    };
    for item in resolved.ast() {
        walker.item(item);
    }
    walker.finish()
}

/// Checks an expression in the file scope as a static position, as Lean `Check.checkExpr`
/// does.
pub(crate) fn run_expr(resolved: &Resolved, expr: &ResolvedExpr) -> Vec<Error> {
    let sigs = sigs(resolved);
    let mut walker = Walker {
        resolved,
        expr: Some(expr),
        sigs: &sigs,
        errors: Vec::new(),
        seq: 0,
    };
    walker.expr(true, expr.expr());
    walker.finish()
}

/// The signatures of the functions, the modules, the structs, and the aliases of the file.
fn sigs(resolved: &Resolved) -> BTreeMap<DeclId, Sig> {
    let mut sigs = BTreeMap::new();
    for item in resolved.ast() {
        let (name, sig) = match item {
            Item::Const { .. } => continue,
            Item::Fn {
                comptime,
                name,
                params,
                ..
            } => (
                name,
                Sig::Fn(params.iter().map(|p| *comptime || p.comptime).collect()),
            ),
            Item::Module { name, params, .. } => (name, Sig::Module(params.len())),
            Item::Struct {
                name,
                params,
                fields,
                ..
            } => (
                name,
                Sig::Struct {
                    params: params.len(),
                    fields: fields.len(),
                },
            ),
            Item::Alias { name, .. } => (name, Sig::Alias),
        };
        if let Some(Target::Decl(id)) = resolved.target(name.id) {
            sigs.insert(id, sig);
        }
    }
    sigs
}

struct Walker<'a> {
    resolved: &'a Resolved,
    /// The expression of the command line, whose names have their own map of targets.
    expr: Option<&'a ResolvedExpr>,
    sigs: &'a BTreeMap<DeclId, Sig>,
    /// The errors with their order in the walk, which breaks a tie of positions.
    errors: Vec<(usize, Error)>,
    /// The next order number.
    seq: usize,
}

fn type_arity(p: Prelude) -> usize {
    match p {
        Prelude::UInt | Prelude::SInt => 1,
        _ => 0,
    }
}

fn fn_arity(p: Prelude) -> usize {
    match p {
        Prelude::Error | Prelude::Len | Prelude::DataBits => 1,
        _ => 2,
    }
}

fn resource(kind: Kind) -> Option<&'static str> {
    match kind {
        Kind::Input | Kind::Output => Some("a port"),
        Kind::Reg => Some("a register"),
        Kind::Wire => Some("a wire"),
        Kind::Instance => Some("an instance"),
        _ => None,
    }
}

impl<'a> Walker<'a> {
    /// What the name node with an id points to.
    fn target(&self, id: NodeId) -> Option<Target> {
        match self.expr {
            Some(expr) => expr.target(id),
            None => self.resolved.target(id),
        }
    }

    /// The errors in position order.
    fn finish(mut self) -> Vec<Error> {
        // The sort is stable, so at one position the first error of the walk stays first.
        self.errors.sort_by_key(|(seq, e)| (e.pos, *seq));
        self.errors.into_iter().map(|(_, e)| e).collect()
    }

    fn tick(&mut self) -> usize {
        self.seq += 1;
        self.seq
    }

    fn report(&mut self, code: Code, pos: Pos, message: String) {
        let seq = self.tick();
        self.errors.push((seq, Error { code, pos, message }));
    }

    /// `S007` at `pos` if `what` has `got` arguments, not `want`.
    fn arity(&mut self, pos: Pos, what: &str, want: usize, got: usize) {
        if want != got {
            self.report(
                Code::S007,
                pos,
                format!("{what} takes {want} argument(s), but it has {got}"),
            );
        }
    }

    /// The head of a type name. A struct misses its parameters. A `type` item is a complete
    /// type. A local has no known head.
    fn head(&self, id: NodeId, name: &str) -> Option<Head> {
        let text = format!("`{name}`");
        match self.target(id)? {
            Target::Prelude(p) if p.is_type() => Some(Head {
                text,
                missing: type_arity(p),
                ctor: Ctor::Convert,
            }),
            Target::Prelude(_) => None,
            Target::Decl(id) => match self.sigs.get(&id)? {
                Sig::Struct { params, fields } => Some(Head {
                    text,
                    missing: *params,
                    ctor: Ctor::Record(*fields),
                }),
                Sig::Alias => Some(Head {
                    text,
                    missing: 0,
                    ctor: Ctor::Unknown,
                }),
                Sig::Fn(_) | Sig::Module(_) => None,
            },
        }
    }

    /// A name that is not a type. A resource in a static position is `S005`.
    fn resource_name(&mut self, is_static: bool, pos: Pos, id: NodeId, name: &str) {
        if let Some(Target::Decl(id)) = self.target(id)
            && is_static
            && let Some(what) = resource(self.resolved.decl(id).kind)
        {
            self.report(
                Code::S005,
                pos,
                format!("`{name}` is {what}; a static position needs a static value"),
            );
        }
    }

    /// Checks the arity of a call at `pos` with `got` arguments. `head` is the type head of a
    /// type callee. The result tells which arguments are static positions.
    fn call(&mut self, pos: Pos, callee: &Expr, head: Option<&Head>, got: usize) -> Statics<'a> {
        if let Some(head) = head {
            return match head.ctor {
                Ctor::Convert => {
                    if got > 1 {
                        self.report(
                            Code::S007,
                            pos,
                            format!("a constructor takes 0 or 1 argument(s), but it has {got}"),
                        );
                    }
                    Statics::All
                }
                Ctor::Record(fields) => {
                    if got != 0 && got != fields {
                        self.report(
                            Code::S007,
                            pos,
                            format!(
                                "a struct constructor takes 0 or {fields} argument(s), but it has {got}"
                            ),
                        );
                    }
                    Statics::Nobody
                }
                Ctor::Unknown => Statics::Nobody,
            };
        }
        let Expr::Name { id, name, .. } = callee else {
            return Statics::Nobody;
        };
        match self.target(*id) {
            Some(Target::Decl(id)) => {
                if let Some(Sig::Fn(flags)) = self.sigs.get(&id) {
                    self.arity(pos, &format!("`{name}`"), flags.len(), got);
                    return Statics::Flags(flags);
                }
                Statics::Nobody
            }
            Some(Target::Prelude(p)) if !p.is_type() => {
                self.arity(pos, &format!("`{name}`"), fn_arity(p), got);
                match p {
                    Prelude::Resize | Prelude::Reinterpret => Statics::First,
                    Prelude::StaticAssert | Prelude::Error => Statics::All,
                    _ => Statics::Nobody,
                }
            }
            _ => Statics::Nobody,
        }
    }

    fn expr(&mut self, is_static: bool, expr: &Expr) {
        self.visit(is_static, false, expr);
    }

    /// An expression. `is_static` is true in a static position. `base` is true for the base of
    /// an index, whose index holds the arguments of a type name. The result is the type head
    /// of a type in an expression: a type name, an index of one, or `[T; N]`. Another
    /// expression gives `None`. Thus the walk visits each node once.
    fn visit(&mut self, is_static: bool, base: bool, expr: &Expr) -> Option<Head> {
        match expr {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } | Expr::Unit { .. } => None,
            Expr::Name { pos, id, name } => {
                let head = self.head(*id, name);
                match &head {
                    Some(h) if !base => self.arity(*pos, &h.text, h.missing, 0),
                    Some(_) => {}
                    None => self.resource_name(is_static, *pos, *id, name),
                }
                head
            }
            Expr::Unary { arg, .. } => {
                self.expr(is_static, arg);
                None
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(is_static, lhs);
                self.expr(is_static, rhs);
                None
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(is_static, cond);
                self.expr(is_static, yes);
                self.expr(is_static, no);
                None
            }
            Expr::Call {
                pos, callee, args, ..
            } => {
                let head = self.visit(true, false, callee);
                let statics = self.call(*pos, callee, head.as_ref(), args.len());
                for (k, arg) in args.iter().enumerate() {
                    self.expr(is_static || statics.at(k), arg);
                }
                None
            }
            Expr::Index { pos, base, args } => {
                let head = self.visit(is_static, true, base);
                if let Some(h) = &head {
                    self.arity(*pos, &h.text, h.missing, args.len());
                }
                for arg in args {
                    self.expr(true, arg);
                }
                head.map(|h| Head::complete(h.ctor))
            }
            Expr::Field { base, .. } | Expr::Select { base, .. } => {
                self.expr(is_static, base);
                None
            }
            Expr::Tuple { elems, .. } | Expr::Array { elems, .. } => {
                for elem in elems {
                    self.expr(is_static, elem);
                }
                None
            }
            Expr::ArrayType { elem, len, .. } => {
                self.type_expr(elem);
                self.expr(true, len);
                Some(Head::complete(Ctor::Convert))
            }
        }
    }

    fn type_expr(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Name { pos, id, name } => {
                if let Some(h) = self.head(*id, name) {
                    self.arity(*pos, &h.text, h.missing, 0);
                }
            }
            TypeExpr::Index { pos, base, args } => {
                if let TypeExpr::Name { id, name, .. } = &**base {
                    if let Some(h) = self.head(*id, name) {
                        self.arity(*pos, &h.text, h.missing, args.len());
                    }
                } else {
                    self.arity(*pos, "a complete type", 0, args.len());
                    self.type_expr(base);
                }
                for arg in args {
                    self.expr(true, arg);
                }
            }
            TypeExpr::Unit { .. } => {}
            TypeExpr::Tuple { elems, .. } => {
                for elem in elems {
                    self.type_expr(elem);
                }
            }
            TypeExpr::Array { elem, len, .. } => {
                self.type_expr(elem);
                self.expr(true, len);
            }
        }
    }

    /// `S006` at `pos` if a `comptime fn` has the statement `what`.
    fn placement(&mut self, owner: Owner, pos: Pos, what: &str) {
        if owner == Owner::ComptimeFn {
            self.report(Code::S006, pos, format!("a `comptime fn` has no {what}"));
        }
    }

    fn stmts(&mut self, owner: Owner, stmts: &[Stmt]) {
        for stmt in stmts {
            self.stmt(owner, stmt);
        }
    }

    fn stmt(&mut self, owner: Owner, stmt: &Stmt) {
        match stmt {
            Stmt::Local { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.type_expr(ty);
                }
                self.expr(false, value);
            }
            Stmt::Assign { target, value, .. } => {
                self.expr(false, target);
                self.expr(false, value);
            }
            Stmt::Connect { pos, target, value } => {
                self.placement(owner, *pos, "`:=`");
                self.expr(false, target);
                self.expr(false, value);
            }
            Stmt::Reg { pos, ty, init, .. } => {
                self.placement(owner, *pos, "register");
                self.type_expr(ty);
                self.expr(true, init);
            }
            Stmt::Wire { pos, ty, .. } => {
                self.placement(owner, *pos, "wire");
                self.type_expr(ty);
            }
            Stmt::Input { pos, ty, .. } | Stmt::Output { pos, ty, .. } => {
                self.placement(owner, *pos, "port");
                self.type_expr(ty);
            }
            Stmt::Inst {
                pos, module, args, ..
            } => {
                self.placement(owner, *pos, "instance");
                if let Some(Target::Decl(id)) = self.target(module.id)
                    && let Some(Sig::Module(want)) = self.sigs.get(&id)
                {
                    let want = *want;
                    self.arity(*pos, &format!("`{}`", module.name), want, args.len());
                }
                for arg in args {
                    self.expr(true, arg);
                }
            }
            Stmt::Ret { pos, value } => {
                if owner == Owner::Module {
                    self.report(Code::S006, *pos, "a module body has no `return`".to_owned());
                }
                if let Some(value) = value {
                    self.expr(false, value);
                }
            }
            Stmt::CtIf { cond, yes, no, .. } => {
                self.expr(true, cond);
                self.stmts(owner, yes);
                if let Some(no) = no {
                    self.stmts(owner, no);
                }
            }
            Stmt::CtFor { lo, hi, body, .. } => {
                self.expr(true, lo);
                self.expr(true, hi);
                self.stmts(owner, body);
            }
            Stmt::Block { body, .. } => self.stmts(owner, body),
            Stmt::Expr { value, .. } => self.expr(false, value),
            Stmt::Alias { ty, .. } => self.type_expr(ty),
        }
    }

    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.type_expr(&param.ty);
        }
    }

    fn item(&mut self, item: &Item) {
        match item {
            Item::Const { ty, value, .. } => {
                self.type_expr(ty);
                self.expr(true, value);
            }
            Item::Fn {
                comptime,
                params,
                ret,
                body,
                ..
            } => {
                self.params(params);
                self.type_expr(ret);
                let owner = if *comptime {
                    Owner::ComptimeFn
                } else {
                    Owner::Fn
                };
                self.stmts(owner, body);
            }
            Item::Module { params, body, .. } => {
                self.params(params);
                self.stmts(Owner::Module, body);
            }
            Item::Struct { params, fields, .. } => {
                self.params(params);
                for field in fields {
                    self.type_expr(&field.ty);
                }
            }
            Item::Alias { ty, .. } => self.type_expr(ty),
        }
    }
}
