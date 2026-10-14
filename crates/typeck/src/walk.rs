// SPDX-License-Identifier: Apache-2.0
//! One walk over the resolved AST in source order. It recurses over blocks and expressions,
//! so it runs on the front-end thread.

use crate::{Code, Error};
use parse::ast::{Expr, FnParam, Item, NodeId, Param, ParamMode, Pos, Stmt, TypeExpr};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
use std::collections::{BTreeMap, BTreeSet};

/// The item whose body is open, for `S006`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Module,
    Fn,
    ComptimeFn,
}

/// The signature of an item that a call, an instance, or a type name needs.
enum Sig {
    /// A function: its `comptime` mark and the mode of each parameter. Each parameter of a
    /// `comptime fn` is static.
    Fn {
        comptime: bool,
        modes: Vec<ParamMode>,
    },
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

/// Which parameters of a callee are static positions.
#[derive(Clone, Copy)]
enum Statics {
    /// A function: every parameter of a `comptime fn`, else each `comptime` parameter.
    Params { comptime: bool },
    /// Every argument: `static_assert` and `error` take messages.
    All,
}

/// A function that a call names: the modes of its parameters and its static positions. A
/// constructor `T(n)` has no modes, and its argument is static.
#[derive(Clone, Copy)]
struct Callee<'a> {
    modes: &'a [ParamMode],
    statics: Statics,
}

impl Callee<'_> {
    fn is_static(&self, k: usize) -> bool {
        match self.statics {
            Statics::Params { comptime } => {
                comptime || self.modes.get(k) == Some(&ParamMode::Comptime)
            }
            Statics::All => true,
        }
    }

    /// The mode of the parameter `k`.
    fn mode(&self, k: usize) -> ParamMode {
        self.modes.get(k).copied().unwrap_or(ParamMode::None)
    }
}

fn prelude_statics(p: Prelude) -> Statics {
    match p {
        Prelude::StaticAssert | Prelude::Error => Statics::All,
        _ => Statics::Params { comptime: false },
    }
}

/// Whether a call or a static position makes an expression static: the context, or the callee.
fn static_at(is_static: bool, callee: Option<&Callee<'_>>, k: usize) -> bool {
    is_static || callee.is_some_and(|c| c.is_static(k))
}

pub(crate) fn run(resolved: &Resolved) -> Vec<Error> {
    let sigs = sigs(resolved);
    let mut walker = Walker {
        resolved,
        expr: None,
        sigs: &sigs,
        errors: Vec::new(),
        seq: 0,
        mutable: BTreeSet::new(),
        pending: BTreeMap::new(),
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
        mutable: BTreeSet::new(),
        pending: BTreeMap::new(),
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
                Sig::Fn {
                    comptime: *comptime,
                    modes: params.iter().map(|p| p.mode).collect(),
                },
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
    /// The `let mut` locals and the `mut` formals: the mutable roots.
    mutable: BTreeSet<DeclId>,
    /// For each root, the number of open windows that hold it as pending. A `mut` actual reads
    /// and changes only the counter of its root, so it needs no scan of the open windows.
    pending: BTreeMap<DeclId, usize>,
}

fn type_arity(p: Prelude) -> usize {
    match p {
        Prelude::UInt | Prelude::SInt | Prelude::List => 1,
        _ => 0,
    }
}

fn resource(kind: Kind) -> Option<&'static str> {
    match kind {
        Kind::Input | Kind::Output => Some("a port"),
        Kind::Reg => Some("a register"),
        Kind::Wire => Some("a wire"),
        Kind::Mem => Some("a memory"),
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

    /// The parameter that the receiver of the method node with an id binds to.
    fn receiver_of(&self, id: NodeId) -> Option<usize> {
        match self.expr {
            Some(expr) => expr.receiver(id),
            None => self.resolved.receiver(id),
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
                Sig::Fn { .. } | Sig::Module(_) => None,
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

    /// The function that a name node points to: a `fn` item or a prelude function. Another
    /// name has no known parameters.
    fn callee(&self, id: NodeId) -> Option<Callee<'a>> {
        match self.target(id)? {
            Target::Decl(id) => match self.sigs.get(&id)? {
                Sig::Fn { comptime, modes } => Some(Callee {
                    modes,
                    statics: Statics::Params {
                        comptime: *comptime,
                    },
                }),
                _ => None,
            },
            Target::Prelude(p) if p.is_type() => None,
            Target::Prelude(p) => Some(Callee {
                modes: p.modes(),
                statics: prelude_statics(p),
            }),
        }
    }

    /// Checks the arity of a call at `pos` with `got` arguments. `head` is the type head of a
    /// type callee. The result is the callee.
    fn call(
        &mut self,
        pos: Pos,
        callee: &Expr,
        head: Option<&Head>,
        got: usize,
    ) -> Option<Callee<'a>> {
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
                    Some(Callee {
                        modes: &[],
                        statics: Statics::All,
                    })
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
                    None
                }
                Ctor::Unknown => None,
            };
        }
        let Expr::Name { id, name, .. } = callee else {
            return None;
        };
        let callee = self.callee(*id)?;
        self.arity(pos, &format!("`{name}`"), callee.modes.len(), got);
        Some(callee)
    }

    /// Checks the receiver call `node` at `pos` to the function with the name node `id`,
    /// which has `got` explicit arguments. The receiver binds to the parameter that `resolve`
    /// recorded. The result is the callee and the index of that parameter, or `None` after an
    /// `S007`.
    fn receiver(
        &mut self,
        pos: Pos,
        node: NodeId,
        id: NodeId,
        name: &str,
        got: usize,
    ) -> Option<(Callee<'a>, usize)> {
        let callee = self.callee(id)?;
        let Some(bound) = self.receiver_of(node) else {
            self.report(
                Code::S007,
                pos,
                format!("`{name}` has no parameter without `comptime` for the receiver"),
            );
            return None;
        };
        self.arity(pos, &format!("`{name}`"), callee.modes.len(), got + 1);
        Some((callee, bound))
    }

    /// The root of a place: the declaration of the name at its base.
    fn root(&self, expr: &Expr) -> Option<DeclId> {
        let mut cur = expr;
        loop {
            match cur {
                Expr::Name { id, .. } => {
                    return match self.target(*id)? {
                        Target::Decl(id) => Some(id),
                        Target::Prelude(_) => None,
                    };
                }
                Expr::Index { base, .. } | Expr::Select { base, .. } | Expr::Field { base, .. } => {
                    cur = base;
                }
                _ => return None,
            }
        }
    }

    /// Makes the root pending for one more window.
    fn hold(&mut self, root: DeclId) {
        *self.pending.entry(root).or_insert(0) += 1;
    }

    /// Ends the windows of the roots.
    fn release(&mut self, roots: &[DeclId]) {
        for root in roots {
            if let Some(n) = self.pending.get_mut(root) {
                *n = n.saturating_sub(1);
            }
        }
    }

    /// The `mut` actual `x`, before its parts. It is `S008` if it is not a place with a
    /// mutable root, or if its root is pending. Then its root is pending. The result is the
    /// root, for `release`.
    fn mut_actual(&mut self, x: &Expr) -> Option<DeclId> {
        let Some(root) = self.root(x) else {
            self.report(
                Code::S008,
                expr_pos(x),
                "a `mut` actual is a place".to_owned(),
            );
            return None;
        };
        if !self.mutable.contains(&root) {
            self.report(
                Code::S008,
                expr_pos(x),
                "a `mut` actual has a `let mut` local or a `mut` formal as its root".to_owned(),
            );
            return None;
        }
        if self.pending.get(&root).copied().unwrap_or(0) > 0 {
            self.report(
                Code::S008,
                expr_pos(x),
                "the root of this `mut` actual is pending in its window".to_owned(),
            );
        }
        self.hold(root);
        Some(root)
    }

    /// The check of the actual `x` at the parameter `k` of the callee, before its parts. The
    /// result is the root that it makes pending.
    fn pre(&mut self, callee: Option<&Callee<'_>>, k: usize, x: &Expr) -> Option<DeclId> {
        if callee.is_some_and(|c| c.mode(k) == ParamMode::Mut) {
            self.mut_actual(x)
        } else {
            None
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
                let target = self.call(*pos, callee, head.as_ref(), args.len());
                let mut roots = Vec::new();
                for (k, arg) in args.iter().enumerate() {
                    roots.extend(self.pre(target.as_ref(), k, arg));
                    self.expr(static_at(is_static, target.as_ref(), k), arg);
                }
                self.release(&roots);
                None
            }
            Expr::Method {
                pos,
                id,
                recv,
                name,
                args,
            } => {
                // The receiver evaluates first. It binds to the parameter `bound`, so the
                // argument `k` binds to the parameter `k` before `bound` and to `k + 1` from
                // `bound` on.
                let bound = self.receiver(*pos, *id, name.id, &name.name, args.len());
                let callee = bound.map(|(c, _)| c);
                let at = bound.map_or(0, |(_, b)| b);
                let mut held = Vec::new();
                held.extend(self.pre(callee.as_ref(), at, recv));
                self.expr(static_at(is_static, callee.as_ref(), at), recv);
                for (k, arg) in args.iter().enumerate() {
                    let j = if k < at { k } else { k + 1 };
                    held.extend(self.pre(callee.as_ref(), j, arg));
                    self.expr(static_at(is_static, callee.as_ref(), j), arg);
                }
                self.release(&held);
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
            Expr::FnType { params, ret, .. } => {
                self.fn_type(params, ret);
                Some(Head {
                    text: "a function type".to_owned(),
                    missing: 0,
                    ctor: Ctor::Unknown,
                })
            }
        }
    }

    /// The parameter types and the result type of a function type.
    fn fn_type(&mut self, params: &[FnParam], ret: &TypeExpr) {
        for param in params {
            self.type_expr(&param.ty);
        }
        self.type_expr(ret);
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
                    let what = if matches!(**base, TypeExpr::Fn { .. }) {
                        "a function type"
                    } else {
                        "a complete type"
                    };
                    self.arity(*pos, what, 0, args.len());
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
            TypeExpr::Fn { params, ret, .. } => self.fn_type(params, ret),
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
            Stmt::Local {
                mutable,
                name,
                ty,
                value,
                ..
            } => {
                if let Some(ty) = ty {
                    self.type_expr(ty);
                }
                self.expr(false, value);
                if *mutable {
                    self.declare_mutable(name.id);
                }
            }
            Stmt::Assign { target, value, .. } => {
                let root = self.root(target);
                if let Some(root) = root {
                    self.hold(root);
                }
                self.expr(false, target);
                self.expr(false, value);
                self.release(root.as_slice());
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
            Stmt::Mem {
                pos, word, depth, ..
            } => {
                self.placement(owner, *pos, "memory");
                self.type_expr(word);
                self.expr(true, depth);
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
            if param.mode == ParamMode::Mut {
                self.declare_mutable(param.name.id);
            }
        }
    }

    /// Records the declaration of the name node as a mutable root.
    fn declare_mutable(&mut self, id: NodeId) {
        if let Some(Target::Decl(decl)) = self.target(id) {
            self.mutable.insert(decl);
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

/// The position of an expression.
fn expr_pos(expr: &Expr) -> Pos {
    match expr {
        Expr::Num { pos, .. }
        | Expr::Bool { pos, .. }
        | Expr::Str { pos, .. }
        | Expr::Name { pos, .. }
        | Expr::Unary { pos, .. }
        | Expr::Binary { pos, .. }
        | Expr::Cond { pos, .. }
        | Expr::Call { pos, .. }
        | Expr::Method { pos, .. }
        | Expr::Index { pos, .. }
        | Expr::Field { pos, .. }
        | Expr::Unit { pos }
        | Expr::Tuple { pos, .. }
        | Expr::Array { pos, .. }
        | Expr::Select { pos, .. }
        | Expr::ArrayType { pos, .. }
        | Expr::FnType { pos, .. } => *pos,
    }
}
