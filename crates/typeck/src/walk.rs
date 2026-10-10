//! One walk over the resolved AST in source order. It recurses over blocks and expressions,
//! so it runs on the front-end thread.

use crate::{Code, Error};
use parse::ast::{Expr, Item, Param, Pos, Stmt, TypeExpr};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
use std::collections::BTreeMap;

/// The item whose body is open, for `S006`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Module,
    Fn,
    ComptimeFn,
}

/// The signature of an item that a call or an instance needs.
enum Sig {
    /// A function: a flag for each parameter, true for a static one. Each parameter of a
    /// `comptime fn` is static.
    Fn(Vec<bool>),
    /// A module: its number of parameters.
    Module(usize),
}

/// What a call's callee tells about the arguments.
enum Callee<'a> {
    /// A function item.
    Fn(&'a [bool]),
    Prelude(Prelude),
    /// A type used as a constructor, `T(n)`.
    Constructor,
    /// A local, a constant, or another expression: elab checks it.
    Unknown,
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

/// The signatures of the functions and the modules of the file.
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
        };
        if let Some(Target::Decl(id)) = resolved.target(name.pos) {
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
        Prelude::Error => 1,
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
    /// What the name token at a position points to.
    fn target(&self, pos: Pos) -> Option<Target> {
        match self.expr {
            Some(expr) => expr.target(pos),
            None => self.resolved.target(pos),
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
        self.report_at(seq, code, pos, message);
    }

    fn report_at(&mut self, seq: usize, code: Code, pos: Pos, message: String) {
        self.errors.push((seq, Error { code, pos, message }));
    }

    /// `S007` at `pos` if `what` has `got` arguments, not `want`.
    fn arity(&mut self, pos: Pos, what: &str, want: usize, got: usize) {
        let seq = self.tick();
        self.arity_at(seq, pos, what, want, got);
    }

    fn arity_at(&mut self, seq: usize, pos: Pos, what: &str, want: usize, got: usize) {
        if want != got {
            self.report_at(
                seq,
                Code::S007,
                pos,
                format!("{what} takes {want} argument(s), but it has {got}"),
            );
        }
    }

    fn prelude_type(&self, pos: Pos) -> Option<Prelude> {
        match self.target(pos) {
            Some(Target::Prelude(p)) if p.is_type() => Some(p),
            _ => None,
        }
    }

    /// The name and the number of missing index arguments of a type in an expression: `T`
    /// or an index of it. A complete type misses none. Another expression is not a type.
    fn type_head(&self, expr: &Expr) -> Option<(String, usize)> {
        match expr {
            Expr::Name { pos, name } => self
                .prelude_type(*pos)
                .map(|p| (format!("`{name}`"), type_arity(p))),
            Expr::Index { base, .. } => self
                .type_head(base)
                .map(|_| ("a complete type".to_owned(), 0)),
            _ => None,
        }
    }

    /// A name. A type name has no index here. A resource in a static position is `S005`.
    fn name(&mut self, is_static: bool, pos: Pos, name: &str) {
        match self.target(pos) {
            Some(Target::Prelude(p)) if p.is_type() => {
                self.arity(pos, &format!("`{name}`"), type_arity(p), 0);
            }
            Some(Target::Decl(id)) if is_static => {
                if let Some(what) = resource(self.resolved.decl(id).kind) {
                    self.report(
                        Code::S005,
                        pos,
                        format!("`{name}` is {what}; a static position needs a static value"),
                    );
                }
            }
            _ => {}
        }
    }

    /// Checks the arity of a call. The result tells which arguments are static positions.
    fn callee(&mut self, pos: Pos, callee: &Expr, got: usize) -> Callee<'a> {
        if let Expr::Name { pos: at, name } = callee {
            match self.target(*at) {
                Some(Target::Decl(id)) => {
                    if let Some(Sig::Fn(flags)) = self.sigs.get(&id) {
                        self.arity(pos, &format!("`{name}`"), flags.len(), got);
                        return Callee::Fn(flags);
                    }
                    return Callee::Unknown;
                }
                Some(Target::Prelude(p)) if !p.is_type() => {
                    self.arity(pos, &format!("`{name}`"), fn_arity(p), got);
                    return Callee::Prelude(p);
                }
                _ => {}
            }
        }
        if self.type_head(callee).is_some() {
            self.arity(pos, "a constructor", 1, got);
            return Callee::Constructor;
        }
        Callee::Unknown
    }

    fn expr(&mut self, is_static: bool, expr: &Expr) {
        match expr {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } => {}
            Expr::Name { pos, name } => self.name(is_static, *pos, name),
            Expr::Unary { arg, .. } => self.expr(is_static, arg),
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(is_static, lhs);
                self.expr(is_static, rhs);
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(is_static, cond);
                self.expr(is_static, yes);
                self.expr(is_static, no);
            }
            Expr::Call { pos, callee, args } => {
                self.expr(true, callee);
                let kind = self.callee(*pos, callee, args.len());
                for (k, arg) in args.iter().enumerate() {
                    let arg_static = match &kind {
                        Callee::Fn(flags) => flags.get(k).copied().unwrap_or(false),
                        Callee::Prelude(Prelude::Resize | Prelude::Reinterpret) => k == 0,
                        Callee::Prelude(_) | Callee::Constructor => true,
                        Callee::Unknown => false,
                    };
                    self.expr(is_static || arg_static, arg);
                }
            }
            Expr::Index { pos, base, args } => {
                self.index(is_static, *pos, base, args);
            }
            Expr::Field { base, .. } => self.expr(is_static, base),
        }
    }

    /// An index. It visits the base once and returns the type head of the whole index, which
    /// is a complete type if the base chain starts at a type name.
    fn index(&mut self, is_static: bool, pos: Pos, base: &Expr, args: &[Expr]) -> bool {
        // The outer check ranks before the checks inside the base at one position.
        let seq = self.tick();
        let head = match base {
            // The base type name has its arguments, so it skips the check of a bare name.
            Expr::Name { pos, name } if self.prelude_type(*pos).is_some() => self
                .prelude_type(*pos)
                .map(|p| (format!("`{name}`"), type_arity(p))),
            Expr::Index { pos, base, args } => self
                .index(is_static, *pos, base, args)
                .then(|| ("a complete type".to_owned(), 0)),
            _ => {
                self.expr(is_static, base);
                None
            }
        };
        let is_type = head.is_some();
        if let Some((name, missing)) = head {
            self.arity_at(seq, pos, &name, missing, args.len());
        }
        for arg in args {
            self.expr(true, arg);
        }
        is_type
    }

    fn type_expr(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Name { pos, name } => {
                if let Some(p) = self.prelude_type(*pos) {
                    self.arity(*pos, &format!("`{name}`"), type_arity(p), 0);
                }
            }
            TypeExpr::Index { pos, base, args } => {
                let (what, missing) = match &**base {
                    TypeExpr::Name { pos, name } => (
                        format!("`{name}`"),
                        self.prelude_type(*pos).map_or(0, type_arity),
                    ),
                    TypeExpr::Index { .. } => ("a complete type".to_owned(), 0),
                };
                self.arity(*pos, &what, missing, args.len());
                if matches!(&**base, TypeExpr::Index { .. }) {
                    self.type_expr(base);
                }
                for arg in args {
                    self.expr(true, arg);
                }
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
                if let Some(Target::Decl(id)) = self.target(module.pos)
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
        }
    }
}
