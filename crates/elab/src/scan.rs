// SPDX-License-Identifier: Apache-2.0
//! The pass before the evaluation. It finds the heights that size the stack of the evaluator,
//! the value of each number literal, the symbols of the source names, and the call sites.
//!
//! The evaluator recurses over the AST, and each active call, constant in progress, or
//! instantiation in progress starts the recursion again in its item. The pass finds two
//! heights: the highest node, and the highest node that can start a nested evaluation, a
//! call, the use of a constant, or an `instance` statement. `parse::NestedStack` sizes the
//! stack from them.
//!
//! The decimal conversion of a literal is not a unit of the cost model: Lean parses a literal
//! to its integer. Thus it runs here, once for each literal, and the evaluation only copies a
//! value after it paid for it. The text table of the symbols runs here too, as the Lean
//! `symbols` runs before the fuel counts.

use crate::int::Int;
use crate::names::Sym;
use parse::NestedStack;
use parse::ast::{Expr, Ident, Item, NodeId, Pos, Stmt, TypeExpr};
use resolve::{DeclId, Kind, Resolved, ResolvedExpr, Target};
use std::collections::BTreeMap;

/// The value of each number literal, by its parse and its node id. The key is `true` for a
/// literal of the top expression, which is a different parse with its own ids.
pub(crate) type Numbers = BTreeMap<(bool, NodeId), Int>;

/// The symbols of a file. Each distinct source name gets one number, so a lookup or a key
/// compares numbers and not text.
#[derive(Default)]
pub(crate) struct Syms {
    /// The text of each symbol.
    pub texts: Vec<String>,
    /// The symbol of each declaration of a binder of the AST.
    pub decls: BTreeMap<DeclId, Sym>,
    /// The symbol of each field name, by its node id.
    pub fields: BTreeMap<NodeId, Sym>,
    /// The symbol of the name of each item.
    pub items: Vec<Sym>,
    /// The symbol of `clock`, the default domain.
    pub clock: Sym,
    /// The number of each call node in the body of each item: its index among the call nodes
    /// of the body, in position order, by its node id. Calls at one position share a number,
    /// as in the Lean `callSites`. Section 7.3 names a call frame with it.
    pub calls: Vec<BTreeMap<NodeId, u64>>,
}

/// The result of the pass before the evaluation of `top` in the file scope of `file`.
pub(crate) struct Scan {
    pub stack: NestedStack,
    pub numbers: Numbers,
    pub syms: Syms,
}

pub(crate) fn of(file: &Resolved, top: Option<&ResolvedExpr>) -> Scan {
    let mut walk = Walk {
        file,
        top,
        height: 0,
        nested: 0,
        numbers: Numbers::new(),
        table: BTreeMap::new(),
        syms: Syms::default(),
        calls: Vec::new(),
    };
    if let Some(top) = top {
        walk.expr(top.expr(), 1);
    }
    walk.top = None;
    for item in file.ast() {
        let (Item::Const { name, .. } | Item::Fn { name, .. } | Item::Module { name, .. }) = item;
        let s = walk.intern(&name.name);
        walk.syms.items.push(s);
    }
    walk.syms.clock = walk.intern("clock");
    for item in file.ast() {
        walk.item(item);
    }
    Scan {
        stack: NestedStack::new(walk.height, walk.nested),
        numbers: walk.numbers,
        syms: walk.syms,
    }
}

struct Walk<'a> {
    file: &'a Resolved,
    /// The top expression while the walk is in it: it has its own map of targets.
    top: Option<&'a ResolvedExpr>,
    height: usize,
    nested: usize,
    numbers: Numbers,
    table: BTreeMap<String, Sym>,
    syms: Syms,
    /// The position and the node id of each call node of the body of the current item.
    calls: Vec<(Pos, NodeId)>,
}

impl Walk<'_> {
    fn is_constant(&self, id: NodeId) -> bool {
        let target = match self.top {
            Some(top) => top.target(id),
            None => self.file.target(id),
        };
        matches!(target, Some(Target::Decl(id)) if self.file.decl(id).kind == Kind::Const)
    }

    fn reach(&mut self, depth: usize) {
        self.height = self.height.max(depth);
    }

    fn intern(&mut self, x: &str) -> Sym {
        if let Some(&s) = self.table.get(x) {
            return s;
        }
        let s = self.syms.texts.len();
        self.syms.texts.push(x.to_owned());
        self.table.insert(x.to_owned(), s);
        s
    }

    fn binder(&mut self, b: &Ident) {
        let s = self.intern(&b.name);
        if let Some(Target::Decl(id)) = self.file.target(b.id) {
            self.syms.decls.insert(id, s);
        }
    }

    fn item(&mut self, item: &Item) {
        self.calls.clear();
        match item {
            Item::Const { ty, value, .. } => {
                self.ty(ty, 1);
                self.expr(value, 1);
                self.calls.clear();
            }
            Item::Fn {
                params, ret, body, ..
            } => {
                self.stmts(body, 1);
                let calls = std::mem::take(&mut self.calls);
                for p in params {
                    self.binder(&p.name);
                    self.ty(&p.ty, 1);
                }
                self.ty(ret, 1);
                self.calls = calls;
            }
            Item::Module {
                params,
                domains,
                body,
                ..
            } => {
                self.stmts(body, 1);
                let calls = std::mem::take(&mut self.calls);
                for p in params {
                    self.binder(&p.name);
                    self.ty(&p.ty, 1);
                }
                for d in domains.iter().flatten() {
                    self.binder(d);
                }
                self.calls = calls;
            }
        }
        self.calls.sort_unstable();
        let mut sites = BTreeMap::new();
        let mut k = 0u64;
        let mut last = None;
        for &(p, id) in &self.calls {
            if last.is_some_and(|q| q != p) {
                k += 1;
            }
            last = Some(p);
            sites.insert(id, k);
        }
        self.syms.calls.push(sites);
    }

    fn stmts(&mut self, ss: &[Stmt], depth: usize) {
        for s in ss {
            self.stmt(s, depth);
        }
    }

    fn stmt(&mut self, s: &Stmt, depth: usize) {
        self.reach(depth);
        let d = depth + 1;
        match s {
            Stmt::Local {
                name, ty, value, ..
            } => {
                if let Some(ty) = ty {
                    self.ty(ty, d);
                }
                self.expr(value, d);
                self.binder(name);
            }
            Stmt::Assign { target, value, .. } | Stmt::Connect { target, value, .. } => {
                self.expr(target, d);
                self.expr(value, d);
            }
            Stmt::Reg { name, ty, init, .. } => {
                self.ty(ty, d);
                self.expr(init, d);
                self.binder(name);
            }
            Stmt::Wire { name, ty, .. }
            | Stmt::Input { name, ty, .. }
            | Stmt::Output { name, ty, .. } => {
                self.ty(ty, d);
                self.binder(name);
            }
            Stmt::Inst { name, args, .. } => {
                self.nested = self.nested.max(depth);
                for a in args {
                    self.expr(a, d);
                }
                self.binder(name);
            }
            Stmt::Ret { value, .. } => {
                if let Some(v) = value {
                    self.expr(v, d);
                }
            }
            Stmt::CtIf { cond, yes, no, .. } => {
                self.expr(cond, d);
                self.stmts(yes, d + 1);
                if let Some(no) = no {
                    self.stmts(no, d + 1);
                }
            }
            Stmt::CtFor {
                var, lo, hi, body, ..
            } => {
                self.expr(lo, d);
                self.expr(hi, d);
                self.binder(var);
                self.stmts(body, d + 1);
            }
            Stmt::Block { body, .. } => self.stmts(body, d),
            Stmt::Expr { value, .. } => self.expr(value, d),
        }
    }

    fn ty(&mut self, t: &TypeExpr, depth: usize) {
        self.reach(depth);
        if let TypeExpr::Index { base, args, .. } = t {
            self.ty(base, depth + 1);
            for a in args {
                self.expr(a, depth + 1);
            }
        }
    }

    fn expr(&mut self, e: &Expr, depth: usize) {
        self.reach(depth);
        let d = depth + 1;
        match e {
            Expr::Num { id, value, .. } => {
                let n = Int::from_decimal(value.as_str()).unwrap_or_else(Int::zero);
                self.numbers.insert((self.top.is_some(), *id), n);
            }
            Expr::Bool { .. } | Expr::Str { .. } => {}
            Expr::Name { id, .. } => {
                if self.is_constant(*id) {
                    self.nested = self.nested.max(depth);
                }
            }
            Expr::Unary { arg, .. } => self.expr(arg, d),
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(lhs, d);
                self.expr(rhs, d);
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(cond, d);
                self.expr(yes, d);
                self.expr(no, d);
            }
            Expr::Call {
                pos,
                id,
                callee,
                args,
            } => {
                self.nested = self.nested.max(depth);
                if self.top.is_none() {
                    self.calls.push((*pos, *id));
                }
                self.expr(callee, d);
                for a in args {
                    self.expr(a, d);
                }
            }
            Expr::Index { base, args, .. } => {
                self.expr(base, d);
                for a in args {
                    self.expr(a, d);
                }
            }
            Expr::Field { base, field, .. } => {
                if self.top.is_none() {
                    let s = self.intern(&field.name);
                    self.syms.fields.insert(field.id, s);
                }
                self.expr(base, d);
            }
        }
    }
}
