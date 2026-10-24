// SPDX-License-Identifier: Apache-2.0
//! The pass before the evaluation. It finds the heights that size the stack of the evaluator,
//! the value of each number literal, and the symbols of the source names.
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
use parse::ast::{Expr, FnParam, Ident, Item, NodeId, Pattern, PortForm, Stmt, TypeExpr};
use resolve::{DeclId, Kind, Resolved, ResolvedExpr, Target};
use std::collections::{BTreeMap, BTreeSet};

/// The value of each number literal, by its parse and its node id. The key is `true` for a
/// literal of the top expression, which is a different parse with its own ids.
pub(crate) type Numbers = BTreeMap<(bool, NodeId), Int>;

/// The argument lists of index expressions that hold a call, a receiver call, or a type
/// expression, by the address of the list. The AST does not move while the evaluator runs, and
/// an index node has no id of its own. An evaluation looks up the property and scans no
/// expression.
#[derive(Default)]
pub(crate) struct CallArgs(BTreeSet<usize>);

impl CallArgs {
    fn key(args: &[Expr]) -> usize {
        args.as_ptr() as usize
    }

    /// Whether the arguments `args` of an index hold a call. Such an index can change a local
    /// of its frame while it evaluates, because only a call passes a local as a `mut` actual or
    /// runs a statement.
    pub(crate) fn has_call(&self, args: &[Expr]) -> bool {
        !args.is_empty() && self.0.contains(&Self::key(args))
    }
}

/// The symbols of a file. Each distinct source name gets one number, so a lookup or a key
/// compares numbers and not text.
#[derive(Default)]
pub(crate) struct Syms {
    /// The text of each symbol.
    pub texts: Vec<String>,
    /// The symbol of each text. The scan fills it, and a name that the run computes extends it
    /// (`symbol_of`), so each text has one symbol.
    table: BTreeMap<String, Sym>,
    /// The symbol of each declaration of a binder of the AST.
    pub decls: BTreeMap<DeclId, Sym>,
    /// The symbol of each field name, by its node id.
    pub fields: BTreeMap<NodeId, Sym>,
    /// The symbol of the name of each item.
    pub items: Vec<Sym>,
    /// The number of each field of each struct item by the symbol of its name, in the order of
    /// the items. An item that is not a struct has none.
    pub struct_fields: Vec<BTreeMap<Sym, usize>>,
    /// The symbol of each field of each struct item, in the order of its declaration. An item
    /// that is not a struct has none. The name of a field in a leaf name comes from it.
    pub field_order: Vec<Vec<Sym>>,
    /// The port families of each module item by the symbol of their name, in the order of the
    /// items: `true` for an input. The resolver finds them in the whole body, also in the arm of a
    /// `comptime if` that does not run. An item that is not a module has none.
    pub families: Vec<BTreeMap<Sym, bool>>,
    /// The symbol of `clock`, the default domain.
    pub clock: Sym,
    /// The symbols of `tag` and `payload`, the names of the parts of an enum.
    pub tag: Sym,
    pub payload: Sym,
}

impl Syms {
    /// The symbol of the text `x`. A text that has none takes the next free symbol, and its text
    /// goes into the table once. The caller of a computed name charges the size of `x` first.
    pub(crate) fn symbol_of(&mut self, x: &str) -> Sym {
        if let Some(&s) = self.table.get(x) {
            return s;
        }
        let s = self.texts.len();
        self.texts.push(x.to_owned());
        self.table.insert(x.to_owned(), s);
        s
    }

    /// The symbol of the text `x`, if a name of the file or of a computed key has it.
    pub(crate) fn find(&self, x: &str) -> Option<Sym> {
        self.table.get(x).copied()
    }
}

/// The result of the pass before the evaluation of `top` in the file scope of `file`.
pub(crate) struct Scan {
    pub stack: NestedStack,
    pub numbers: Numbers,
    pub call_args: CallArgs,
    pub syms: Syms,
    /// The expression nodes that the pass visited, for the tests of the work.
    #[cfg(test)]
    pub nodes: u64,
}

pub(crate) fn of(file: &Resolved, top: Option<&ResolvedExpr>) -> Scan {
    let mut walk = Walk {
        file,
        top,
        height: 0,
        nested: 0,
        numbers: Numbers::new(),
        call_args: CallArgs::default(),
        #[cfg(test)]
        nodes: 0,
        syms: Syms::default(),
        families: BTreeMap::new(),
    };
    if let Some(top) = top {
        walk.expr(top.expr(), 1);
    }
    walk.top = None;
    for item in file.ast() {
        let s = walk.intern(&item.name().name);
        walk.syms.items.push(s);
    }
    walk.syms.clock = walk.intern("clock");
    walk.syms.tag = walk.intern("tag");
    walk.syms.payload = walk.intern("payload");
    for item in file.ast() {
        walk.item(item);
    }
    Scan {
        stack: NestedStack::new(walk.height, walk.nested),
        numbers: walk.numbers,
        call_args: walk.call_args,
        syms: walk.syms,
        #[cfg(test)]
        nodes: walk.nodes,
    }
}

struct Walk<'a> {
    file: &'a Resolved,
    /// The top expression while the walk is in it: it has its own map of targets.
    top: Option<&'a ResolvedExpr>,
    height: usize,
    nested: usize,
    numbers: Numbers,
    call_args: CallArgs,
    #[cfg(test)]
    nodes: u64,
    syms: Syms,
    /// The port families of the module item that the walk is in.
    families: BTreeMap<Sym, bool>,
}

impl Walk<'_> {
    /// Whether the use of the name `id` can start a nested evaluation: a constant, a `type`
    /// item, a struct item, or a function item, whose signature evaluates as a value. A `type`
    /// statement is a local, which starts none.
    fn starts_nesting(&self, id: NodeId) -> bool {
        let target = match self.top {
            Some(top) => top.target(id),
            None => self.file.target(id),
        };
        let Some(Target::Decl(decl)) = target else {
            return false;
        };
        let d = match self.top {
            Some(top) => top.decl(self.file, decl),
            None => self.file.decl(decl),
        };
        match d.kind {
            Kind::Const | Kind::Struct | Kind::Enum | Kind::Fn => true,
            Kind::Alias => self.file.item(&d.name) == Some(decl),
            _ => false,
        }
    }

    fn reach(&mut self, depth: usize) {
        self.height = self.height.max(depth);
    }

    fn intern(&mut self, x: &str) -> Sym {
        self.syms.symbol_of(x)
    }

    fn binder(&mut self, b: &Ident) {
        let s = self.intern(&b.name);
        if let Some(Target::Decl(id)) = self.file.target(b.id) {
            self.syms.decls.insert(id, s);
        }
    }

    /// Notes the port family of an indexed declaration. Its name node targets the family, whose
    /// kind tells the direction of its first entry.
    fn family(&mut self, name: &Ident) {
        let Some(Target::Decl(id)) = self.file.target(name.id) else {
            return;
        };
        if let Kind::Family { input } = self.file.decl(id).kind
            && let Some(&s) = self.syms.decls.get(&id)
        {
            self.families.insert(s, input);
        }
    }

    fn item(&mut self, item: &Item) {
        let mut struct_fields = BTreeMap::new();
        let mut field_order = Vec::new();
        self.families = BTreeMap::new();
        match item {
            Item::Const { ty, value, .. } => {
                self.ty(ty, 1);
                self.expr(value, 1);
            }
            Item::Fn {
                params, ret, body, ..
            } => {
                self.stmts(body, 1);
                for p in params {
                    self.binder(&p.name);
                    self.ty(&p.ty, 1);
                }
                self.ty(ret, 1);
            }
            Item::Module {
                params,
                domains,
                body,
                ..
            } => {
                self.stmts(body, 1);
                for p in params {
                    self.binder(&p.name);
                    self.ty(&p.ty, 1);
                }
                for d in domains.iter().flatten() {
                    self.binder(d);
                }
            }
            Item::Struct { params, fields, .. } => {
                for p in params {
                    self.binder(&p.name);
                    self.ty(&p.ty, 1);
                }
                let mut numbers = BTreeMap::new();
                for (k, f) in fields.iter().enumerate() {
                    let s = self.intern(&f.name.name);
                    field_order.push(s);
                    numbers.entry(s).or_insert(k);
                    self.ty(&f.ty, 1);
                }
                struct_fields = numbers;
            }
            Item::Alias { ty, .. } => self.ty(ty, 1),
            Item::Enum { tag, variants, .. } => {
                self.ty(tag, 1);
                for v in variants {
                    for ty in &v.payload {
                        self.ty(ty, 1);
                    }
                    self.expr(&v.tag, 1);
                }
            }
        }
        self.syms.struct_fields.push(struct_fields);
        self.syms.field_order.push(field_order);
        self.syms.families.push(std::mem::take(&mut self.families));
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
            Stmt::Mem {
                name, word, depth, ..
            } => {
                self.ty(word, d);
                self.expr(depth, d);
                self.binder(name);
            }
            Stmt::Input { name, form, ty, .. } | Stmt::Output { name, form, ty, .. } => {
                if let PortForm::Indexed(k) = form {
                    self.expr(k, d);
                }
                self.ty(ty, d);
                if let PortForm::Keyed(k) = form {
                    self.expr(k, d);
                }
                self.binder(name);
                self.family(name);
            }
            Stmt::Wire { name, ty, .. } | Stmt::Alias { name, ty, .. } => {
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
            Stmt::Expr { value, .. } => {
                self.expr(value, d);
            }
        }
    }

    fn ty(&mut self, t: &TypeExpr, depth: usize) {
        self.reach(depth);
        match t {
            TypeExpr::Unit { .. } => {}
            TypeExpr::Name { id, .. } => {
                if self.starts_nesting(*id) {
                    self.nested = self.nested.max(depth);
                }
            }
            TypeExpr::Index { base, args, .. } => {
                self.ty(base, depth + 1);
                for a in args {
                    self.expr(a, depth + 1);
                }
            }
            TypeExpr::Tuple { elems, .. } => {
                for e in elems {
                    self.ty(e, depth + 1);
                }
            }
            TypeExpr::Array { elem, len, .. } => {
                self.ty(elem, depth + 1);
                self.expr(len, depth + 1);
            }
            TypeExpr::Fn { params, ret, .. } => self.fn_type(params, ret, depth + 1),
        }
    }

    fn fn_type(&mut self, params: &[FnParam], ret: &TypeExpr, depth: usize) {
        for param in params {
            self.ty(&param.ty, depth);
        }
        self.ty(ret, depth);
    }

    /// The value of the literal of a pattern, and the symbols of its binders.
    fn pattern(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Int { id, value, .. } => {
                let n = Int::from_decimal(value.as_str()).unwrap_or_else(Int::zero);
                self.numbers.insert((self.top.is_some(), *id), n);
            }
            Pattern::Variant { binders, .. } => {
                for b in binders.iter().flatten() {
                    self.binder(b);
                }
            }
            Pattern::Wild { .. } | Pattern::Bool { .. } => {}
        }
    }

    /// Walks the expression, and tells whether it holds a call, a receiver call, or a type
    /// expression.
    fn expr(&mut self, e: &Expr, depth: usize) -> bool {
        self.reach(depth);
        #[cfg(test)]
        {
            self.nodes += 1;
        }
        let d = depth + 1;
        match e {
            Expr::Num { id, value, .. } => {
                let n = Int::from_decimal(value.as_str()).unwrap_or_else(Int::zero);
                self.numbers.insert((self.top.is_some(), *id), n);
                false
            }
            Expr::Bool { .. } | Expr::Str { .. } | Expr::Unit { .. } => false,
            // The first use of the enum runs its checks one level deeper.
            Expr::Path { .. } => {
                self.nested = self.nested.max(depth);
                false
            }
            Expr::Name { id, .. } => {
                if self.starts_nesting(*id) {
                    self.nested = self.nested.max(depth);
                }
                false
            }
            Expr::Unary { arg, .. } => self.expr(arg, d),
            Expr::ArrayType { elem, len, .. } => {
                self.ty(elem, d);
                self.expr(len, d);
                true
            }
            Expr::FnType { params, ret, .. } => {
                self.fn_type(params, ret, d);
                true
            }
            Expr::Binary { lhs, rhs, .. } => {
                let l = self.expr(lhs, d);
                self.expr(rhs, d) || l
            }
            Expr::Cond { cond, yes, no, .. } => {
                let c = self.expr(cond, d);
                let y = self.expr(yes, d);
                self.expr(no, d) || c || y
            }
            Expr::Call { callee, args, .. } => {
                self.nested = self.nested.max(depth);
                self.expr(callee, d);
                for a in args {
                    self.expr(a, d);
                }
                true
            }
            Expr::Method { recv, args, .. } => {
                self.nested = self.nested.max(depth);
                self.expr(recv, d);
                for a in args {
                    self.expr(a, d);
                }
                true
            }
            Expr::Index { base, args, .. } => {
                let mut calls = self.expr(base, d);
                let mut in_args = false;
                for a in args {
                    in_args |= self.expr(a, d);
                }
                if in_args && !args.is_empty() {
                    self.call_args.0.insert(CallArgs::key(args));
                }
                calls |= in_args;
                calls
            }
            Expr::Field { base, field, .. } => {
                if self.top.is_none() {
                    let s = self.intern(&field.name);
                    self.syms.fields.insert(field.id, s);
                }
                self.expr(base, d)
            }
            Expr::Select { base, .. } => self.expr(base, d),
            Expr::Match { scrut, arms, .. } => {
                let mut calls = self.expr(scrut, d);
                for arm in arms {
                    self.pattern(&arm.pat);
                    calls |= self.expr(&arm.value, d);
                }
                calls
            }
            Expr::Tuple { elems, .. } | Expr::Array { elems, .. } => {
                let mut calls = false;
                for e in elems {
                    calls |= self.expr(e, d);
                }
                calls
            }
        }
    }
}
