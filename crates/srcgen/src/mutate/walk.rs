// SPDX-License-Identifier: Apache-2.0
//! The pre-order walk over the sites of a mutation kind.

use super::super::program::sexpr as sexpr_text;
use super::super::program::{FieldTy, HBin, HExpr, Item, Place, Radix, SBin, SExpr, STy, Stmt, Ty};
use super::{Effect, Hit, Kind};
use num_bigint::BigInt;
use std::mem;

/// A pre-order walk over the sites of one kind: items in order, then
/// statements in order, then expressions left to right. Without a target
/// it only counts the sites (and, for `Rename`, collects the names); with
/// one it mutates that site.
pub(super) struct Walk<'a> {
    kind: Kind,
    top: &'a str,
    target: Option<usize>,
    pub(super) seen: usize,
    pub(super) hit: Option<Hit>,
    pub(super) names: Vec<String>,
    /// The names that hold a function value: a call through one checks its
    /// arguments at run time (pass 5), so an arity change in dead code stays
    /// unseen.
    values: Vec<String>,
    /// Whether the site being walked always runs: it is in the top frame of
    /// a module, and in no lazy operand or branch.
    always: bool,
    /// The name and index of the current item, and the count of its
    /// statements so far.
    item: String,
    index: usize,
    stmt: usize,
}

impl<'a> Walk<'a> {
    pub(super) fn new(kind: Kind, top: &'a str, target: Option<usize>) -> Walk<'a> {
        Walk {
            kind,
            top,
            target,
            seen: 0,
            hit: None,
            names: Vec::new(),
            values: Vec::new(),
            always: false,
            item: String::new(),
            index: 0,
            stmt: 0,
        }
    }

    /// Counts a site of `kind`; true if it is the target.
    fn site(&mut self, kind: Kind) -> bool {
        if kind != self.kind || self.hit.is_some() {
            return false;
        }
        self.seen += 1;
        self.target == Some(self.seen - 1)
    }

    fn hit(&mut self, what: String, effect: Effect) {
        self.hit = Some(Hit { what, effect });
    }

    pub(super) fn items(&mut self, items: &mut Vec<Item>) {
        self.values = function_values(items);
        let mut i = 0;
        while let Some(item) = items.get(i) {
            let name = item_name(item).to_owned();
            if name != self.top && self.site(Kind::Delete) {
                items.remove(i);
                self.hit(format!("delete item {name}"), Effect::Gone(name, None));
                return;
            }
            if self.site(Kind::Duplicate) {
                items.insert(i + 1, item.clone());
                self.hit(format!("duplicate item {name}"), Effect::Code(Some("S002")));
                return;
            }
            self.item = name;
            self.index = i;
            self.stmt = 0;
            if let Some(item) = items.get_mut(i) {
                self.item_body(item);
            }
            if self.hit.is_some() {
                return;
            }
            i += 1;
        }
    }

    fn item_body(&mut self, item: &mut Item) {
        self.always = false;
        match item {
            Item::Const { value, .. } => self.sexpr(value),
            Item::HwFnValue { .. } => {}
            Item::ListFn(f) => self.sexpr(&mut f.element),
            Item::MutFn(f) => {
                self.sexpr(&mut f.update);
                self.sexpr(&mut f.ret);
                if let Some((_, value)) = &mut f.diag {
                    self.sexpr(value);
                }
            }
            Item::Struct(def) => {
                for (_, t) in &mut def.fields {
                    if let FieldTy::UInt(w) | FieldTy::SInt(w) = t {
                        self.width(w);
                    }
                }
            }
            Item::ComptimeFn(f) => {
                self.sexpr(&mut f.base);
                self.sexpr(&mut f.step);
            }
            Item::Helper {
                params,
                ret,
                body,
                result,
                ..
            } => {
                for (_, t) in params {
                    self.ty(t);
                }
                self.ty(ret);
                self.stmts(body, false);
                self.hexpr(result);
            }
            Item::Module { body, .. } => self.stmts(body, true),
        }
    }

    /// The statements of a body; `top` if it is the top frame of a module.
    fn stmts(&mut self, body: &mut Vec<Stmt>, top: bool) {
        let outer = self.always;
        self.always = top;
        self.stmts_in(body, top);
        self.always = outer;
    }

    fn stmts_in(&mut self, body: &mut Vec<Stmt>, top: bool) {
        let mut i = 0;
        while let Some(s) = body.get(i) {
            self.stmt += 1;
            let n = self.stmt;
            if self.site(Kind::Delete) {
                let effect = match (declared(s), s) {
                    (Some(name), _) => Effect::Gone(name.to_owned(), Some(self.index)),
                    (None, Stmt::Connect(..)) if top => Effect::Code(Some("S018")),
                    _ => Effect::Code(None),
                };
                body.remove(i);
                self.hit(format!("delete statement {n} of {}", self.item), effect);
                return;
            }
            if declared(s).is_some() && self.site(Kind::Duplicate) {
                body.insert(i + 1, s.clone());
                let what = format!("duplicate statement {n} of {}", self.item);
                self.hit(what, Effect::Code(Some("S002")));
                return;
            }
            if let Some(s) = body.get_mut(i) {
                self.stmt_parts(s);
            }
            if self.hit.is_some() {
                return;
            }
            i += 1;
        }
    }

    fn stmt_parts(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Input(_, t) | Stmt::Output(_, t) | Stmt::Wire(_, t) => self.ty(t),
            Stmt::Reg(_, t, reset) => {
                self.ty(t);
                self.sexpr(reset);
            }
            Stmt::Let { ty, value, .. } => {
                if let Some(t) = ty {
                    self.ty(t);
                }
                self.hexpr(value);
            }
            Stmt::StaticLet(_, _, v)
            | Stmt::MutLet(_, _, v)
            | Stmt::Assert(v, _)
            | Stmt::Diagnostic(_, v) => self.sexpr(v),
            Stmt::Push(list, v) => {
                self.rename(list);
                self.sexpr(v);
            }
            Stmt::PopLet(_, list) => self.rename(list),
            Stmt::MutCall { root, f, args, .. } => {
                self.rename(root);
                self.rename(f);
                self.args(f, args, zero());
                for a in args {
                    self.sexpr(a);
                }
            }
            Stmt::Assign(n, v) => {
                self.rename(n);
                self.hexpr(v);
            }
            Stmt::Connect(place, v) => {
                match place {
                    Place::Name(n) | Place::Field(n, _) => self.rename(n),
                }
                self.hexpr(v);
            }
            Stmt::Instance(_, m, args) => {
                self.rename(m);
                self.args(m, args, zero());
                for a in args {
                    self.sexpr(a);
                }
            }
            Stmt::If(c, then, els) => {
                self.sexpr(c);
                self.stmts(then, false);
                if let Some(els) = els {
                    self.stmts(els, false);
                }
            }
            Stmt::For(_, lo, hi, body) => {
                self.sexpr(lo);
                self.sexpr(hi);
                self.stmts(body, false);
            }
            Stmt::Error(_) => {}
            Stmt::Block(body) => self.stmts(body, false),
        }
    }

    /// Walks a part that may not run: no site in it always runs.
    fn lazily(&mut self, walk: impl FnOnce(&mut Self)) {
        let outer = mem::replace(&mut self.always, false);
        walk(self);
        self.always = outer;
    }

    fn rename(&mut self, name: &mut String) {
        if self.kind == Kind::Rename && self.target.is_none() {
            self.names.push(name.clone());
        }
        if self.site(Kind::Rename) {
            let old = mem::replace(name, "q0".to_owned());
            let what = format!("rename {old} to q0 in {}", self.item);
            self.hit(what, Effect::Code(Some("S003")));
        }
    }

    /// The arity sites of a call or an instance of `callee`.
    fn args<T>(&mut self, callee: &str, args: &mut Vec<T>, zero: T) {
        let through_value = self.values.iter().any(|v| v == callee);
        let code = if through_value && !self.always {
            None
        } else {
            Some("S007")
        };
        if !args.is_empty() && self.site(Kind::DropArg) {
            let what = format!("drop argument {} of {callee} in {}", args.len(), self.item);
            args.pop();
            self.hit(what, Effect::Code(code));
        }
        if self.site(Kind::AddArg) {
            args.push(zero);
            let what = format!("add argument {} to {callee} in {}", args.len(), self.item);
            self.hit(what, Effect::Code(code));
        }
    }

    fn ty(&mut self, t: &mut Ty) {
        if let Ty::UInt(w) | Ty::SInt(w) = t {
            self.width(w);
        }
    }

    /// The width of a type or of a struct field.
    fn width(&mut self, w: &mut SExpr) {
        let new = if self.site(Kind::Widen) {
            let one = SExpr::Int(BigInt::from(1), Radix::Dec);
            SExpr::Binary(SBin::Add, Box::new(w.clone()), Box::new(one))
        } else if *w != zero() && self.site(Kind::ZeroWidth) {
            zero()
        } else {
            self.sexpr(w);
            return;
        };
        let what = format!(
            "change width {} to {} in {}",
            sexpr_text(w),
            sexpr_text(&new),
            self.item
        );
        *w = new;
        self.hit(what, Effect::Code(None));
    }

    fn sexpr(&mut self, e: &mut SExpr) {
        if *e != fault() && self.site(Kind::Fault) {
            let what = format!("change {} to (1 / 0) in {}", sexpr_text(e), self.item);
            *e = fault();
            self.hit(what, Effect::Code(None));
            return;
        }
        match e {
            SExpr::Int(..) | SExpr::Bool(_) | SExpr::Str(_) | SExpr::NewList(_) => {}
            SExpr::Name(n) => self.rename(n),
            SExpr::Call(f, args) => {
                self.rename(f);
                self.args(f, args, zero());
                for a in args {
                    self.sexpr(a);
                }
            }
            SExpr::Tuple(xs) | SExpr::Array(xs) => {
                for x in xs {
                    self.sexpr(x);
                }
            }
            SExpr::Record(name, targs, fields) => {
                self.rename(name);
                for x in targs.iter_mut().chain(fields) {
                    self.sexpr(x);
                }
            }
            SExpr::Zero(name, targs) | SExpr::DataBits(name, targs) => {
                self.rename(name);
                for x in targs {
                    self.sexpr(x);
                }
            }
            SExpr::Select(a, ..)
            | SExpr::Field(a, _)
            | SExpr::Len(a)
            | SExpr::StrOf(a)
            | SExpr::Unary(_, a) => {
                self.sexpr(a);
            }
            SExpr::Binary(SBin::Land | SBin::Lor, a, b) => {
                self.sexpr(a);
                self.lazily(|w| w.sexpr(b));
            }
            SExpr::Index(a, b) | SExpr::Binary(_, a, b) => {
                self.sexpr(a);
                self.sexpr(b);
            }
            SExpr::If(c, t, f) => {
                self.sexpr(c);
                self.lazily(|w| {
                    w.sexpr(t);
                    w.sexpr(f);
                });
            }
        }
    }

    fn hexpr(&mut self, e: &mut HExpr) {
        match e {
            HExpr::Name(n) | HExpr::Field(n, _) => self.rename(n),
            HExpr::Static(s) => self.sexpr(s),
            HExpr::Make(t, s) => {
                self.ty(t);
                self.sexpr(s);
            }
            HExpr::Unary(_, a) => self.hexpr(a),
            HExpr::Binary(HBin::Land | HBin::Lor, a, b) => {
                self.hexpr(a);
                self.lazily(|w| w.hexpr(b));
            }
            HExpr::Binary(_, a, b) => {
                self.hexpr(a);
                self.hexpr(b);
            }
            HExpr::If(c, t, f) => {
                self.hexpr(c);
                self.lazily(|w| {
                    w.hexpr(t);
                    w.hexpr(f);
                });
            }
            HExpr::Resize(t, a) | HExpr::Reinterpret(t, a) => {
                self.ty(t);
                self.hexpr(a);
            }
            HExpr::Call(f, args) => {
                self.rename(f);
                self.args(f, args, HExpr::Static(zero()));
                for a in args {
                    self.hexpr(a);
                }
            }
            HExpr::Receiver(recv, f, args) => {
                self.hexpr(recv);
                self.rename(f);
                self.args(f, args, HExpr::Static(zero()));
                for a in args {
                    self.hexpr(a);
                }
            }
        }
    }
}

/// The names of the consts and parameters of a function type, and of the
/// function values of helpers.
fn function_values(items: &[Item]) -> Vec<String> {
    let mut names = Vec::new();
    for item in items {
        match item {
            Item::Const {
                name,
                ty: STy::Fn(_),
                ..
            }
            | Item::HwFnValue { name, .. } => names.push(name.clone()),
            Item::Module { params, .. } => {
                let functions = params.iter().filter(|(_, t)| matches!(t, STy::Fn(_)));
                names.extend(functions.map(|(n, _)| n.clone()));
            }
            _ => {}
        }
    }
    names
}

fn item_name(item: &Item) -> &str {
    match item {
        Item::Const { name, .. }
        | Item::Helper { name, .. }
        | Item::HwFnValue { name, .. }
        | Item::Module { name, .. } => name,
        Item::ComptimeFn(f) => &f.name,
        Item::Struct(def) => &def.name,
        Item::ListFn(f) => &f.name,
        Item::MutFn(f) => &f.name,
    }
}

/// The name that a declaration statement declares.
fn declared(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::Input(n, _)
        | Stmt::Output(n, _)
        | Stmt::Reg(n, _, _)
        | Stmt::Wire(n, _)
        | Stmt::Let { name: n, .. }
        | Stmt::StaticLet(n, _, _)
        | Stmt::MutLet(n, _, _)
        | Stmt::PopLet(n, _)
        | Stmt::MutCall { name: n, .. }
        | Stmt::Instance(n, _, _) => Some(n),
        _ => None,
    }
}

fn zero() -> SExpr {
    SExpr::Int(BigInt::from(0), Radix::Dec)
}

/// `(1 / 0)`.
fn fault() -> SExpr {
    let one = SExpr::Int(BigInt::from(1), Radix::Dec);
    SExpr::Binary(SBin::Div, Box::new(one), Box::new(zero()))
}
