// SPDX-License-Identifier: Apache-2.0
//! The pre-order walk over the sites of a mutation kind.

use super::super::program::sexpr as sexpr_text;
use super::super::program::{
    FieldTy, HBin, HExpr, Item, Place, Radix, SBin, SExpr, STy, Stmt, Ty, Un,
};
use super::uses::{self, Callees};
use super::{EFFECT_FN, Effect, Hit, KEEP_FN, Kind};
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
    /// The function values whose first formal is a `mut` list.
    list_values: Vec<String>,
    /// The helpers with a `mut` first formal.
    mut_helpers: Vec<String>,
    /// The static `let mut` roots in scope, with their types.
    scope: Vec<(String, STy)>,
    /// The ports and registers of the current module.
    hardware: Vec<String>,
    /// Whether the site is in an arm of an `if`.
    arm: bool,
    /// Whether the site runs when the top frame of a module runs, with both
    /// arms of a hardware `if` counted as run. `always` is stricter.
    reach: bool,
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
            list_values: Vec::new(),
            mut_helpers: Vec::new(),
            scope: Vec::new(),
            hardware: Vec::new(),
            arm: false,
            reach: false,
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
        self.list_values = list_values(items);
        self.mut_helpers = mut_helpers(items);
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
        self.reach = false;
        self.arm = false;
        self.scope.clear();
        self.hardware.clear();
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
        let outer = (self.always, self.reach);
        (self.always, self.reach) = (top, top);
        self.stmts_in(body, top);
        (self.always, self.reach) = outer;
    }

    fn stmts_in(&mut self, body: &mut Vec<Stmt>, top: bool) {
        let mark = self.scope.len();
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
            if let Some(root) = mut_root(s)
                && self.site(Kind::Immutable)
            {
                let callees = Callees {
                    mut_helpers: &self.mut_helpers,
                    values: &self.values,
                };
                let code = uses::of(root, body.get(i + 1..).unwrap_or_default(), &callees).code();
                let what = format!("make {root} immutable in {}", self.item);
                if let Some(s) = body.get_mut(i) {
                    freeze(s);
                }
                self.hit(what, Effect::Code(code));
                return;
            }
            if let Some(s) = body.get_mut(i) {
                self.stmt_parts(s);
                if let Stmt::MutLet(n, t, _) = s {
                    self.scope.push((n.clone(), t.clone()));
                }
            }
            if self.hit.is_some() {
                return;
            }
            i += 1;
        }
        self.scope.truncate(mark);
    }

    fn stmt_parts(&mut self, s: &mut Stmt) {
        self.note_hardware(s);
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
            Stmt::MutCall {
                root,
                f,
                args,
                receiver,
                ..
            } => {
                self.rename(root);
                self.rename(f);
                self.args(f, args, zero());
                for a in args.iter_mut() {
                    self.sexpr(a);
                }
                self.window(root, f, args, *receiver);
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

    /// Records the ports and registers of a module.
    fn note_hardware(&mut self, s: &Stmt) {
        if let Stmt::Input(n, _) | Stmt::Reg(n, ..) = s {
            self.hardware.push(n.clone());
        }
    }

    /// Whether the condition `c` is certainly not static by value: a port
    /// or a register, or its negation. The front ends fold an operator on
    /// constants, and a call can drop its operand, so any other condition
    /// may fold to a static `Bool` that takes one arm.
    fn is_hardware(&self, c: &HExpr) -> bool {
        match c {
            HExpr::Name(n) => self.hardware.contains(n),
            HExpr::Unary(Un::Not, a) => self.is_hardware(a),
            _ => false,
        }
    }

    /// The newest static `let mut` `Int` in scope.
    fn counter(&self) -> Option<String> {
        let (name, _) = self.scope.iter().rev().find(|(_, t)| *t == STy::Int)?;
        Some(name.clone())
    }

    /// The sites of `ArmEffect` and `ArmMutation`: a static `Int` operand
    /// in an arm.
    fn arm_operand(&mut self, e: &mut SExpr) {
        if !self.arm {
            return;
        }
        let code = self.reach.then_some("S016");
        let (what, new) = if self.site(Kind::ArmEffect) {
            let new = SExpr::Call(EFFECT_FN.to_owned(), vec![e.clone()]);
            (format!("call {EFFECT_FN} on {}", sexpr_text(e)), new)
        } else if let Some(root) = self.counter()
            && self.site(Kind::ArmMutation)
        {
            let what = format!("call {KEEP_FN} on {root} and {}", sexpr_text(e));
            (what, keep(&root, e.clone()))
        } else {
            return;
        };
        *e = new;
        self.hit(
            format!("{what} in an arm of {}", self.item),
            Effect::Code(code),
        );
    }

    /// Walks a part that may not run: no site in it always runs.
    fn lazily(&mut self, walk: impl FnOnce(&mut Self)) {
        let outer = (self.always, self.reach);
        (self.always, self.reach) = (false, false);
        walk(self);
        (self.always, self.reach) = outer;
    }

    /// The sites of `Window` and `ValueWindow`: an argument of a call on a
    /// list root becomes `root.pop()`. The mutant is printed and never
    /// walked again, so the pop is a name of the printer.
    fn window(&mut self, root: &str, f: &str, args: &mut [SExpr], receiver: bool) {
        let is_list = |scope: &[(String, STy)]| {
            scope
                .iter()
                .rev()
                .find(|(n, _)| n == root)
                .is_some_and(|(_, t)| matches!(t, STy::List(_)))
        };
        let through_value = self.list_values.iter().any(|v| v == f);
        let (kind, code) = match (receiver, through_value) {
            (true, false) => (Kind::Window, Some("S008")),
            (false, true) => (Kind::ValueWindow, self.always.then_some("S008")),
            _ => return,
        };
        if !is_list(&self.scope) {
            return;
        }
        for (i, arg) in args.iter_mut().enumerate() {
            if self.site(kind) {
                // The mutant is printed and never walked again, so this name is never resolved.
                *arg = SExpr::Name(format!("{root}.pop()"));
                let what = format!("pop {root} in argument {} of {f} in {}", i + 1, self.item);
                self.hit(what, Effect::Code(code));
                return;
            }
        }
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
        } else if self.site(Kind::TypeEffect) {
            let code = self.reach.then_some("S016");
            let new = SExpr::Call(EFFECT_FN.to_owned(), vec![w.clone()]);
            let what = format!(
                "call {EFFECT_FN} in the width {} in {}",
                sexpr_text(w),
                self.item
            );
            *w = new;
            self.hit(what, Effect::Code(code));
            return;
        } else if let Some(root) = self.counter()
            && self.site(Kind::TypeMutation)
        {
            let code = self.reach.then_some("S016");
            let new = keep(&root, w.clone());
            let what = format!(
                "call {KEEP_FN} on {root} in the width {} in {}",
                sexpr_text(w),
                self.item
            );
            *w = new;
            self.hit(what, Effect::Code(code));
            return;
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
            HExpr::Static(s) => {
                self.sexpr(s);
                if int_valued(s) {
                    self.arm_operand(s);
                }
            }
            HExpr::Make(t, s) => {
                self.ty(t);
                self.sexpr(s);
                if !matches!(t, Ty::Bool) {
                    self.arm_operand(s);
                }
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
                // A hardware `if` evaluates both arms.
                let both = self.is_hardware(c);
                let (always, reach, arm) = (self.always, self.reach, self.arm);
                (self.always, self.reach, self.arm) = (false, reach && both, true);
                self.hexpr(t);
                self.hexpr(f);
                (self.always, self.reach, self.arm) = (always, reach, arm);
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

/// `p0(root, e)`: a call that takes `root` as its `mut` actual.
fn keep(root: &str, e: SExpr) -> SExpr {
    SExpr::Call(KEEP_FN.to_owned(), vec![SExpr::Name(root.to_owned()), e])
}

/// Whether `e` has the type `Int` by its syntax: a literal, or an
/// arithmetic operator.
fn int_valued(e: &SExpr) -> bool {
    match e {
        SExpr::Int(..) | SExpr::Unary(Un::Neg | Un::Inv, _) => true,
        SExpr::Binary(op, ..) => !matches!(
            op,
            SBin::Eq
                | SBin::Ne
                | SBin::Lt
                | SBin::Le
                | SBin::Gt
                | SBin::Ge
                | SBin::Land
                | SBin::Lor
        ),
        _ => false,
    }
}

/// The consts of a function type whose first formal is a `mut` list.
fn list_values(items: &[Item]) -> Vec<String> {
    items
        .iter()
        .filter_map(|item| match item {
            Item::Const {
                name,
                ty: STy::Fn(f),
                ..
            } if matches!(f.params.first(), Some((true, STy::List(_)))) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// The helpers with a `mut` first formal.
fn mut_helpers(items: &[Item]) -> Vec<String> {
    items
        .iter()
        .filter_map(|item| match item {
            Item::Helper {
                name,
                mut_first: true,
                ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// The name of a `let mut` root: static or hardware.
fn mut_root(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::MutLet(n, ..)
        | Stmt::Let {
            name: n,
            mutable: true,
            ..
        } => Some(n),
        _ => None,
    }
}

/// Makes a `let mut` a `let`.
fn freeze(s: &mut Stmt) {
    match s {
        Stmt::MutLet(n, t, v) => {
            *s = Stmt::StaticLet(mem::take(n), t.clone(), v.clone());
        }
        Stmt::Let { mutable, .. } => *mutable = false,
        _ => {}
    }
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
