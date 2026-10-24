// SPDX-License-Identifier: Apache-2.0
//! The pre-order walk over the sites of a mutation kind.

use super::super::program::hexpr as hexpr_text;
use super::super::program::is_resource_helper;
use super::super::program::sexpr as sexpr_text;
use super::super::program::{
    EnumDef, FTy, FieldTy, HBin, HExpr, Item, Match, PTy, Pattern, Place, Port, Radix, SBin, SExpr,
    STy, Scalar, Stmt, Ty, Un, Variant,
};
use super::uses::{self, Callees};
use super::{EFFECT_FN, Effect, Hit, KEEP_FN, Kind, beyond};
use num_bigint::BigInt;
use std::collections::BTreeMap;
use std::mem;

/// The sites of `Kind::Delete` that one binding makes, when the helper that
/// holds it also declares the resource.
const DELETE_BINDING_SITES: usize = 32;

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
    /// The helpers with a `comptime` formal, and which formals they are: an
    /// actual there is a static position, not an operand.
    static_formals: BTreeMap<String, Vec<bool>>,
    /// The helpers with a handle formal: a call of one binds its actuals.
    binders: Vec<String>,
    /// The resources that the helper under the walk declares in its body.
    declared_here: Vec<String>,
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
    /// The names of the enum items.
    enum_names: Vec<String>,
    /// The ports, registers, and wires of the module, with their types.
    typed: Vec<(String, Ty)>,
    /// The enums that the top frame of a module uses, found by a first walk.
    used: Vec<String>,
    /// The families with an indexed declaration in the module body, and how
    /// many indexed declarations each name has in the current item.
    families: Vec<String>,
    indexed: BTreeMap<String, usize>,
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
            static_formals: BTreeMap::new(),
            binders: Vec::new(),
            declared_here: Vec::new(),
            scope: Vec::new(),
            hardware: Vec::new(),
            arm: false,
            reach: false,
            always: false,
            enum_names: Vec::new(),
            typed: Vec::new(),
            used: Vec::new(),
            families: Vec::new(),
            indexed: BTreeMap::new(),
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
        if matches!(
            self.kind,
            Kind::SameTag | Kind::TagFit | Kind::PayloadOverflow
        ) {
            let mut first = Walk::new(Kind::Rename, self.top, None);
            first.items(&mut items.clone());
            self.used = first.used;
        }
        self.enum_names = items
            .iter()
            .filter_map(|i| match i {
                Item::Enum(d) => Some(d.name.clone()),
                _ => None,
            })
            .collect();
        self.values = function_values(items);
        self.list_values = list_values(items);
        self.mut_helpers = mut_helpers(items);
        self.static_formals = static_formals(items);
        self.binders = binders(items);
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
        self.declared_here = match item {
            Item::Helper { body, .. } if is_resource_helper(&self.item) => body
                .iter()
                .filter_map(|s| match s {
                    Stmt::Reg(n, ..)
                    | Stmt::Wire(n, ..)
                    | Stmt::Mem(n, ..)
                    | Stmt::Instance(n, ..) => Some(n.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        self.indexed.clear();
        if let Item::Module { body, .. } | Item::Helper { body, .. } = item {
            count_indexed(body, &mut self.indexed);
        }
        self.families = match item {
            Item::Module { .. } => self.indexed.keys().cloned().collect(),
            _ => Vec::new(),
        };
        self.always = false;
        self.reach = false;
        self.arm = false;
        self.scope.clear();
        self.hardware.clear();
        self.typed.clear();
        match item {
            Item::Const { value, .. } => self.sexpr(value),
            Item::HwFnValue { .. } => {}
            Item::Enum(def) => self.enum_item(def),
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
                    match t {
                        FieldTy::UInt(w) | FieldTy::SInt(w) => self.width(w),
                        FieldTy::Handle(t) => self.fty(t),
                        FieldTy::Static(_) => {}
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
                    self.fty(t);
                }
                self.fty(ret);
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
        // A name that a nested frame declares leaves scope with the frame.
        let (hardware, typed) = (self.hardware.len(), self.typed.len());
        let mut i = 0;
        while let Some(s) = body.get(i) {
            self.stmt += 1;
            let n = self.stmt;
            // The binding of a resource that a helper declares is several
            // sites of `Delete`: the other statements of a program far
            // outnumber those, and a deleted one leaves a resource of the
            // helper unbound at its declaration.
            let copies = if self.binds_declared(s) {
                DELETE_BINDING_SITES
            } else {
                1
            };
            if (0..copies).any(|_| self.site(Kind::Delete)) {
                let effect = match (declared(s), s) {
                    // Another indexed declaration keeps the family.
                    (Some(_), Stmt::Port(p))
                        if p.key.is_some() && self.indexed.get(&p.name).is_some_and(|&n| n > 1) =>
                    {
                        Effect::Code(None)
                    }
                    (Some(name), _) => Effect::Gone(name.to_owned(), Some(self.index)),
                    (None, s) if top && self.is_binding(s) => Effect::Code(Some("S018")),
                    _ => Effect::Code(None),
                };
                body.remove(i);
                self.hit(format!("delete statement {n} of {}", self.item), effect);
                return;
            }
            if top && self.is_binding(s) && self.site(Kind::DuplicateBind) {
                body.insert(i + 1, s.clone());
                let what = format!("copy binding statement {n} of {}", self.item);
                self.hit(what, Effect::Code(Some("S018")));
                return;
            }
            if declared(s).is_some() && self.site(Kind::Duplicate) {
                // Two entries with one key are `S019` when the copy runs.
                // The family is no second declaration of the name.
                let code = match s {
                    Stmt::Port(p) if p.key.is_some() => self.always.then_some("S019"),
                    _ => Some("S002"),
                };
                body.insert(i + 1, s.clone());
                let what = format!("duplicate statement {n} of {}", self.item);
                self.hit(what, Effect::Code(code));
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
        self.hardware.truncate(hardware);
        self.typed.truncate(typed);
    }

    /// Whether `s` binds a resource that the helper under the walk declares
    /// itself: the target of a `:=`, the memory of a `write_port`, or the
    /// first actual of a binding call.
    fn binds_declared(&self, s: &Stmt) -> bool {
        let named = |n: &str| self.declared_here.iter().any(|d| d == n);
        match s {
            Stmt::Connect(Place::Name(n) | Place::Field(n, _), _) => named(n),
            Stmt::WritePort { mem, .. } => named(mem),
            Stmt::Call(f, args) if self.binders.contains(f) => {
                matches!(args.first(), Some(HExpr::Name(n)) if named(n))
            }
            _ => false,
        }
    }

    /// Whether `s` binds a resource of the module: a `:=`, a `write_port`,
    /// or a call of a helper that takes a handle. A call of a helper that
    /// only declares binds nothing from outside, and a copy of it declares
    /// a second set of resources.
    fn is_binding(&self, s: &Stmt) -> bool {
        match s {
            Stmt::Connect(..) | Stmt::WritePort { .. } => true,
            Stmt::Call(f, _) => self.binders.contains(f),
            _ => false,
        }
    }

    fn stmt_parts(&mut self, s: &mut Stmt) {
        self.note_hardware(s);
        if self.scalar_family(s) {
            return;
        }
        match s {
            Stmt::Input(_, t) | Stmt::Output(_, t) | Stmt::Wire(_, t) => self.ty(t),
            Stmt::Port(p) => self.port_parts(p),
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
                self.place_parts(place);
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
            Stmt::Call(f, args) => {
                self.rename(f);
                self.args(f, args, HExpr::Static(zero()));
                for a in args {
                    self.hexpr(a);
                }
            }
            Stmt::HList(_, t) => self.fty(t),
            Stmt::HPush(list, h) => {
                self.rename(list);
                self.hexpr(h);
            }
            Stmt::Mem(_, t, depth) => {
                self.ty(t);
                self.sexpr(depth);
            }
            Stmt::WritePort {
                mem,
                addr,
                data,
                en,
                ..
            } => {
                self.rename(mem);
                self.hexpr(addr);
                self.hexpr(data);
                self.hexpr(en);
            }
        }
    }

    /// The parts of a port declaration: its type and its keys.
    fn port_parts(&mut self, p: &mut Port) {
        if let PTy::Data(t) = &mut p.ty {
            self.ty(t);
        }
        if let Some(k) = &mut p.key
            && self.family_key(k)
        {
            return;
        }
        if let Some(public) = &mut p.public {
            if self.public_sites(public) {
                return;
            }
            self.sexpr(public);
        } else if let Some(k) = &mut p.key {
            self.sexpr(k);
        }
    }

    /// The sites of `KeyRange` and `KeyType` on the key `k` of a family,
    /// in a declaration or a selection. The first error is the key when the
    /// site always runs.
    fn family_key(&mut self, k: &mut SExpr) -> bool {
        let big = SExpr::Int(BigInt::from(1u64 << 32), Radix::Dec);
        if self.site(Kind::KeyRange) {
            *k = big;
            self.hit(
                format!("make a family key 2^32 in {}", self.item),
                Effect::Code(self.always.then_some("S012")),
            );
            return true;
        }
        if self.site(Kind::KeyType) {
            // A `Bool` and a static finite integer are no `Nat`.
            let finite = SExpr::Convert(STy::UInt(4), Box::new(zero()));
            *k = if self.seen.is_multiple_of(2) {
                SExpr::Bool(true)
            } else {
                finite
            };
            self.hit(
                format!("make a family key a value of another type in {}", self.item),
                Effect::Code(self.always.then_some("S010")),
            );
            return true;
        }
        false
    }

    /// The sites of `KeyType` and `BadName` on the `as` key of a port.
    fn public_sites(&mut self, public: &mut SExpr) -> bool {
        let always = self.always;
        let code = |code| always.then_some(code);
        if self.site(Kind::KeyType) {
            *public = SExpr::Int(BigInt::from(3), Radix::Dec);
            let code = code("S010");
            self.hit(
                format!("make an `as` key an integer in {}", self.item),
                Effect::Code(code),
            );
            return true;
        }
        match public {
            SExpr::Str(_) if self.site(Kind::BadName) => {
                const BAD: [&str; 3] = ["1c", "", "reg"];
                *public = SExpr::Str(BAD[self.seen % BAD.len()].to_owned());
                let code = code("S022");
                self.hit(
                    format!("break the name rule with an `as` key in {}", self.item),
                    Effect::Code(code),
                );
                true
            }
            SExpr::PortKey(_, false, index) if self.site(Kind::BadName) => {
                **index = SExpr::Int(BigInt::from(1), Radix::Dec);
                let code = code("S022");
                self.hit(
                    format!("give a scalar PortKey the index 1 in {}", self.item),
                    Effect::Code(code),
                );
                true
            }
            _ => false,
        }
    }

    /// `ScalarFamily`: a scalar port of the top frame of a module gets the
    /// `as` key of a family that the module body declares. The table of
    /// public names holds the family from the start (spec 5.6), so the port
    /// is `S019` also if no entry came before it. The binder stays, so
    /// pass 2 sees no collision (a plain rename is `S002`).
    fn scalar_family(&mut self, s: &mut Stmt) -> bool {
        if self.families.is_empty() {
            return false;
        }
        let scalar = match s {
            Stmt::Input(n, t) => Some((false, n.clone(), PTy::Data(t.clone()))),
            Stmt::Output(n, t) => Some((true, n.clone(), PTy::Data(t.clone()))),
            Stmt::Port(p) if p.key.is_none() => Some((p.output, p.name.clone(), p.ty.clone())),
            _ => None,
        };
        let Some((output, name, ty)) = scalar else {
            return false;
        };
        if !self.always || !self.site(Kind::ScalarFamily) {
            return false;
        }
        // The family cycles with the site, so that a module with several
        // families offers each of them, also one that only an untaken arm
        // declares.
        let family = self.families.get((self.seen - 1) % self.families.len());
        let Some(family) = family.cloned() else {
            return false;
        };
        let what = format!("give the scalar port {name} the key of the family {family}");
        *s = Stmt::Port(Port {
            output,
            name,
            key: None,
            public: Some(SExpr::Str(family)),
            ty,
        });
        self.hit(
            format!("{what} in {}", self.item),
            Effect::Code(Some("S019")),
        );
        true
    }

    /// The target of a `:=`.
    fn place_parts(&mut self, place: &mut Place) {
        match place {
            Place::Name(n) | Place::Field(n, _) => self.rename(n),
            Place::Path(e) => self.hexpr(e),
            Place::Entry(fam, k) => {
                self.rename(fam);
                self.entry_key(k);
            }
            Place::ChildEntry(u, _, k) => {
                self.rename(u);
                self.entry_key(k);
            }
        }
    }

    /// The key of a selection: a site of `KeyRange` and `KeyType`, else a
    /// static expression.
    fn entry_key(&mut self, k: &mut SExpr) {
        if !self.family_key(k) {
            self.sexpr(k);
        }
    }

    /// Records the ports and registers of a module.
    fn note_hardware(&mut self, s: &Stmt) {
        if let Stmt::Input(n, _) | Stmt::Reg(n, ..) = s {
            self.hardware.push(n.clone());
        }
        if let Stmt::Port(p) = s
            && p.key.is_none()
            && !p.output
        {
            self.hardware.push(p.name.clone());
        }
        if let Stmt::Input(n, t) | Stmt::Reg(n, t, _) | Stmt::Wire(n, t) = s {
            self.typed.push((n.clone(), t.clone()));
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

    /// Whether the value `e` is certainly hardware: it reads a port, a
    /// register, or a binder of such a value through an operator, a
    /// constructor, or `reinterpret`. A name of a `let` can hold a static
    /// value, so it does not count. A static operand does not make an
    /// operator static, because the other operand is hardware. An `if` and
    /// a `match` fold when their condition or scrutinee is static, and a
    /// call can drop its operands, so none of them counts.
    fn certainly_hardware(&self, e: &HExpr) -> bool {
        match e {
            HExpr::Name(n) => self.hardware.contains(n),
            HExpr::Unary(_, a) | HExpr::Resize(_, a) | HExpr::Reinterpret(_, a) => {
                self.certainly_hardware(a)
            }
            // `&&` and `||` do not run their right operand if the left one
            // decides, so `false && x` is static. The other operators run
            // both.
            HExpr::Binary(HBin::Land | HBin::Lor, a, _) => self.certainly_hardware(a),
            HExpr::Binary(_, a, b) => self.certainly_hardware(a) || self.certainly_hardware(b),
            HExpr::Ctor(_, _, args) => args.iter().any(|a| self.certainly_hardware(a)),
            _ => false,
        }
    }

    /// The arms of a hardware `match` over a value that is certainly
    /// hardware. All arms evaluate, each under the guard `arm` (spec 9.4),
    /// so a graph effect in one is `S016`, as in an arm of a hardware `if`.
    /// Its binders are certainly hardware too, and `Rename` skips their
    /// declarations.
    fn hardware_arms(&mut self, m: &mut Match<HExpr, HExpr>) {
        let (always, reach, arm) = (self.always, self.reach, self.arm);
        let marked = self.hardware.len();
        for (p, body) in &mut m.arms {
            (self.always, self.reach, self.arm) = (false, reach, true);
            if let Pattern::Variant(e, _, binders) = p {
                self.rename(e);
                self.hardware.extend(binders.iter().flatten().cloned());
            }
            self.hexpr(body);
            self.hardware.truncate(marked);
            if self.hit.is_some() {
                break;
            }
        }
        (self.always, self.reach, self.arm) = (always, reach, arm);
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

    /// A use of the enum or struct `name`, which counts as a use of the top
    /// frame if the site always runs, and a site of `Rename`.
    fn use_name(&mut self, name: &mut String) {
        if self.always {
            self.used.push(name.clone());
        }
        self.rename(name);
    }

    /// The sites of the arms of a `match` that always runs: `S021` by the
    /// coverage rules of spec 5.6. The arms cover each value, so `_` is
    /// there exactly when the other arms cover fewer than `2^W` values.
    fn arm_sites<S, E: Clone>(&mut self, m: &mut Match<S, E>, text: fn(&E) -> String) -> bool {
        let code = self.always.then_some("S021");
        let wild = m.arms.iter().any(|(p, _)| *p == Pattern::Wild);
        for i in 0..m.arms.len() {
            if self.pattern_sites(m, i, text) {
                return true;
            }
            let is_wild = m.arms.get(i).is_some_and(|(p, _)| *p == Pattern::Wild);
            if self.site(Kind::DeleteArm) {
                // Another arm of a match with `_` leaves the match covered.
                let code = (is_wild || !wild).then_some(code).flatten();
                m.arms.remove(i);
                self.hit(
                    format!("delete arm {} of a match in {}", i + 1, self.item),
                    Effect::Code(code),
                );
                return true;
            }
            if self.site(Kind::DuplicateArm) {
                let copy = m.arms.get(i).cloned();
                if let Some(copy) = copy {
                    m.arms.insert(i + 1, copy);
                }
                self.hit(
                    format!("copy arm {} of a match in {}", i + 1, self.item),
                    Effect::Code(code),
                );
                return true;
            }
        }
        let last_wild =
            m.arms.len() >= 2 && m.arms.last().is_some_and(|(p, _)| *p == Pattern::Wild);
        if last_wild && self.site(Kind::WildFirst) {
            let at = m.arms.len() - 2;
            let arm = m.arms.pop();
            if let Some(arm) = arm {
                m.arms.insert(at, arm);
            }
            self.hit(
                format!("move `_` before the last arm of a match in {}", self.item),
                Effect::Code(code),
            );
            return true;
        }
        // The new arm takes the body of an arm that reads no binder.
        let body = m.arms.iter().find(|(p, e)| {
            let binders = match p {
                Pattern::Variant(_, _, bs) => bs.iter().flatten().cloned().collect(),
                _ => Vec::new(),
            };
            binders.iter().all(|b| !mentions_token(&text(e), b))
        });
        if !wild
            && let Some((_, body)) = body.cloned()
            && self.site(Kind::DeadWild)
        {
            m.arms.push((Pattern::Wild, body));
            self.hit(
                format!("add `_` to a match that covers each value in {}", self.item),
                Effect::Code(code),
            );
            return true;
        }
        false
    }

    /// Whether `e` is an enum value that is certainly typed so: a
    /// constructor, a `reinterpret` of bits, or the zero of an enum.
    fn is_enum_value(&self, e: &SExpr) -> bool {
        match e {
            SExpr::Ctor(..) | SExpr::Unpack(..) => true,
            SExpr::Zero(name, _) => self.enum_names.contains(name),
            _ => false,
        }
    }

    /// The sites `EnumEq` and `EnumCall` on a static enum value. Both are
    /// `S010` (spec 5.1, 5.6) where the value always runs.
    fn enum_sites(&mut self, e: &mut SExpr) -> bool {
        if !self.is_enum_value(e) {
            return false;
        }
        let code = self.always.then_some("S010");
        if self.site(Kind::EnumEq) {
            let what = format!("compare {} with itself in {}", sexpr_text(e), self.item);
            *e = SExpr::Binary(SBin::Eq, Box::new(e.clone()), Box::new(e.clone()));
            self.hit(what, Effect::Code(code));
            return true;
        }
        if let SExpr::Zero(name, _) = e
            && self.site(Kind::EnumCall)
        {
            let what = format!("call the enum {name} with an argument in {}", self.item);
            *e = SExpr::Call(name.clone(), vec![zero()]);
            self.hit(what, Effect::Code(code));
            return true;
        }
        false
    }

    /// `EnumEq` on a hardware enum: a constructor, or the name of a port,
    /// register, or wire of an enum type.
    fn hardware_enum_eq(&mut self, e: &mut HExpr) -> bool {
        let is_enum = match e {
            HExpr::Ctor(..) => true,
            HExpr::Name(n) => self
                .typed
                .iter()
                .any(|(m, t)| m == n && matches!(t, Ty::Enum(_))),
            _ => false,
        };
        if !is_enum || !self.site(Kind::EnumEq) {
            return false;
        }
        let what = format!("compare {} with itself in {}", hexpr_text(e), self.item);
        *e = HExpr::Binary(HBin::Eq, Box::new(e.clone()), Box::new(e.clone()));
        self.hit(what, Effect::Code(self.always.then_some("S010")));
        true
    }

    /// `ArmStage`: a static `Int` operand of a module body becomes a
    /// `match` on a port with the arms `0 => 0` and `_ => 1`. A hardware
    /// scrutinee evaluates both arms, whose static parts differ (`S011`,
    /// spec 5.6).
    fn arm_stage(&mut self, e: &mut HExpr) -> bool {
        let port = self.typed.iter().find_map(|(n, t)| {
            let finite = matches!(t, Ty::UInt(_) | Ty::SInt(_));
            (finite && self.hardware.contains(n)).then(|| n.clone())
        });
        let Some(port) = port else { return false };
        // Only a site that always runs is a site, so the top frame of a
        // module body holds all of them.
        if !self.always || !self.site(Kind::ArmStage) {
            return false;
        }
        let zero_arm = HExpr::Static(zero());
        let one_arm = HExpr::Static(SExpr::Int(BigInt::from(1), Radix::Dec));
        let what = format!(
            "stage the operand {} on {port} in {}",
            hexpr_text(e),
            self.item
        );
        *e = HExpr::Match(Match {
            scrutinee: Box::new(HExpr::Name(port)),
            arms: vec![
                (Pattern::Int(BigInt::ZERO, Radix::Dec), zero_arm),
                (Pattern::Wild, one_arm),
            ],
        });
        self.hit(what, Effect::Code(Some("S011")));
        true
    }

    /// The sites in the pattern of arm `i`: two binders with one name
    /// (`S002`, pass 2), a binder more or less (`S007`, pass 4), and a
    /// pattern of another kind (`S010`, pass 5). The binder that goes, and
    /// the arm whose pattern changes its kind, are not read by the arm,
    /// because pass 3 would see the missing name first.
    fn pattern_sites<S, E>(
        &mut self,
        m: &mut Match<S, E>,
        i: usize,
        text: fn(&E) -> String,
    ) -> bool {
        let Some((pattern, body)) = m.arms.get_mut(i) else {
            return false;
        };
        let body = text(body);
        let read =
            |binders: &[Option<String>]| binders.iter().flatten().any(|b| mentions_token(&body, b));
        if let Pattern::Variant(e, v, binders) = pattern {
            let named: Vec<usize> = (0..binders.len())
                .filter(|&k| binders.get(k).is_some_and(Option::is_some))
                .collect();
            if let [first, second, ..] = named[..]
                && self.site(Kind::DupBinder)
            {
                let name = binders.get(first).cloned().flatten();
                if let Some(slot) = binders.get_mut(second) {
                    *slot = name;
                }
                self.hit(
                    format!("give two binders of {e}::{v} one name in {}", self.item),
                    Effect::Code(Some("S002")),
                );
                return true;
            }
            let last_free = binders
                .last()
                .is_some_and(|b| b.as_ref().is_none_or(|b| !mentions_token(&body, b)));
            if last_free && self.site(Kind::DropArg) {
                binders.pop();
                self.hit(
                    format!("drop a binder of {e}::{v} in {}", self.item),
                    Effect::Code(Some("S007")),
                );
                return true;
            }
            if self.site(Kind::AddArg) {
                binders.push(None);
                self.hit(
                    format!("add a binder to {e}::{v} in {}", self.item),
                    Effect::Code(Some("S007")),
                );
                return true;
            }
        }
        let free = match pattern {
            Pattern::Variant(_, _, bs) => !read(bs),
            Pattern::Wild => false,
            _ => true,
        };
        if free && self.site(Kind::PatternSwap) {
            let new = match pattern {
                Pattern::Int(..) => Pattern::Bool(true),
                _ => Pattern::Int(BigInt::ZERO, Radix::Dec),
            };
            self.hit(
                format!("change the kind of a pattern in {}", self.item),
                Effect::Code(self.always.then_some("S010")),
            );
            *pattern = new;
            return true;
        }
        false
    }

    /// `PatternFit`: a literal arm of a match on a port or register with a
    /// literal width passes the type of the scrutinee (`S012`, spec 5.6).
    fn pattern_fit(&mut self, m: &mut Match<HExpr, HExpr>) -> bool {
        let HExpr::Name(n) = &*m.scrutinee else {
            return false;
        };
        let known = self.typed.iter().find_map(|(name, t)| match t {
            Ty::UInt(SExpr::Int(w, _)) if name == n => Some((false, w.clone())),
            Ty::SInt(SExpr::Int(w, _)) if name == n => Some((true, w.clone())),
            _ => None,
        });
        let Some((signed, width)) = known.and_then(|(s, w)| u32::try_from(w).ok().map(|w| (s, w)))
        else {
            return false;
        };
        for (p, _) in &mut m.arms {
            if matches!(p, Pattern::Int(..)) && self.site(Kind::PatternFit) {
                *p = Pattern::Int(beyond(signed, width), Radix::Dec);
                self.hit(
                    format!("make a literal pass {n} in {}", self.item),
                    Effect::Code(self.always.then_some("S012")),
                );
                return true;
            }
        }
        false
    }

    /// The sites of an `enum` item: a tag that repeats the first tag is
    /// `S021` at the first use of the enum, which is certain if the top
    /// frame of a module uses the enum.
    fn enum_item(&mut self, def: &mut EnumDef) {
        let top = self.used.contains(&def.name).then_some("S021");
        let fit = self.used.contains(&def.name).then_some("S012");
        for i in 0..def.variants.len() {
            if self.site(Kind::Duplicate) {
                if let Some(v) = def.variants.get(i).cloned() {
                    def.variants.insert(i + 1, v);
                }
                self.hit(
                    format!("duplicate variant {} of {}", i + 1, def.name),
                    Effect::Code(Some("S002")),
                );
                return;
            }
            if i > 0 && self.site(Kind::SameTag) {
                let first = def.variants.first().map(|v| v.tag.clone());
                if let (Some(first), Some(v)) = (first, def.variants.get_mut(i)) {
                    v.tag = first;
                    self.hit(
                        format!("give variant {} of {} the first tag", i + 1, def.name),
                        Effect::Code(top),
                    );
                }
                return;
            }
            if self.site(Kind::TagFit)
                && let Some(v) = def.variants.get_mut(i)
            {
                v.tag = beyond(false, def.tag_width).into_parts().1;
                self.hit(
                    format!(
                        "give variant {} of {} a tag that does not fit",
                        i + 1,
                        def.name
                    ),
                    Effect::Code(fit),
                );
                return;
            }
        }
        // A tag is free if the tag type has more values than variants.
        let free = (0..1u32 << def.tag_width)
            .map(num_bigint::BigUint::from)
            .find(|t| def.variants.iter().all(|v| v.tag != *t));
        if let Some(tag) = free
            && self.site(Kind::PayloadOverflow)
        {
            def.variants.push(Variant {
                name: format!("V{}", def.variants.len()),
                tag,
                payload: vec![Scalar::UInt(65536), Scalar::Bool],
            });
            self.hit(
                format!("add a variant of 65537 payload bits to {}", def.name),
                Effect::Code(fit),
            );
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

    fn fty(&mut self, t: &mut FTy) {
        match t {
            FTy::Data(t) | FTy::Reg(t) | FTy::Wire(t) | FTy::Input(t) => self.ty(t),
            FTy::Mem(t, depth) => {
                self.ty(t);
                self.sexpr(depth);
            }
            FTy::Instance(module, args) => {
                self.rename(module);
                for a in args {
                    self.sexpr(a);
                }
            }
            FTy::Tuple(ts) => {
                for t in ts {
                    self.fty(t);
                }
            }
            FTy::Array(t, _) | FTy::List(t) => self.fty(t),
            FTy::Struct(name) => self.rename(name),
            FTy::Unit | FTy::Static(_) => {}
        }
    }

    fn ty(&mut self, t: &mut Ty) {
        match t {
            Ty::UInt(w) | Ty::SInt(w) => self.width(w),
            Ty::Enum(name) => self.use_name(name),
            Ty::Bool => {}
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
        if self.enum_sites(e) {
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
            SExpr::Ctor(name, _, args) => {
                self.use_name(name);
                self.args(name, args, zero());
                for x in args {
                    self.sexpr(x);
                }
            }
            SExpr::Unpack(name, a) | SExpr::Pack(name, a) | SExpr::BitsConv(name, a) => {
                self.use_name(name);
                self.sexpr(a);
            }
            SExpr::Zero(name, targs) | SExpr::DataBits(name, targs) => {
                self.use_name(name);
                for x in targs {
                    self.sexpr(x);
                }
            }
            SExpr::Select(a, ..)
            | SExpr::Field(a, _)
            | SExpr::Len(a)
            | SExpr::StrOf(a)
            | SExpr::Convert(_, a)
            | SExpr::Unary(_, a) => {
                self.sexpr(a);
            }
            SExpr::Binary(SBin::Land | SBin::Lor, a, b) => {
                self.sexpr(a);
                self.lazily(|w| w.sexpr(b));
            }
            SExpr::Index(a, b) | SExpr::PortKey(a, _, b) | SExpr::Binary(_, a, b) => {
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
            SExpr::Match(m) => {
                if self.arm_sites(m, sexpr_text) {
                    return;
                }
                self.sexpr(&mut m.scrutinee);
                // Only the selected arm runs. The binders are declarations,
                // so no site renames them.
                self.lazily(|w| {
                    for (p, arm) in &mut m.arms {
                        if let Pattern::Variant(e, ..) = p {
                            w.rename(e);
                        }
                        w.sexpr(arm);
                    }
                });
            }
        }
    }

    /// The expressions of handles and of memory ports.
    fn handle_expr(&mut self, e: &mut HExpr) {
        match e {
            HExpr::Tuple(xs) | HExpr::Array(xs) => {
                for x in xs {
                    self.hexpr(x);
                }
            }
            HExpr::Record(name, xs) => {
                self.rename(name);
                for x in xs {
                    self.hexpr(x);
                }
            }
            HExpr::Index(b, i) => {
                self.hexpr(b);
                self.sexpr(i);
            }
            HExpr::Select(b, _) | HExpr::Read(b) => self.hexpr(b),
            HExpr::ReadPort { mem, addr, en, .. } => {
                self.rename(mem);
                self.hexpr(addr);
                self.hexpr(en);
            }
            _ => {}
        }
    }

    /// A call of a helper. An actual of a `comptime` formal is a static
    /// position, not an operand.
    fn call_parts(&mut self, f: &mut String, args: &mut Vec<HExpr>) {
        self.rename(f);
        self.args(f, args, HExpr::Static(zero()));
        let statics = self
            .static_formals
            .get(f.as_str())
            .cloned()
            .unwrap_or_default();
        for (i, a) in args.iter_mut().enumerate() {
            match a {
                // A hardware value there is `S005`, not the `S011` of the
                // stage.
                HExpr::Static(s) if statics.get(i) == Some(&true) => self.sexpr(s),
                a => self.hexpr(a),
            }
        }
    }

    fn hexpr(&mut self, e: &mut HExpr) {
        if self.hardware_enum_eq(e)
            || (matches!(e, HExpr::Static(s) if int_valued(s)) && self.arm_stage(e))
        {
            return;
        }
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
            HExpr::Call(f, args) => self.call_parts(f, args),
            HExpr::Match(m) => {
                if self.arm_sites(m, hexpr_text) || self.pattern_fit(m) {
                    return;
                }
                self.hexpr(&mut m.scrutinee);
                if self.certainly_hardware(&m.scrutinee) {
                    self.hardware_arms(m);
                } else {
                    // The front ends fold a scrutinee that is static by
                    // value, and the match then selects one arm, so no arm
                    // always runs.
                    self.lazily(|w| {
                        for (p, arm) in &mut m.arms {
                            if let Pattern::Variant(e, ..) = p {
                                w.rename(e);
                            }
                            w.hexpr(arm);
                        }
                    });
                }
            }
            HExpr::Ctor(name, _, args) => {
                self.use_name(name);
                self.args(name, args, HExpr::Static(zero()));
                for a in args {
                    self.hexpr(a);
                }
            }
            HExpr::Unit => {}
            HExpr::Entry(fam, k) => {
                self.rename(fam);
                self.entry_key(k);
            }
            HExpr::ChildEntry(u, _, k) => {
                self.rename(u);
                self.entry_key(k);
            }
            HExpr::Tuple(_)
            | HExpr::Array(_)
            | HExpr::Record(..)
            | HExpr::Index(..)
            | HExpr::Select(..)
            | HExpr::Read(_)
            | HExpr::ReadPort { .. } => self.handle_expr(e),
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

/// The helpers with a `comptime` formal, and which formals are those.
fn static_formals(items: &[Item]) -> BTreeMap<String, Vec<bool>> {
    items
        .iter()
        .filter_map(|item| match item {
            Item::Helper { name, params, .. }
                if params.iter().any(|(_, t)| matches!(t, FTy::Static(_))) =>
            {
                let flags = params
                    .iter()
                    .map(|(_, t)| matches!(t, FTy::Static(_)))
                    .collect();
                Some((name.clone(), flags))
            }
            _ => None,
        })
        .collect()
}

/// The helpers with a formal of a handle type or a list of handles: the
/// `Call` of one binds its actuals.
fn binders(items: &[Item]) -> Vec<String> {
    items
        .iter()
        .filter_map(|item| match item {
            Item::Helper { name, params, .. }
                if params
                    .iter()
                    .any(|(_, t)| !matches!(t, FTy::Data(_) | FTy::Unit | FTy::Static(_))) =>
            {
                Some(name.clone())
            }
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
        Item::Enum(def) => &def.name,
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
        | Stmt::Mem(n, _, _)
        | Stmt::Port(Port { name: n, .. })
        | Stmt::HList(n, _)
        | Stmt::Let { name: n, .. }
        | Stmt::StaticLet(n, _, _)
        | Stmt::MutLet(n, _, _)
        | Stmt::PopLet(n, _)
        | Stmt::MutCall { name: n, .. }
        | Stmt::Instance(n, _, _) => Some(n),
        _ => None,
    }
}

/// The number of indexed declarations of each name in `body`.
fn count_indexed(body: &[Stmt], counts: &mut BTreeMap<String, usize>) {
    for s in body {
        match s {
            Stmt::Port(p) if p.key.is_some() => *counts.entry(p.name.clone()).or_default() += 1,
            Stmt::If(_, then, els) => {
                count_indexed(then, counts);
                count_indexed(els.as_deref().unwrap_or_default(), counts);
            }
            Stmt::For(_, _, _, inner) | Stmt::Block(inner) => count_indexed(inner, counts),
            _ => {}
        }
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

/// Whether `token` is a word of `text`: a name between characters that no
/// name has.
fn mentions_token(text: &str, token: &str) -> bool {
    text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|word| word == token)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn walk() -> Walk<'static> {
        let mut w = Walk::new(Kind::Rename, "M0", None);
        w.hardware.push("i0".to_owned());
        w
    }

    fn hw(name: &str) -> HExpr {
        HExpr::Name(name.to_owned())
    }

    fn stat(b: bool) -> HExpr {
        HExpr::Static(SExpr::Bool(b))
    }

    fn bin(op: HBin, a: HExpr, b: HExpr) -> HExpr {
        HExpr::Binary(op, Box::new(a), Box::new(b))
    }

    /// `false && x` and `true || x` are static, so only the left operand of
    /// `&&` and `||` decides. The other operators run both operands. A
    /// folding `if` or `match` is no hardware.
    #[test]
    fn a_lazy_or_folding_form_is_hardware_by_its_first_operand() {
        let w = walk();
        assert!(w.certainly_hardware(&bin(HBin::Land, hw("i0"), stat(true))));
        assert!(!w.certainly_hardware(&bin(HBin::Land, stat(false), hw("i0"))));
        assert!(!w.certainly_hardware(&bin(HBin::Lor, stat(true), hw("i0"))));
        assert!(w.certainly_hardware(&bin(HBin::Addw, stat(true), hw("i0"))));
        assert!(w.certainly_hardware(&bin(HBin::Eq, hw("i0"), stat(true))));
        let folding = HExpr::If(Box::new(stat(true)), Box::new(hw("i0")), Box::new(hw("i0")));
        assert!(!w.certainly_hardware(&folding));
        let selected = HExpr::Match(Match {
            scrutinee: Box::new(stat(true)),
            arms: vec![(Pattern::Wild, hw("i0"))],
        });
        assert!(!w.certainly_hardware(&selected));
        assert!(!w.certainly_hardware(&HExpr::Call("h0".to_owned(), vec![hw("i0")])));
        assert!(!w.certainly_hardware(&hw("l0")));
    }
}
