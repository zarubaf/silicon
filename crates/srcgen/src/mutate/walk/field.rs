// SPDX-License-Identifier: Apache-2.0
//! The sites of the kinds of `@field` (front-end spec 6.2, 9.3). Each rewrite
//! changes the key or the base of one `@field` and fixes the first error
//! where the site always runs: the walk of `@field` checks the base, the
//! key, the kind of the key, and the look-up in this order, and the original
//! program has no other error.

use super::super::{EFFECT_FN, Effect, KEEP_FN, Kind};
use super::{LOCAL, Spot, Walk, zero};
use crate::program::{HExpr, Place, SBin, SExpr, STy, Stmt, Ty};
use num_bigint::BigInt;

/// The key that no field, element, or port has, and the key that no
/// container is long enough for.
const MISSING: &str = "zz";
const FAR: i64 = 99;
/// A name of more than 64 characters, which a message cuts (section 5.5).
const LONG: usize = 70;

/// The class of the key of an `@field`: a `String`, a `Nat`, or a `PortKey`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Key {
    Text,
    Nat,
    Port,
}

fn int(n: i64) -> SExpr {
    SExpr::Int(BigInt::from(n), crate::program::Radix::Dec)
}

impl Walk<'_> {
    fn key_class(&self, key: &SExpr) -> Key {
        match key {
            SExpr::Str(_) => Key::Text,
            SExpr::Binary(SBin::Add, a, _) if matches!(**a, SExpr::Str(_)) => Key::Text,
            SExpr::Name(n) if self.strs.contains(n) => Key::Text,
            SExpr::PortKey(..) => Key::Port,
            _ => Key::Nat,
        }
    }

    /// A text key that is `MISSING` or long, by the site.
    fn absent(&self) -> SExpr {
        if self.seen.is_multiple_of(2) {
            SExpr::Str(MISSING.to_owned())
        } else {
            SExpr::Str("a".repeat(LONG))
        }
    }

    /// Pass 4 sees a name of a port in a key on all code (spec 6.2, `S005`).
    const EVERYWHERE: &'static str = "S005";

    fn found(&mut self, what: &str, code: &'static str) {
        let code = (self.always || code == Self::EVERYWHERE).then_some(code);
        self.hit(format!("{what} in {}", self.item), Effect::Code(code));
    }

    /// The sites on a static `@field(base, key)` and on a chain with an early
    /// key.
    pub(super) fn static_field(&mut self, e: &mut SExpr) -> bool {
        if let SExpr::At(..) | SExpr::Index(..) = e
            && self.early_step(e)
        {
            return true;
        }
        let SExpr::At(base, key) = e else {
            return false;
        };
        let class = self.key_class(key);
        if self.site(Kind::FieldKeyType) {
            **key = if self.seen.is_multiple_of(2) {
                SExpr::Bool(true)
            } else {
                SExpr::Convert(STy::UInt(4), Box::new(zero()))
            };
            self.found("give @field a key of another type", "S010");
        } else if class == Key::Text && self.site(Kind::NoField) {
            **key = self.absent();
            self.found("give @field of a record a key of no field", "S010");
        } else if class == Key::Nat && self.site(Kind::FieldRange) {
            let negative = self.seen.is_multiple_of(2);
            **key = int(if negative { -1 } else { FAR });
            let code = if negative { "S012" } else { "S013" };
            self.found("give @field of a container a key out of range", code);
        } else if self.spot != Spot::Target && self.site(Kind::FieldBase) {
            **base = SExpr::Str("s".to_owned());
            self.found("give @field a String as its base", "S010");
        } else if let Some(def) = self.enum_names.first().cloned()
            && self.spot != Spot::Target
            && self.site(Kind::EnumField)
        {
            **base = SExpr::Zero(def, Vec::new());
            self.found("give @field an enum as its base", "S010");
        } else if let Some(input) = self.inputs.first().cloned()
            && self.site(Kind::KeyNotStatic)
        {
            **key = SExpr::Name(input);
            self.found("give @field the key of a port", Self::EVERYWHERE);
        } else if self.before.is_some()
            && let Some(input) = self.hardware_input()
            && self.site(Kind::KeyValue)
        {
            **key = SExpr::Name(LOCAL.to_owned());
            self.local_of(HExpr::Name(input), false);
            self.found("give @field a hardware value as its key", "S011");
        } else {
            return false;
        }
        true
    }

    /// An own input of a finite type that has bits: its value is hardware in
    /// each run.
    fn hardware_input(&self) -> Option<String> {
        let finite = |t: &Ty| match t {
            Ty::Bool => true,
            Ty::UInt(SExpr::Int(w, _)) | Ty::SInt(SExpr::Int(w, _)) => *w > BigInt::ZERO,
            _ => false,
        };
        self.typed
            .iter()
            .find(|(n, t)| self.inputs.contains(n) && finite(t))
            .map(|(n, _)| n.clone())
    }

    /// The statement `let gp0 = value;` before the statement of the site: a
    /// plain local, or a container of one child.
    fn local_of(&mut self, value: HExpr, mutable: bool) {
        let local = Stmt::Let {
            name: LOCAL.to_owned(),
            mutable,
            ty: None,
            value,
        };
        if let Some(before) = &mut self.before {
            before.push(local);
        }
    }

    /// `EarlyStep`: a key calls a function that runs a `diagnostic`, and an
    /// earlier step of the chain gets a key out of range. A front end that
    /// evaluates the later key before it checks the earlier step prints an
    /// extra record before the `S013`.
    fn early_step(&mut self, e: &mut SExpr) -> bool {
        let (SExpr::At(base, key) | SExpr::Index(base, key)) = e else {
            return false;
        };
        let effectful =
            matches!(&**key, SExpr::KeyCall(f, ..) if self.diag_fns.iter().any(|d| d == f));
        if !effectful {
            return false;
        }
        let (SExpr::At(_, earlier) | SExpr::Index(_, earlier)) = &mut **base else {
            return false;
        };
        if !self.site(Kind::EarlyStep) {
            return false;
        }
        **earlier = int(FAR);
        self.found(
            "give the step before a key with a diagnostic a key out of range",
            "S013",
        );
        true
    }

    /// The sites on a hardware `@field(base, key)`, in a read or a target.
    /// `ReadInput` has no site in a raw `let`: `S017` comes at a later use.
    pub(super) fn hardware_field(&mut self, e: &mut HExpr, raw: bool) -> bool {
        let HExpr::FieldOf(base, key) = e else {
            return false;
        };
        let class = self.key_class(key);
        let target = self.spot == Spot::Target;
        if !target
            && !raw
            && self.before.is_some()
            && let HExpr::Name(u) = &**base
            && self.children.contains_key(u.as_str())
            && self.site(Kind::InstanceData)
        {
            let child = HExpr::Name(u.clone());
            self.local_of(HExpr::Array(vec![child]), false);
            *e = HExpr::FieldOf(Box::new(HExpr::Name(LOCAL.to_owned())), int(0));
            self.found("read a child as data with @field", "S010");
            return true;
        }
        let hit = if self.site(Kind::FieldKeyType) {
            *key = SExpr::Bool(true);
            Some(("give @field a key of another type", "S010"))
        } else if class == Key::Text && self.site(Kind::NoField) {
            *key = self.absent();
            Some(("give @field of a child a key of no port", "S010"))
        } else if class == Key::Nat && self.site(Kind::FieldRange) {
            let negative = self.seen.is_multiple_of(2);
            *key = int(if negative { -1 } else { FAR });
            let code = if negative { "S012" } else { "S013" };
            Some(("give @field of handles a key out of range", code))
        } else if let Some(hit) = self.port_key_sites(key) {
            Some(hit)
        } else if !target && self.site(Kind::FieldBase) {
            **base = HExpr::Static(SExpr::Str("s".to_owned()));
            Some(("give @field a String as its base", "S010"))
        } else if let Some(input) = self.inputs.first().cloned()
            && self.site(Kind::KeyNotStatic)
        {
            *key = SExpr::Name(input);
            Some(("give @field the key of a port", Self::EVERYWHERE))
        } else if !target
            && !raw
            && let HExpr::Name(u) = &**base
            && let Some(input) = self.child_input(u)
            && self.site(Kind::ReadInput)
        {
            *key = SExpr::Str(input);
            Some(("read an input of a child with @field", "S017"))
        } else if self.before.is_some()
            && let Some(input) = self.hardware_input()
            && self.site(Kind::KeyValue)
        {
            *key = SExpr::Name(LOCAL.to_owned());
            self.local_of(HExpr::Name(input), false);
            Some(("give @field a hardware value as its key", "S011"))
        } else if target && class != Key::Text {
            self.target_key(key)
        } else {
            None
        };
        let Some((what, code)) = hit else {
            return false;
        };
        self.found(what, code);
        true
    }

    /// The sites on a `PortKey`: an index of 99 or `2^32` on an entry, the
    /// scalar form of an entry, and the index 1 of a scalar port.
    fn port_key_sites(&mut self, key: &mut SExpr) -> Option<(&'static str, &'static str)> {
        let SExpr::PortKey(_, indexed, index) = key else {
            return None;
        };
        if *indexed && self.site(Kind::FieldRange) {
            let range = self.seen.is_multiple_of(2);
            **index = if range {
                SExpr::Int(BigInt::from(1u64 << 32), crate::program::Radix::Dec)
            } else {
                int(FAR)
            };
            let code = if range { "S012" } else { "S013" };
            return Some(("give an entry key of @field an index out of range", code));
        }
        if *indexed && self.site(Kind::FamilyValue) {
            *indexed = false;
            **index = zero();
            return Some(("select a family of a child as a value with @field", "S010"));
        }
        if !*indexed && self.site(Kind::ScalarKeyIndex) {
            **index = int(1);
            return Some(("give the PortKey of a scalar port the index 1", "S022"));
        }
        None
    }

    /// `TargetKey`: the key of a `:=` target calls a function that runs a
    /// `diagnostic`. A graph effect in an index of a target is `S016`.
    pub(super) fn target_key(&mut self, key: &mut SExpr) -> Option<(&'static str, &'static str)> {
        let slot = match key {
            SExpr::PortKey(_, true, index) => &mut **index,
            SExpr::PortKey(..) | SExpr::Str(_) => return None,
            other => other,
        };
        if self.site(Kind::TargetKey) {
            *slot = SExpr::Call(EFFECT_FN.to_owned(), vec![slot.clone()]);
            return Some((
                "call the function that runs a diagnostic in the key of a target",
                "S016",
            ));
        }
        let root = self.counter()?;
        if !self.site(Kind::TargetMutation) {
            return None;
        }
        *slot = SExpr::Call(KEEP_FN.to_owned(), vec![SExpr::Name(root), slot.clone()]);
        Some((
            "call a function that changes a root in the key of a target",
            "S016",
        ))
    }

    /// `PortPlace`: after an instance statement, a local container of the
    /// child and an assignment to its first input through the container. A
    /// place cannot hold a port (spec 9.3).
    pub(super) fn port_place(&mut self, body: &mut Vec<Stmt>, i: usize) -> bool {
        let Some(Stmt::Instance(u, m, _)) = body.get(i) else {
            return false;
        };
        let Some(port) = self.module_inputs.get(m).and_then(|v| v.first()).cloned() else {
            return false;
        };
        if !self.site(Kind::PortPlace) {
            return false;
        }
        let u = u.clone();
        let local = Stmt::Let {
            name: LOCAL.to_owned(),
            mutable: true,
            ty: None,
            value: HExpr::Array(vec![HExpr::Name(u.clone())]),
        };
        let name = format!("{LOCAL}[0].{port}");
        let assign = Stmt::Assign(name, HExpr::Static(SExpr::Bool(true)));
        body.insert(i + 1, assign);
        body.insert(i + 1, local);
        let what = format!(
            "assign to the port {port} of {u} through a local in {}",
            self.item
        );
        self.hit(what, Effect::Code(self.always.then_some("S010")));
        true
    }

    /// `TargetBase`: the target of a `:=` becomes an `@field` on a static
    /// integer. The target kind of the base is `S017` (spec 5.2).
    pub(super) fn target_base(&mut self, place: &mut Place) -> bool {
        if !self.always {
            return false;
        }
        let Some(root) = self.counter() else {
            return false;
        };
        if !self.site(Kind::TargetBase) {
            return false;
        }
        let key = SExpr::Str("a".to_owned());
        let base = HExpr::FieldOf(Box::new(HExpr::Name(root.clone())), key);
        *place = Place::Path(base);
        let what = format!("select with @field in the integer {root} as a target");
        self.hit(
            format!("{what} in {}", self.item),
            Effect::Code(Some("S017")),
        );
        true
    }

    /// The first input of the module of the instance `u`.
    fn child_input(&self, u: &str) -> Option<String> {
        let module = self.children.get(u)?;
        self.module_inputs.get(module)?.first().cloned()
    }
}
