// SPDX-License-Identifier: Apache-2.0
//! The builtin `@field(x, k)` as a value, and the kind checks of its key, of Lean
//! `Source.Eval.Field` and `Eval.fieldOut` (design sections 6.2 and 9.3).
//!
//! The step evaluates its key in the walk of a read, as an index does (`Evaluator::named_key`).
//! The step ends its segment, and the base reads after the key evaluated and passed the static
//! check. The base gives the key type that it takes (`Base`). The key gets its kind check
//! (`Evaluator::key_plan`), and a `String` key and the name of a `PortKey` charge their size
//! before a look-up reads them (`Evaluator::name_sym`). The look-up adds no name. The selection is
//! then the ordinary one that the key names: a field, an index, or a public port of a child. A
//! key never copies its string: the step reads it where it lies in the store.

use super::inst::{child_key, no_port};
use super::place::{Index, Key, Named, elem};
use super::record::FieldName;
use super::source;
use super::{Evaluator, GuardKind, Opnd, Out, Res, at, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Handle, Port, Seen};
use crate::names::{PathId, Step, Sym, entry_text};
use crate::ops::{Fuel, fit_text, str_text};
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Builtin, Expr, Pos};

/// An `Instance` handle: its child number, its path, its instantiation, and its type.
#[derive(Clone, Copy)]
pub(super) struct InstInfo {
    pub(super) id: usize,
    pub(super) path: PathId,
    pub(super) inst: usize,
    pub(super) ty: TyId,
}

/// The kind of a base of `@field`: a record, an enum, an array, a list, or a tuple (`Seq`), or an
/// `Instance` handle.
#[derive(Clone, Copy)]
pub(super) enum Base {
    Record,
    Enum(TyId),
    Seq,
    Inst(InstInfo),
}

impl Base {
    /// The key type `{w}` that the base takes, in the text "Key of `@field`".
    fn want(self) -> &'static str {
        match self {
            Base::Record | Base::Enum(_) => "`String`",
            Base::Seq => "`Nat`",
            Base::Inst(_) => "`String` or `PortKey`",
        }
    }
}

/// What a key of `@field` names, after its kind check: a name that waits for its size charge, an
/// index, or the public name of a port of a child with the key of an entry. The name borrows the
/// key where it lies in the store.
pub(super) enum Plan<'v> {
    Name(&'v str),
    Index,
    Port(InstInfo, &'v str, Option<u32>),
}

impl Plan<'_> {
    /// The name that charges its size before a look-up reads it.
    pub(super) fn name(&self) -> Option<&str> {
        match self {
            Plan::Name(x) | Plan::Port(_, x, _) => Some(x),
            Plan::Index => None,
        }
    }
}

/// The part that the key selects in a value, as the apply of the step needs it.
pub(super) enum Pick {
    /// A field: its number, its type, and the step of a reference.
    Field(usize, TyId, Step),
    Index(Index),
    Port(InstInfo, Port),
}

/// What the part is, where a key of `@field` selects: a value that the store or the walk holds,
/// or only a data type.
#[derive(Clone, Copy)]
pub(super) enum At<'s> {
    Seen(Seen<'s>),
    Ty(TyId),
}

/// The `S010` "Base of `@field`" of section 6.2 at `pos`, for the base `a`.
pub(super) fn base_error<T>(pos: Pos, a: &str) -> Res<T> {
    fail(
        Code::S010,
        pos,
        format!(
            "`@field` selects in a record, an array, a list, a tuple, or an instance, not {a}; \
             select from such a value"
        ),
    )
}

/// The number of a key that is a non-negative integer.
fn key_number(v: &Value) -> Option<usize> {
    match v {
        Value::Int(k) => k.to_u64().and_then(|k| usize::try_from(k).ok()),
        _ => None,
    }
}

impl Evaluator<'_> {
    /// The key `key` of the `@field` step at `q` with the base `base`. It evaluates as the index
    /// of a read does, with no guard of its own, and it is static (`S011`). A handle gives
    /// "Handle at a static position", and another hardware value gives "Value not static". In a
    /// query operand (`query`), the key evaluates in a structural context of the kind `Query`.
    pub(super) fn named_key<'a>(
        &mut self,
        q: Pos,
        base: &'a Expr,
        key: &'a Expr,
        query: bool,
    ) -> Res<Key<'a>> {
        let o = if query {
            self.guarded(GuardKind::Query(Builtin::TypeOf), |ev| {
                let o = ev.eval(key)?;
                need(key, o)
            })?
        } else {
            let o = self.eval(key)?;
            need(key, o)?
        };
        let kp = key.pos();
        let position = if query {
            "a key of `@TypeOf`"
        } else {
            "a key of `@field`"
        };
        self.static_position(kp, position, &o)?;
        self.check_static(kp, &o)?;
        let number = key_number(self.store.value(&o));
        Ok(Key::Named(Named {
            pos: q,
            base,
            kp,
            charges: self.key_name(self.store.value(&o)).is_some(),
            key: o,
            at: number,
            paid: false,
        }))
    }

    /// Pays the size of the name of the key `named` at its step, if the key has a name and the fuel
    /// can pay it. A key that the fuel cannot pay stays unpaid, and its step ends the segment, so
    /// the checks of the step come before the failed charge (Lean `fieldKeyOf`).
    pub(super) fn pay_early(&mut self, named: &mut Named<'_>) {
        if let Some(name) = self.key_name(self.store.value(&named.key))
            && Self::pay_name(&mut self.fuel, named.kp, name).is_ok()
        {
            named.paid = true;
        }
    }

    /// Whether the step `n` needs its whole base as a result, and not as a part of a stored
    /// container: the base is a handle, a hardware value, or a pending literal, or the name of the
    /// key still waits for its charge.
    pub(super) fn named_whole(&self, n: &Named<'_>, base: &Opnd) -> bool {
        (n.charges && !n.paid) || !matches!(self.opnd_seen(base), Seen::Static(_) | Seen::Agg(_))
    }

    /// The number of the part that the step `n` names in a container of the type `ty`, with no
    /// check: an integer key names its part, and a name names a field only after its charge.
    pub(super) fn named_slot(&self, ty: Option<TyId>, n: &Named<'_>) -> Option<usize> {
        if n.at.is_some() {
            return n.at;
        }
        let Value::Str(name) = self.store.value(&n.key) else {
            return None;
        };
        if !n.paid {
            return None;
        }
        let y = self.syms.find(name)?;
        let parts = self.tys.parts(ty?)?;
        self.field_number_by(parts.item()?, Some(y), name)
    }

    /// The number of the field that the paid name of the step `n` names in the record `a`.
    pub(super) fn named_agg_field(&self, n: &Named<'_>, a: &Agg) -> Option<usize> {
        let Value::Str(name) = self.store.value(&n.key) else {
            return None;
        };
        if !n.paid {
            return None;
        }
        let y = self.syms.find(name)?;
        self.agg_field_at_by(a, Some(y), name).map(|(k, _)| k)
    }

    /// The number and the field type of the part that the step `n` selects in the static
    /// container `seen`, after its checks and the charge of its name. A static container holds no
    /// handle, so no step selects a port.
    pub(super) fn named_number(&self, n: &Named<'_>, seen: Seen<'_>) -> Res<(usize, Option<TyId>)> {
        let key = self.store.value(&n.key);
        let plan = self.named_plan(n, At::Seen(seen), key)?;
        match self.named_finish(n, seen, &plan)? {
            Pick::Field(k, ft, _) => Ok((k, Some(ft))),
            Pick::Index(i) => Ok((self.pick_at(n.pos, n.kp, seen, &i)?, None)),
            Pick::Port(..) => base_error(n.base.pos(), &self.about(seen)),
        }
    }

    /// The kind of the base that `seen` is, if `@field` selects in it (Lean `Val.fieldBase?`). A
    /// static tuple stores no type, so its form gives its kind with no walk. Another value gives
    /// its kind by its stored type.
    pub(super) fn field_base(&self, seen: Seen<'_>) -> Option<Base> {
        match seen {
            Seen::Handle(Handle::Inst { id, path, inst, ty }) => Some(Base::Inst(InstInfo {
                id: *id,
                path: *path,
                inst: *inst,
                ty: *ty,
            })),
            Seen::Static(Value::Record(..)) => Some(Base::Record),
            Seen::Static(Value::Array(..) | Value::Tuple(..) | Value::List(..)) => Some(Base::Seq),
            Seen::Static(Value::Enum(t, ..)) => Some(Base::Enum(*t)),
            Seen::Agg(a) => a.stored_ty().and_then(|t| self.type_base(t)),
            _ => None,
        }
    }

    /// The kind of a base of the data type `t` (Lean `Ty.fieldBase?`).
    pub(super) fn type_base(&self, t: TyId) -> Option<Base> {
        match self.tys.get(t) {
            Ty::Struct(_) => Some(Base::Record),
            Ty::Enum(_) => Some(Base::Enum(t)),
            Ty::Array(..) | Ty::Tuple(_) | Ty::List(_) => Some(Base::Seq),
            _ => None,
        }
    }

    /// The kind check of the static key `key` at `kp` on a base of the kind `base` (Lean
    /// `fieldKeyOf`, before the size charge). `about` gives the text of the base, only in an
    /// error. A record takes a `String`, and an enum too, but a `String` on an enum is "Field of
    /// an enum". An array, a list, and a tuple take a `Nat`: a negative key is `S012`. An
    /// `Instance` handle takes a `String` or a value of the prelude struct `PortKey`, with the
    /// checks of its index (`S022`, `S012`). Each other key is "Key of `@field`".
    pub(super) fn key_plan<'v>(
        &self,
        kp: Pos,
        base: Base,
        key: &'v Value,
        about: impl FnOnce() -> String,
    ) -> Res<Plan<'v>> {
        match (base, key) {
            (Base::Record, Value::Str(s)) => Ok(Plan::Name(s)),
            (Base::Enum(t), Value::Str(s)) => self.enum_field_error(kp, &str_text(s), t),
            (Base::Seq, Value::Int(i)) => {
                if i.is_negative() {
                    fail(Code::S012, kp, fit_text(&Ty::Nat, i, &self.tys))
                } else {
                    Ok(Plan::Index)
                }
            }
            (Base::Inst(info), k) => match self.port_key_of(kp, k) {
                Some(found) => {
                    let (x, entry) = found?;
                    Ok(Plan::Port(info, x, entry))
                }
                None => self.key_kind(kp, base, &about(), k),
            },
            (b, k) => self.key_kind(kp, b, &about(), k),
        }
    }

    /// The `S010` "Key of `@field`" at `kp`: the base `a` of the kind `base` takes another key
    /// than `key`.
    fn key_kind<T>(&self, kp: Pos, base: Base, a: &str, key: &Value) -> Res<T> {
        let w = base.want();
        fail(
            Code::S010,
            kp,
            format!(
                "`@field` on {a} takes {w}, not {}; give a static {w}",
                self.about(Seen::Static(key))
            ),
        )
    }

    /// The port of the child of the type `ty` and the instantiation `inst` that the key of
    /// `@field` selects (Lean `keyPort`). The key has the symbol `y` and the name `name`. A
    /// scalar key selects as `u.name` does (`port_named`). There a family is "Family as a value",
    /// with the base in its text, and no port is "No public port". An indexed key `name[k]`
    /// selects as `u.name[k]` does. There a family without the key `k` is `S013` "Child family
    /// key". A child without the family `name` is "No public port", with the public name
    /// `name[k]`.
    pub(super) fn key_port(
        &self,
        kp: Pos,
        (inst, ty): (usize, TyId),
        base: &Expr,
        (y, name): (Option<Sym>, &str),
        entry: Option<u32>,
    ) -> Res<Port> {
        let Some(k) = entry else {
            return self.port_named(kp, (inst, ty), (y, name), Some(base));
        };
        match y {
            Some(sym) if self.has_family(inst, sym) => match self.elab.port(inst, (sym, Some(k))) {
                Some(port) => Ok(port),
                None => child_key(kp, &self.tys.text(ty), name, k),
            },
            _ => no_port(kp, &self.tys.text(ty), &entry_text(name, Some(k))),
        }
    }

    /// The name of a family in the text "Family as a value": the base of an `@field` as the
    /// source form writes it, then `.` and the name, each with the limit of a string in a message
    /// (section 5.5).
    pub(super) fn family_name(base: &Expr, name: &str) -> String {
        format!(
            "{}.{}",
            str_text(&source::print(base, source::POSTFIX)),
            str_text(name)
        )
    }

    /// The `@field` step `n` on the base `out` of a read (Lean `fieldOut`, steps 5 to 9 of the
    /// `@field` order of section 6.2). A register, a wire, and an own output read as the base of
    /// an ordinary selection does (`base_data`), and so does a child input (`S017`). A container
    /// of handles reads nothing, so its part keeps its handle. Another base than a record, an
    /// enum, an array, a list, a tuple, or an `Instance` handle is "Base of `@field`" at the base.
    /// The errors of the key and of the look-up are at the key. The part refers to its base, so it
    /// charges no size.
    pub(super) fn named_step(&mut self, out: Out, n: &Named<'_>) -> Res<Out> {
        let out = match self.store.seen(&out) {
            Seen::Handle(Handle::Res { .. } | Handle::Input { .. }) | Seen::Pending(..) => {
                self.base_data(n.pos, out)?.into_out()
            }
            _ => out,
        };
        let seen = self.store.seen(&out);
        let key = self.store.value(&n.key);
        let plan = self.named_plan(n, At::Seen(seen), key)?;
        if !n.paid
            && let Some(name) = plan.name()
        {
            Self::pay_name(&mut self.fuel, n.kp, name)?;
        }
        let pick = self.named_finish(n, seen, &plan)?;
        self.named_apply(n, out, pick)
    }

    /// The kind checks of the step `n` at the part `at` (Lean `fieldKeyOf`, before the size
    /// charge). A part that is no base is "Base of `@field`" at the base. The key `key` is the
    /// static key of `n`, which the caller reads where it lies in the store.
    pub(super) fn named_plan<'v>(
        &self,
        n: &Named<'_>,
        at: At<'_>,
        key: &'v Value,
    ) -> Res<Plan<'v>> {
        let about = || match at {
            At::Seen(seen) => self.about(seen),
            At::Ty(t) => format!("a value of `{}`", self.tys.text(t)),
        };
        let base = match at {
            At::Seen(seen) => self.field_base(seen),
            At::Ty(t) => self.type_base(t),
        };
        let Some(base) = base else {
            return base_error(n.base.pos(), &about());
        };
        self.key_plan(n.kp, base, key, about)
    }

    /// The charge of the size of a name of a key at `kp`: 1 plus its characters. It parts the
    /// fuel from the evaluator, so the name can stay where it lies in the store.
    pub(super) fn pay_name(fuel: &mut Fuel, kp: Pos, name: &str) -> Res<()> {
        fuel.pay(1 + name.chars().count() as u128).map_err(at(kp))
    }

    /// The part of the value `seen` that the checked key of `n` selects, after the size charge
    /// of its name: the look-up of the symbol, and the checks of the selection. The look-up adds
    /// no name.
    pub(super) fn named_finish(&self, n: &Named<'_>, seen: Seen<'_>, plan: &Plan<'_>) -> Res<Pick> {
        match *plan {
            Plan::Name(name) => {
                let y = self.syms.find(name);
                let f = FieldName {
                    sym: y,
                    name,
                    keyed: true,
                };
                if y.is_none() {
                    return self.missing_field(n.kp, f, self.record_of(seen), seen);
                }
                if let Seen::Agg(agg) = seen {
                    let (k, ft, step) = self.agg_field_find(n.kp, f, y, agg)?;
                    return Ok(Pick::Field(k, ft, step));
                }
                let (k, ft) = self.field_at_by(n.kp, f, seen)?;
                Ok(Pick::Field(k, ft, Step::Elem(0)))
            }
            Plan::Index => Ok(Pick::Index(self.index_of(&n.key))),
            Plan::Port(info, name, entry) => {
                let y = self.syms.find(name);
                let port = self.key_port(n.kp, (info.inst, info.ty), n.base, (y, name), entry)?;
                Ok(Pick::Port(info, port))
            }
        }
    }

    /// The struct type of the record `seen`, if it is one.
    pub(super) fn record_of(&self, seen: Seen<'_>) -> Option<TyId> {
        match seen {
            Seen::Static(Value::Record(t, _)) => Some(*t),
            Seen::Agg(a) => self.record_ty(a),
            _ => None,
        }
    }

    /// The selection of `pick` in the base `out` at the node `n.pos`. A part of an aggregate
    /// normalizes there, and the part of a static value is a reference.
    fn named_apply(&mut self, n: &Named<'_>, out: Out, pick: Pick) -> Res<Out> {
        let on_agg = matches!(self.store.seen(&out), Seen::Agg(_));
        match pick {
            Pick::Field(k, ft, step) if on_agg => self.agg_part(n.pos, out, k, step, Some(ft)),
            Pick::Field(k, ..) => Ok(elem(Opnd::Static(out), k)),
            Pick::Index(i) if on_agg => self.agg_index(n.pos, n.kp, out, &i),
            Pick::Index(i) => {
                let k = self.pick_at(n.pos, n.kp, self.store.seen(&out), &i)?;
                Ok(elem(Opnd::Static(out), k))
            }
            Pick::Port(info, port) => self.port_out(n.pos, (info.id, info.path), port),
        }
    }
}
