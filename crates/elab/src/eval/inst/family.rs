// SPDX-License-Identifier: Apache-2.0
//! The port families of design section 5.6, as Lean `Elab.entry`, `Eval.entryDecl`,
//! `Eval.familySel`, `Eval.childSel`, `Eval.familyTarget`, and `Elab.childTarget` define them.
//!
//! A family `req` holds one port for each key. An entry `input req[k]: T;` is one whole port with
//! the core name `req$<k>f`. It goes into the table `Work::entries` by its family binder and its
//! key, and no frame slot holds it. A key is a `u32` (section 5.4), so each compare, sort, and
//! name of a key takes constant work. The text of an error renders when the error is made.
//!
//! The order of the checks follows section 6.2. A declaration charges its statement, evaluates
//! its key in a structural context, takes the typed use of the key at `Nat` (`family_key`), takes
//! its type and its data type, and then checks that the key is new. A selection charges its index
//! node and its name node, evaluates its key, takes the checks of a key, and then looks up the
//! entry. A selection refers to the port: it charges no size and copies nothing.

use super::{Elab, PortDecl, entry_text};
use crate::Code;
use crate::agg::{Agg, Base};
use crate::eval::{Evaluator, GuardKind, Names, Out, Res, fail, need};
use crate::hw::{Handle, Port, Seen, Val};
use crate::names::{PathId, Step, Sym};
use crate::ops::int_text;
use crate::types::TyId;
use crate::value::Value;
use parse::ast::{Expr, Ident, NodeId, Pos, TypeExpr};
use resolve::{DeclId, Target};

/// The `S010` error "Family as a value" of section 6.2 at `pos`, for the family `x`.
pub(in crate::eval) fn family_value<T>(pos: Pos, x: &str) -> Res<T> {
    fail(
        Code::S010,
        pos,
        format!("`{x}` is a port family, not a value; select one port with `{x}[k]`"),
    )
}

/// The `S013` error "Child family key" of section 6.2 at `pos`, for the key `k` of the family `x`
/// of a child of the instance type `m`.
pub(in crate::eval) fn child_key<T>(pos: Pos, m: &str, x: &str, k: u32) -> Res<T> {
    fail(
        Code::S013,
        pos,
        format!("the child `{m}` has no entry `{x}[{k}]`; select a key that `{m}` declares"),
    )
}

/// A static family key as the typed use at `Nat` sees it: a key, a number out of range with its
/// text, or a value of another type with its description.
pub(in crate::eval) enum FamKey {
    Key(u32),
    Range(String),
    Other(String),
}

impl FamKey {
    /// The key, or the error at `pos`. A key below 0 or of 2^32 or more is `S012` "Family key
    /// range", and a key of another type is `S010` "Family key type". A static `UInt` is such a
    /// type.
    pub(in crate::eval) fn key(&self, pos: Pos) -> Res<u32> {
        match self {
            FamKey::Key(k) => Ok(*k),
            FamKey::Range(i) => fail(
                Code::S012,
                pos,
                format!("a family key is 0 to 4294967295, not {i}; use a key in this range"),
            ),
            FamKey::Other(a) => fail(
                Code::S010,
                pos,
                format!(
                    "a family key is a static `Nat`, not {a}; compute the key from static \
                     integers, for example a loop value"
                ),
            ),
        }
    }
}

impl Elab {
    /// The value and the declaration position of the entry `key` of the family `id`.
    fn entry(&self, id: DeclId, key: u32) -> Option<&(Val, Pos)> {
        self.work.entries.get(&(id, key))
    }
}

impl Evaluator<'_> {
    /// The binder of the family that the name node `node` targets, if it names a family.
    pub(in crate::eval) fn family_of(&self, node: NodeId) -> Option<DeclId> {
        match self.target(node) {
            Some(Target::Decl(id))
                if matches!(self.decl_ref(id).kind, resolve::Kind::Family { .. }) =>
            {
                Some(id)
            }
            _ => None,
        }
    }

    /// The symbol of the field name `f`, if the file scope has one.
    pub(in crate::eval) fn port_sym(&self, f: &Ident) -> Option<Sym> {
        match self.names {
            Names::Top => None,
            Names::File => self.syms.fields.get(&f.id).copied(),
        }
    }

    /// Whether the done instantiation `inst` has a port family with the symbol `sym`.
    pub(in crate::eval) fn has_family(&self, inst: usize, sym: Sym) -> bool {
        self.elab
            .interface(inst)
            .and_then(|i| self.syms.families.get(i.item))
            .is_some_and(|m| m.contains_key(&sym))
    }

    /// The family of a child that the field `f` of the base `b` names, when `b` is an `Instance`
    /// handle (Lean `childFamily`).
    pub(in crate::eval) fn child_family(&self, b: &Out, f: &Ident) -> bool {
        let Seen::Handle(Handle::Inst { inst, .. }) = self.store.seen(b) else {
            return false;
        };
        self.port_sym(f).is_some_and(|s| self.has_family(*inst, s))
    }

    /// The text of the port `port`: its name, or the entry `x[k]`.
    pub(in crate::eval) fn port_text(&self, port: &Port) -> String {
        let name = self.syms.texts.get(port.sym).map_or("", String::as_str);
        entry_text(name, port.key)
    }

    /// The family key that the static value `v` stands for. The text of an error renders here,
    /// when the key is out of range or of another type, so a key in range makes no text.
    pub(in crate::eval) fn fam_key(&self, v: &Value) -> FamKey {
        match v {
            Value::Int(i) => match i.to_u64().and_then(|k| u32::try_from(k).ok()) {
                Some(k) => FamKey::Key(k),
                None => FamKey::Range(int_text(i)),
            },
            v => FamKey::Other(self.about(Seen::Static(v))),
        }
    }

    /// The typed use of the static family key `v` at `Nat`, at the key `pos` (section 5.6).
    fn family_key(&self, pos: Pos, v: &Value) -> Res<u32> {
        self.fam_key(v).key(pos)
    }

    /// The key `o` at `kp` of a selection of the family `x` with its name at `np` (section 6.2).
    /// A hardware key is `S010` "Family as a value" at the name. A handle is no static value
    /// (`S011`). Then the key gets its typed use (`family_key`).
    pub(in crate::eval) fn selection_key(&self, np: Pos, kp: Pos, x: &str, o: &Out) -> Res<u32> {
        let hardware = match self.store.seen(o) {
            Seen::Hw(_) => true,
            Seen::Agg(a) => !a.stored_ty().is_some_and(TyId::holds_handles),
            _ => false,
        };
        if hardware {
            return family_value(np, x);
        }
        self.check_static(kp, o)?;
        self.family_key(kp, self.store.value(o))
    }

    /// The key expression `k` of a family, evaluated in its structural context.
    pub(in crate::eval) fn key_out(&mut self, k: &Expr) -> Res<Out> {
        self.guarded(GuardKind::Key, |ev| {
            let o = ev.eval(k)?;
            need(k, o)
        })
    }

    /// The declaration of the entry `key` of the family named by `name`, at `pos` (section 6.2,
    /// entry order). The statement charged 1. The key evaluates in a structural context and is
    /// static (`S011`), then it gets its typed use. The type gets the checks of a scalar port,
    /// and then the entry must be new (`S019`). The entry is one whole port with the core name
    /// `<x>$<k>f`. The field keeps its name apart from every other name (section 7.2), so it
    /// takes no version.
    pub(in crate::eval) fn entry_decl(
        &mut self,
        pos: Pos,
        input: bool,
        name: &Ident,
        key: &Expr,
        ty: &TypeExpr,
    ) -> Res<()> {
        let o = self.key_out(key)?;
        self.check_static(key.pos(), &o)?;
        let k = self.family_key(key.pos(), self.store.value(&o))?;
        let tid = self.type_expr(ty)?;
        let t = self.data_type(pos, tid)?;
        let id = self.decl(name)?;
        if let Some((_, first)) = self.elab.entry(id, k) {
            let (line, col) = (first.line, first.col);
            return fail(
                Code::S019,
                pos,
                format!(
                    "the port `{}[{k}]` is declared here and at {line}:{col}; declare each key \
                     of `{}` once",
                    name.name, name.name
                ),
            );
        }
        let sym = self.sym(id);
        self.elab.work.body.ports.push(PortDecl {
            sym,
            key: Some(k),
            input,
            ty: t,
            tid,
            pos,
        });
        let outer = self.paths.child(None, sym);
        let path = self.paths.push(outer, Step::Family(k));
        let v = self.port_value(pos, input, path, tid, (sym, Some(k)))?;
        self.elab.work.entries.insert((id, k), (v, pos));
        Ok(())
    }

    /// The value of the entry `k` of the family `x` with the binder `id`, at the key `kp`. A key
    /// that the body did not declare before is `S013` "Undeclared family key".
    pub(in crate::eval) fn entry_val(&self, kp: Pos, x: &str, id: DeclId, k: u32) -> Res<Val> {
        match self.elab.entry(id, k) {
            Some((v, _)) => Ok(v.clone()),
            None => fail(
                Code::S013,
                kp,
                format!(
                    "the port family `{x}` has no key {k} here; declare `{x}[{k}]` before this use"
                ),
            ),
        }
    }

    /// The selection of the entry `k` of the own family `x` with the binder `id`, at the index
    /// node `pos` and the key `kp`. An input entry reads as a port name does, and an output
    /// entry gives its handle. The result refers to the port, so it charges no size, and it has
    /// no local root.
    fn entry_at(
        &mut self,
        pos: Pos,
        key_pos: Pos,
        (name, family): (&str, DeclId),
        key: u32,
    ) -> Res<Out> {
        match self.entry_val(key_pos, name, family, key)? {
            Val::Agg(agg) => match *agg {
                Agg::Ref(base, ty) => {
                    let named = !self.tys.meta(ty).leaves.is_zero();
                    let value = self.read_ref(pos, base, ty)?;
                    Ok(if named {
                        Out::Named(value)
                    } else {
                        Out::Made(value)
                    })
                }
                other => Ok(Out::Named(Val::Agg(Box::new(other)))),
            },
            value => Ok(Out::Named(value)),
        }
    }

    /// The selection `req[k]` at the index node `pos`, when `base` names an own family (section
    /// 5.6): `None` for another base. The index node charged 1, and the name node charges 1. The
    /// key evaluates in a structural context, gets the checks of a selection key, and selects the
    /// entry. A selection with more or fewer than one key is `S010` before the name charges.
    pub(in crate::eval) fn family_selection(
        &mut self,
        pos: Pos,
        base: &Expr,
        args: &[Expr],
    ) -> Res<Option<Out>> {
        let Expr::Name {
            pos: name_pos,
            id,
            name,
        } = base
        else {
            return Ok(None);
        };
        let Some(family) = self.family_of(*id) else {
            return Ok(None);
        };
        let [key] = args else {
            return fail(
                Code::S010,
                pos,
                "an index of a value has one argument".to_owned(),
            );
        };
        self.charge(*name_pos, 1)?;
        let out = self.key_out(key)?;
        let number = self.selection_key(*name_pos, key.pos(), name, &out)?;
        self.entry_at(pos, key.pos(), (name, family), number)
            .map(Some)
    }

    /// The port `port` of the child number `id` with the path `path`, at `pos`: an input gives
    /// its handle, and an output refers to it, unless it has no hardware leaf and is a new static
    /// value. An output entry has the field `<k>f` (section 7.2).
    pub(in crate::eval) fn port_out(
        &mut self,
        pos: Pos,
        (id, path): (usize, PathId),
        port: Port,
    ) -> Res<Out> {
        if port.input {
            return Ok(Out::Named(Val::Handle(Handle::Input {
                inst: id,
                path,
                port,
            })));
        }
        let mut name = self.paths.child(None, port.sym);
        if let Some(key) = port.key {
            name = self.paths.push(name, Step::Family(key));
        }
        let value = self.read_ref(pos, Base::Out(path, name), port.ty)?;
        Ok(if matches!(value, Val::Static(_)) {
            Out::Made(value)
        } else {
            Out::Named(value)
        })
    }

    /// The selection `u.f[k]` at the index node `p` of the family `f` of the child behind the
    /// base `b`, with the field node at `q` (section 6.2). The index node and the field node
    /// charged 1, and `u` evaluated once. The base is an `Instance` handle whose module has the
    /// family `f` (`child_family`). The key evaluates in a structural context, gets the checks of
    /// a selection key with `S010` at `q`, and selects the entry of the child. A key that the
    /// child did not declare is `S013` "Child family key".
    pub(in crate::eval) fn child_sel(
        &mut self,
        (p, q): (Pos, Pos),
        b: &Out,
        f: &Ident,
        key: &Expr,
    ) -> Res<Out> {
        let Seen::Handle(Handle::Inst { id, path, inst, ty }) = self.store.seen(b) else {
            return family_value(q, &f.name);
        };
        let (id, path, inst, ty) = (*id, *path, *inst, *ty);
        let out = self.key_out(key)?;
        let number = self.selection_key(q, key.pos(), &f.name, &out)?;
        let sym = self.port_sym(f).unwrap_or(0);
        match self.elab.port(inst, (sym, Some(number))) {
            Some(port) => self.port_out(p, (id, path), port),
            None => child_key(key.pos(), &self.tys.text(ty), &f.name, number),
        }
    }
}
