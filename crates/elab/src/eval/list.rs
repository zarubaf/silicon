// SPDX-License-Identifier: Apache-2.0
//! The lists of Lean `Source.Eval`: `list(T)`, `push`, and `pop`. `push` and `pop` change the
//! place of their list in place, with no copy of the list: the place resolves once
//! (`place_at`), and the change is one walk down its path. A value that `push` adds copies
//! only after its charge, and `pop` charges the element before it takes the element out.

use super::agg::{Delta, ListMut};
use super::place::Held;
use super::typed::Element;
use super::{Evaluator, Opnd, Out, Res, at, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Seen, Val};
use crate::limit;
use crate::ops;
use crate::types::TyId;
use crate::value::Value;
use parse::ast::{Expr, Pos};

/// The element of a `push` after its typed use. A value that is already of the element type
/// stays where it is until its charge is paid.
pub(super) enum Typed {
    Converted(Agg),
    Same(Out),
}

impl Evaluator<'_> {
    /// `list(T)` at the call `pos`: an empty list of `T`. It checks its depth and charges 1.
    pub(super) fn list_new(&mut self, pos: Pos, g: &str, t: &Out) -> Res<Option<Out>> {
        self.check_static(pos, t)?;
        let Value::Type(elem) = self.store.value(t) else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{g}` needs a type, not {}",
                    self.store.value(t).text(&self.tys)
                ),
            );
        };
        let elem = *elem;
        let list = Value::List(elem, Vec::new());
        self.bounded(pos, list.depth())?;
        self.charge(pos, 1)?;
        // An element type with the handle flag gives an empty list node (section 5.1).
        let list_ty = self.tys.list(elem);
        Ok(Some(Out::Made(
            Agg::typed(&mut self.tys, list_ty, list).into_val(),
        )))
    }

    /// The part of the place is not a list: `S010` at `pos`.
    fn not_a_list<T>(&self, pos: Pos, g: &str, place: &super::place::Place) -> Res<T> {
        let part = self.store.current(place.root, &place.keys);
        fail(
            Code::S010,
            pos,
            format!("`{g}` needs a list, not {}", self.text(part)),
        )
    }

    /// `push(xs, x)` at the call `pos`. The place of `xs` resolves first, then `x` evaluates.
    /// The place must hold a list (`S010`), and the mutation rule holds (`S016`). The typed use
    /// of `x` at the element type comes next, and a hardware element is `S011`. The new depth of
    /// the root comes from the element and the steps of the place (`S015`): the root is within
    /// the nesting depth, so only the element on the path can raise it, and no walk enters the
    /// list. The charge is the size of the element, before the element copies into the list.
    pub(super) fn push(&mut self, pos: Pos, g: &str, xs: &[&Expr]) -> Res<Option<Out>> {
        let [list, item] = xs else {
            return fail(
                Code::S007,
                pos,
                format!("`{g}` takes 2 argument(s), but it has {}", xs.len()),
            );
        };
        let place = self.place_at(list.pos(), Code::S008, list)?;
        let arg = self.eval(item)?;
        let arg = need(item, arg)?;
        self.store.shut_window(place.root);
        let Held::List { elem, len } = place.held else {
            return self.not_a_list(pos, g, &place);
        };
        self.mutation(pos, place.id)?;
        let typed = self.typed_use(pos, elem, false, arg, Element(item.pos()))?;
        let (depth, size) = self.typed_dims(&typed);
        self.bounded(pos, place.keys.len() as u64 + 1 + depth)?;
        limit::list(len as u128 + 1).map_err(at(pos))?;
        self.charge(pos, u128::from(size))?;
        let part = self.element_part(pos, typed)?;
        self.charge_refresh(pos, &place)?;
        self.charge_held(pos, place.root)?;
        let delta = Delta::Grow {
            size,
            depth: 1 + depth,
        };
        let before = self.store.before_list_edit(place.root, &place.keys, len);
        let pushed = if matches!(self.store.root(&place.root), Val::Agg(_)) {
            let push = |list: ListMut<'_>| match (list, part) {
                (ListMut::Static(ys), Agg::Static(value)) => {
                    ys.push(value);
                    true
                }
                (ListMut::Node(parts), part) => {
                    parts.push(part);
                    true
                }
                (ListMut::Static(_), _) => false,
            };
            self.edit_list(pos, &place, Some(delta), push)?
        } else if let Agg::Static(value) = part {
            self.store.push_static(place.root, &place.keys, value);
            Some(true)
        } else {
            Some(false)
        };
        if pushed != Some(true) {
            return fail(
                Code::S011,
                item.pos(),
                "a list holds no hardware value".to_owned(),
            );
        }
        self.store.log_push(before);
        Ok(Some(Out::Made(Val::Static(Value::Unit))))
    }

    /// The depth and the size of the typed element of a `push`, from the stored numbers.
    fn typed_dims(&self, typed: &Typed) -> (u64, u64) {
        match typed {
            Typed::Converted(a) => (a.depth(&self.tys), a.size(&self.graph, &self.tys)),
            Typed::Same(o) => {
                let s = self.store.seen(o);
                let depth = match s {
                    Seen::Static(v) => v.depth(),
                    Seen::Agg(a) => a.depth(&self.tys),
                    _ => 1,
                };
                (depth, u64::try_from(self.seen_size(s)).unwrap_or(u64::MAX))
            }
        }
    }

    /// The part that the typed element is. A result that stayed where it was copies now: the
    /// charge of the element came before.
    fn element_part(&self, pos: Pos, typed: Typed) -> Res<Agg> {
        match typed {
            Typed::Converted(a) => Ok(a),
            Typed::Same(o) => match Agg::of_val(self.store.take(o)) {
                Ok(a) => Ok(a),
                Err(_) => fail(Code::S010, pos, "the element has no part".to_owned()),
            },
        }
    }

    /// Whether the result has a hardware leaf (Lean `Val.hasHw`).
    fn out_has_hw(&self, o: &Out) -> bool {
        match self.store.seen(o) {
            Seen::Hw(_) => true,
            Seen::Agg(a) => a.leaves(&self.tys) > 0,
            _ => false,
        }
    }

    /// The typed use of the result `o` at the element type `elem` of a list (Lean `siteUse` at an
    /// element). A value with a hardware leaf is `S011` at `xp`, also after a read. A handle type
    /// keeps the handle. A value of another type reads (`data_at`), and a static value converts.
    /// A node of the type stays where it is, and another node converts part by part.
    pub(super) fn typed_element(&mut self, pos: Pos, xp: Pos, elem: TyId, o: Out) -> Res<Typed> {
        let hardware = || fail(Code::S011, xp, "a list holds no hardware value".to_owned());
        if self.out_has_hw(&o) {
            return hardware();
        }
        if self.tys.get(elem).is_handle() {
            return Ok(Typed::Converted(Agg::Handle(
                self.handle_leaf(pos, elem, &o)?,
            )));
        }
        let o = self.settle(pos, elem, o)?;
        let Opnd::Static(o) = self.data_at(xp, elem, o)? else {
            return hardware();
        };
        if self.out_has_hw(&o) {
            return hardware();
        }
        match self.store.seen(&o) {
            Seen::Handle(_) => self.handle_wrong(pos, elem, self.store.seen(&o)),
            Seen::Agg(a) if a.stored_ty() == Some(elem) => Ok(Typed::Same(o)),
            Seen::Agg(_) => Ok(Typed::Converted(self.typed_agg(pos, elem, o)?)),
            Seen::Static(_) => {
                self.check_static(pos, &o)?;
                match ops::convert(elem, self.store.value(&o), &mut self.fuel, &self.tys)
                    .map_err(at(pos))?
                {
                    Some(v) => Ok(Typed::Converted(Agg::typed(&mut self.tys, elem, v))),
                    None => Ok(Typed::Same(o)),
                }
            }
            s => fail(
                Code::S010,
                xp,
                format!("{} is not an element of a list", self.text(s)),
            ),
        }
    }

    /// `pop(xs)` at the call `pos`. The place of `xs` resolves first. It must hold a list
    /// (`S010`) that is not empty (`S013`), and the mutation rule holds (`S016`). The charge is
    /// the size of the last element, and then the element leaves the list, in one walk down the
    /// path.
    pub(super) fn pop(&mut self, pos: Pos, g: &str, xs: &[&Expr]) -> Res<Option<Out>> {
        let [list] = xs else {
            return fail(
                Code::S007,
                pos,
                format!("`{g}` takes 1 argument(s), but it has {}", xs.len()),
            );
        };
        let place = self.place_at(list.pos(), Code::S008, list)?;
        self.store.shut_window(place.root);
        let Held::List { elem, len } = place.held else {
            return self.not_a_list(pos, g, &place);
        };
        if len == 0 {
            return fail(Code::S013, pos, "`pop` of an empty list".to_owned());
        }
        self.mutation(pos, place.id)?;
        if self.store.is_held(place.root) || matches!(self.store.root(&place.root), Val::Agg(_)) {
            // The copies of the parked references come before the change, after both charges.
            // The read of the element walks the path once more, and the size of the root pays
            // for it.
            let (size, last_depth) = self.last_of(&place);
            self.charge(pos, u128::from(size))?;
            // An element deeper than the element type can lower the depth of the list. Then the
            // change charges the root and builds each node on the path again.
            let deep = last_depth > elem.depth();
            self.charge_refresh(pos, &place)?;
            if deep {
                self.charge_root(pos, &place)?;
            }
            self.charge_held(pos, place.root)?;
            let delta = (!deep).then_some(Delta::Shrink { size });
            let before = self.store.before_list_edit(place.root, &place.keys, len);
            let popped = if matches!(self.store.root(&place.root), Val::Agg(_)) {
                self.edit_list(pos, &place, delta, |list| match list {
                    ListMut::Static(ys) => ys.pop().map(Agg::Static),
                    ListMut::Node(xs) => xs.pop(),
                })?
                .flatten()
            } else {
                self.store
                    .pop_static(place.root, &place.keys)
                    .map(Agg::Static)
            };
            let Some(w) = popped else {
                return self.not_a_list(pos, g, &place);
            };
            self.store.log_pop(before, &w);
            return Ok(Some(Out::Made(w.into_val())));
        }
        let Evaluator { store, fuel, .. } = self;
        let Some(popped) = store.pop_paying(place.root, &place.keys, fuel) else {
            return self.not_a_list(pos, g, &place);
        };
        let w = popped.map_err(at(pos))?;
        Ok(Some(Out::Made(Val::Static(w))))
    }

    /// The size and the depth of the last element of the list at the place, from the stored
    /// numbers. An empty or absent list gives 0.
    fn last_of(&self, place: &super::place::Place) -> (u64, u64) {
        match self.store.current(place.root, &place.keys) {
            Seen::Static(Value::List(_, ys)) => ys.last().map_or((0, 0), |w| (w.size(), w.depth())),
            Seen::Agg(Agg::List(_, p)) => p.0.last().map_or((0, 0), |w| {
                (w.size(&self.graph, &self.tys), w.depth(&self.tys))
            }),
            _ => (0, 0),
        }
    }
}
