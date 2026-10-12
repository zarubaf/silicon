// SPDX-License-Identifier: Apache-2.0
//! The lists of Lean `Source.Eval`: `list(T)`, `push`, and `pop`. `push` and `pop` change the
//! place of their list in place, with no copy of the list: the place resolves once
//! (`place_at`), and the change is one walk down its path. A value that `push` adds copies
//! only after its charge, and `pop` charges the element before it takes the element out.

use super::place::Held;
use super::{Evaluator, Opnd, Out, Res, at, expr_pos, fail, need};
use crate::Code;
use crate::hw::Val;
use crate::ops;
use crate::types::TyId;
use crate::value::Value;
use parse::ast::{Expr, Pos};

/// The element of a `push` after its typed use. A value that is already of the element type
/// stays where it is until its charge is paid.
enum Typed {
    Converted(Value),
    Same(Out),
}

impl Evaluator<'_> {
    /// A mutation at `pos` of a binding of the current frame (section 9.4). The binding is older
    /// than the innermost hardware arm when that arm started at the current depth: `S016`.
    pub(super) fn mutation(&self, pos: Pos) -> Res<()> {
        if self.arm == Some(self.depth) {
            return fail(
                Code::S016,
                pos,
                "a hardware arm changes a binding from before the arm".to_owned(),
            );
        }
        Ok(())
    }

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
        let list = Value::List(*elem, Vec::new());
        self.bounded(pos, list.depth())?;
        self.charge(pos, 1)?;
        Ok(Some(Out::Made(Val::Static(list))))
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
    pub(super) fn push(&mut self, pos: Pos, g: &str, xs: &[Expr]) -> Res<Option<Out>> {
        let [list, x] = xs else {
            return fail(
                Code::S007,
                pos,
                format!("`{g}` takes 2 argument(s), but it has {}", xs.len()),
            );
        };
        let place = self.place_at(expr_pos(list), Code::S008, list)?;
        let o = self.eval(x)?;
        let o = need(x, o)?;
        let Held::List { elem, .. } = place.held else {
            return self.not_a_list(pos, g, &place);
        };
        self.mutation(pos)?;
        let typed = self.typed_element(pos, expr_pos(x), elem, o)?;
        let (depth, size) = match &typed {
            Typed::Converted(v) => (v.depth(), v.size()),
            Typed::Same(o) => {
                let v = self.store.value(o);
                (v.depth(), v.size())
            }
        };
        self.bounded(pos, place.keys.len() as u64 + 1 + depth)?;
        self.charge(pos, u128::from(size))?;
        let w = match typed {
            Typed::Converted(v) => v,
            Typed::Same(o) => self.static_value(pos, o)?,
        };
        if let Some(Value::List(_, ys)) = self.store.part_mut(place.root, &place.keys) {
            ys.push(w);
        }
        Ok(Some(Out::Made(Val::Static(Value::Unit))))
    }

    /// The typed use of the result `o` at the element type `elem` of a list. A hardware value is
    /// `S011` at `xp`. A static value of another type converts and charges, and a static value
    /// of the type stays a reference.
    fn typed_element(&mut self, pos: Pos, xp: Pos, elem: TyId, o: Out) -> Res<Typed> {
        let o = self.settle(pos, elem, o)?;
        let Opnd::Static(o) = self.data(xp, o)? else {
            return fail(Code::S011, xp, "a list holds no hardware value".to_owned());
        };
        self.check_static(pos, &o)?;
        match ops::convert(elem, self.store.value(&o), &mut self.fuel, &self.tys)
            .map_err(at(pos))?
        {
            Some(v) => Ok(Typed::Converted(v)),
            None => Ok(Typed::Same(o)),
        }
    }

    /// `pop(xs)` at the call `pos`. The place of `xs` resolves first. It must hold a list
    /// (`S010`) that is not empty (`S013`), and the mutation rule holds (`S016`). The charge is
    /// the size of the last element, and then the element leaves the list, in one walk down the
    /// path.
    pub(super) fn pop(&mut self, pos: Pos, g: &str, xs: &[Expr]) -> Res<Option<Out>> {
        let [list] = xs else {
            return fail(
                Code::S007,
                pos,
                format!("`{g}` takes 1 argument(s), but it has {}", xs.len()),
            );
        };
        let place = self.place_at(expr_pos(list), Code::S008, list)?;
        let Held::List { len, .. } = place.held else {
            return self.not_a_list(pos, g, &place);
        };
        if len == 0 {
            return fail(Code::S013, pos, "`pop` of an empty list".to_owned());
        }
        self.mutation(pos)?;
        let Evaluator { store, fuel, .. } = self;
        let Some(Value::List(_, ys)) = store.part_mut(place.root, &place.keys) else {
            return self.not_a_list(pos, g, &place);
        };
        let size = ys.last().map_or(0, Value::size);
        fuel.pay(u128::from(size)).map_err(at(pos))?;
        let w = ys.pop().unwrap_or(Value::Unit);
        Ok(Some(Out::Made(Val::Static(w))))
    }
}
