// SPDX-License-Identifier: Apache-2.0
//! The index, the selector `.N`, `len`, and the places of Lean `Source.Eval`. An index and a
//! selector refer to an element, so they charge no size and copy nothing: a binding of the
//! result is the copy. An assignment to a place updates the one element in the local, because
//! no other binding shares the container. A read and a place each walk their path once.

use super::{Evaluator, Frame, Opnd, Out, Res, Slot, expr_pos, fail, need, same_form};
use crate::Code;
use crate::hw::{Ref, Root, Seen, Val};
use crate::int::Int;
use crate::ops::int_text;
use crate::types::TyId;
use crate::value::Value;
use parse::ast::{Expr, Ident, Nat, Pos};
use resolve::Target;
use std::borrow::Cow;

/// A step of a place or a read after its root: an index at the position with its arguments,
/// a selector `.N` with the positions of its node and of its number literal, or a field `.f`.
#[derive(Clone, Copy)]
enum Sel<'a> {
    Index(Pos, &'a [Expr]),
    Select(Pos, Pos, &'a Nat),
    Field(Pos, &'a Ident),
}

impl Sel<'_> {
    /// The position of the node of the step, where the step charges.
    fn pos(&self) -> Pos {
        let (Sel::Index(q, _) | Sel::Select(q, ..) | Sel::Field(q, _)) = *self;
        q
    }
}

/// A step of a place whose index evaluated: an index at its node, with the position of its
/// index expression and the index, or a selector `.N` as in `Sel`.
enum Key<'a> {
    Index(Pos, Pos, Index),
    Select(Pos, Pos, &'a Nat),
    Field(Pos, &'a Ident),
}

/// What the walk along a place knows of the type of the part: its type, no type, or the type
/// of the element itself, which it finds at the end.
#[derive(Clone, Copy)]
enum Known {
    Ty(TyId),
    Absent,
    Element,
}

/// A static index, read once when it evaluates: its number, the text of an integer that no
/// `usize` holds, or the message of a value that is not an integer. A step checks it later
/// without the value of the index.
pub(super) enum Index {
    Number(usize),
    Wide(String),
    Bad(String),
}

/// An index of a type, which is complete: `S007` at the index.
fn fail_type_index<T>(q: Pos) -> Res<T> {
    fail(Code::S007, q, "a complete type takes no index".to_owned())
}

/// The root of a place and its steps from the root outward. Another target has no place.
fn chain(e: &Expr) -> Option<(&Expr, Vec<Sel<'_>>)> {
    let mut steps = Vec::new();
    let mut cur = e;
    loop {
        match cur {
            Expr::Index { pos, base, args } => {
                steps.push(Sel::Index(*pos, args));
                cur = base;
            }
            Expr::Select {
                pos,
                base,
                lit_pos,
                index,
            } => {
                steps.push(Sel::Select(*pos, *lit_pos, index));
                cur = base;
            }
            Expr::Field { pos, base, field } => {
                steps.push(Sel::Field(*pos, field));
                cur = base;
            }
            Expr::Name { .. } => {
                steps.reverse();
                return Some((cur, steps));
            }
            _ => return None,
        }
    }
}

/// The container `v` with the element at the numbers `keys` replaced by `w`. No other binding
/// shares the container, so the update is in place.
fn replace(v: &mut Value, keys: &[usize], w: Value) {
    let mut cur = v;
    for &k in keys {
        cur = match cur {
            Value::Array(_, xs) | Value::Tuple(xs) | Value::Record(_, xs) => match xs.get_mut(k) {
                Some(x) => x,
                None => return,
            },
            _ => return,
        };
    }
    *cur = w;
}

/// The element `k` of the container `b`, as a reference to it. An index or a selector refers
/// to an element, so a binding of the result is a copy.
pub(super) fn elem(b: Opnd, k: usize) -> Out {
    match b {
        Opnd::Static(Out::Ref(Ref { root, mut path })) => {
            path.push(k);
            Out::Ref(Ref { root, path })
        }
        Opnd::Static(Out::Made(Val::Static(mut v)) | Out::Named(Val::Static(mut v))) => {
            Out::Named(Val::Static(take_element(&mut v, k)))
        }
        Opnd::Static(o) => o,
        Opnd::Hw(h) => Out::Made(Val::Hw(h)),
    }
}

/// The element `k` of an owned container.
fn take_element(v: &mut Value, k: usize) -> Value {
    match v {
        Value::Array(_, xs) | Value::Tuple(xs) | Value::Record(_, xs) => xs
            .get_mut(k)
            .map_or(Value::Unit, |x| std::mem::replace(x, Value::Unit)),
        _ => Value::Unit,
    }
}

impl Evaluator<'_> {
    /// What an operand is.
    fn opnd_seen<'s>(&'s self, b: &'s Opnd) -> Seen<'s> {
        match b {
            Opnd::Static(o) => self.store.seen(o),
            Opnd::Hw(h) => Seen::Hw(*h),
        }
    }

    /// The static index `i`, read once. An index that is not an integer keeps its message.
    pub(super) fn index_of(&self, i: &Out) -> Index {
        let k = match self.store.value(i) {
            Value::Int(k) => Cow::Borrowed(k),
            Value::UInt(x) => Cow::Owned(Int::from_unsigned(x)),
            v => {
                return Index::Bad(format!(
                    "an index is a static integer, not {}",
                    v.text(&self.tys)
                ));
            }
        };
        match k.to_u64().and_then(|k| usize::try_from(k).ok()) {
            Some(k) => Index::Number(k),
            None => Index::Wide(int_text(&k)),
        }
    }

    /// The number of the element that the static index `i` at `q` picks from `base`, a result
    /// of an index at `pos`. The checks come in this order: the container (`S010`), the type
    /// of the index (`S010`), then its range (`S013`).
    pub(super) fn pick_at(&self, pos: Pos, q: Pos, base: Seen<'_>, i: &Index) -> Res<usize> {
        let len = match base {
            Seen::Static(Value::Array(_, xs) | Value::Tuple(xs)) => xs.len(),
            s => {
                return fail(
                    Code::S010,
                    pos,
                    format!("an index needs an array or a tuple, not {}", self.text(s)),
                );
            }
        };
        let range = |k: &str| {
            fail(
                Code::S013,
                q,
                format!("the index {k} is out of range for {len} element(s)"),
            )
        };
        match i {
            Index::Number(k) if *k < len => Ok(*k),
            Index::Number(k) => range(&k.to_string()),
            Index::Wide(k) => range(k),
            Index::Bad(m) => fail(Code::S010, q, m.clone()),
        }
    }

    /// The number of the element that the selector `.index` with its literal at `q` picks
    /// from `base`, a result of a selector at `pos`.
    fn select_at(&self, pos: Pos, q: Pos, index: &Nat, base: Seen<'_>) -> Res<usize> {
        let (len, v) = match base {
            Seen::Static(v @ Value::Tuple(xs)) => (xs.len(), v),
            s => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "the selector `.{}` needs a tuple, not {}",
                        selector_text(index),
                        self.text(s)
                    ),
                );
            }
        };
        match index.as_str().parse::<usize>() {
            Ok(k) if k < len => Ok(k),
            _ => fail(
                Code::S013,
                q,
                format!(
                    "the selector {} is out of range for {}",
                    selector_text(index),
                    v.text(&self.tys)
                ),
            ),
        }
    }

    /// The step of a read at `e` and its base: an index of a value or a selector `.N`.
    /// Another expression, also an index of a type, is the root of the read.
    fn read_step<'e>(&self, e: &'e Expr) -> Option<(Sel<'e>, &'e Expr)> {
        match e {
            Expr::Index { pos, base, args } => {
                let ty = match &**base {
                    Expr::Name { id, .. } => {
                        matches!(self.target(*id), Some(Target::Prelude(k)) if k.is_type())
                            || self.struct_item(*id).is_some()
                    }
                    _ => false,
                };
                (!ty).then_some((Sel::Index(*pos, args), &**base))
            }
            Expr::Select {
                pos,
                base,
                lit_pos,
                index,
            } => Some((Sel::Select(*pos, *lit_pos, index), &**base)),
            _ => None,
        }
    }

    /// A read `e` through indices and selectors `.N`, whose node charged. Each node charges
    /// before its base evaluates, from the outside in, and an index with more than one
    /// argument fails before its base. Then the root evaluates, and each step from the root
    /// outward reads its base as data and evaluates its index.
    ///
    /// Lean checks the container and the index of each step before the next index evaluates.
    /// Here the checks run in one walk along the path after the indices, so no step walks
    /// again from the root. A failed check comes before an error of a later index, so the
    /// first error is that of Lean. Only a static container has elements, so each base after
    /// the first is static data.
    pub(super) fn read(&mut self, e: &Expr) -> Res<Option<Out>> {
        let mut steps = Vec::new();
        let mut next = self.read_step(e);
        let mut root = e;
        while let Some((step, base)) = next {
            if let Sel::Index(q, args) = step
                && args.len() != 1
            {
                return fail(
                    Code::S010,
                    q,
                    "an index of a value has one argument".to_owned(),
                );
            }
            steps.push(step);
            next = self.read_step(base);
            if next.is_some() {
                self.charge(expr_pos(base), 1)?;
            }
            root = base;
        }
        steps.reverse();
        let first = match steps.first() {
            Some(step) => step.pos(),
            None => {
                return fail(
                    Code::S010,
                    expr_pos(e),
                    "not a read of an element".to_owned(),
                );
            }
        };
        let b = self.eval(root)?;
        let b = need(root, b)?;
        let b = self.data(first, b)?;
        if let Some(Sel::Index(q, _)) = steps.first()
            && matches!(self.opnd_seen(&b), Seen::Static(Value::Type(_)))
        {
            return fail_type_index(*q);
        }
        let mut keyed = Vec::with_capacity(steps.len());
        let mut stop = None;
        for step in &steps {
            match self.key(step) {
                Ok(k) => keyed.push(k),
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            }
        }
        let mut keys = Vec::with_capacity(keyed.len());
        let mut cur = self.opnd_seen(&b);
        for key in &keyed {
            let k = match key {
                Key::Index(q, ..) if matches!(cur, Seen::Static(Value::Type(_))) => {
                    return fail_type_index(*q);
                }
                Key::Index(q, xp, i) => self.pick_at(*q, *xp, cur, i)?,
                Key::Select(q, r, index) => self.select_at(*q, *r, index, cur)?,
                Key::Field(q, f) => self.field_at(*q, f, cur)?.0,
            };
            cur = self.store.step(cur, k);
            keys.push(k);
        }
        if let Some(e) = stop {
            // The base of the step whose index failed is a type: that check comes first.
            if let Some(Sel::Index(q, _)) = steps.get(keyed.len())
                && matches!(cur, Seen::Static(Value::Type(_)))
            {
                return fail_type_index(*q);
            }
            return Err(e);
        }
        let Some((&k, rest)) = keys.split_first() else {
            return fail(
                Code::S010,
                expr_pos(e),
                "not a read of an element".to_owned(),
            );
        };
        let mut out = elem(b, k);
        for &k in rest {
            out = elem(Opnd::Static(out), k);
        }
        Ok(Some(out))
    }

    /// `len` of an array at the call `pos`. It refers to the array, so it charges no size.
    pub(super) fn len(&mut self, pos: Pos, mut vs: Vec<Out>) -> Res<Option<Out>> {
        let (Some(v), true) = (vs.pop(), vs.is_empty()) else {
            return fail(
                Code::S007,
                pos,
                format!("`len` takes 1 argument(s), but it has {}", vs.len() + 1),
            );
        };
        let n = match self.data(pos, v)? {
            Opnd::Static(o) => match self.store.value(&o) {
                Value::Array(_, xs) => xs.len() as u64,
                v => {
                    return fail(
                        Code::S010,
                        pos,
                        format!("`len` takes an array, not {}", v.text(&self.tys)),
                    );
                }
            },
            Opnd::Hw(h) => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "`len` takes an array, not hardware {}",
                        self.tys.text_of(&self.graph.ty(h))
                    ),
                );
            }
        };
        Ok(Some(Out::Made(Val::Static(Value::Int(Int::from_u64(n))))))
    }

    /// An assignment to a `let mut` local, or to a part of it by indices and selectors `.N`.
    /// The root name charges nothing. Each step charges 1 at its node, then its index
    /// evaluates, from the root outward. Then the right side evaluates, with the type of the
    /// element as its type.
    ///
    /// Lean checks the container and the index of each step before the next step charges.
    /// Here the checks run in one walk along the path after the indices, so no step walks
    /// again from the root. `S008` keeps the root unchanged while the indices evaluate, and
    /// a failed check comes before an error of a later step. Thus the first error is that of
    /// Lean.
    pub(super) fn assign(&mut self, pos: Pos, target: &Expr, value: &Expr) -> Res<Option<Val>> {
        let bad = || {
            fail(
                Code::S010,
                pos,
                "an assignment target is a `let mut` local".to_owned(),
            )
        };
        let Some((Expr::Name { id: root_id, .. }, steps)) = chain(target) else {
            return bad();
        };
        let place = match self.target(*root_id) {
            Some(Target::Decl(id)) => self
                .store
                .frame()
                .and_then(|f: &Frame| f.get(&id))
                .filter(|s| s.mutable)
                .map(|s| (id, s.ty)),
            _ => None,
        };
        let Some((id, slot_ty)) = place else {
            return bad();
        };
        let frame = self.store.frames.len().saturating_sub(1);
        let root = Root::Local(frame, id);
        let mut keyed = Vec::with_capacity(steps.len());
        let mut stop = None;
        for step in &steps {
            match self.charge(step.pos(), 1).and_then(|()| self.key(step)) {
                Ok(k) => keyed.push(k),
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            }
        }
        let (keys, ty) = self.walk(root, slot_ty, &keyed)?;
        if let Some(e) = stop {
            return Err(e);
        }
        let o = self.eval(value)?;
        let o = need(value, o)?;
        self.copy(pos, &o)?;
        let y = if let Some(t) = ty {
            self.conform_val(pos, t, o)?
        } else {
            let old = self.store.current(root, &keys);
            let new = self.store.seen(&o);
            if !same_form(old, new) {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "expected {}, but the value is {}",
                        self.text(old),
                        self.text(new)
                    ),
                );
            }
            self.store.take(o)
        };
        if keys.is_empty() {
            let y = self.named(pos, id, y);
            if let Some(slot) = self.store.frame_mut().and_then(|f| f.get_mut(&id)) {
                slot.value = y;
            }
            return Ok(None);
        }
        let w = self.item(expr_pos(value), y)?;
        if let Some(Slot {
            value: Val::Static(r),
            ..
        }) = self.store.frame_mut().and_then(|f| f.get_mut(&id))
        {
            replace(r, &keys, w);
        }
        Ok(None)
    }

    /// The step `step` of a place or a read with its index, which gets its static check.
    fn key<'a>(&mut self, step: &Sel<'a>) -> Res<Key<'a>> {
        match *step {
            Sel::Index(q, args) => {
                let [i] = args else {
                    return fail(
                        Code::S010,
                        q,
                        "an index of a value has one argument".to_owned(),
                    );
                };
                let o = self.eval(i)?;
                let o = need(i, o)?;
                let xp = expr_pos(i);
                self.check_static(xp, &o)?;
                Ok(Key::Index(q, xp, self.index_of(&o)))
            }
            Sel::Select(q, r, index) => Ok(Key::Select(q, r, index)),
            Sel::Field(q, f) => Ok(Key::Field(q, f)),
        }
    }

    /// The numbers of the steps `keyed` of the local at `root`, and the type of the part, in
    /// one walk from the root outward. `ty` is the type of the local, if it has one.
    ///
    /// Lean takes the part of the type at each step, and the type of the element when it has
    /// no type. The type of a tuple is the tuple of the types of its elements, so below a
    /// step without a type the type stays that of the element until an array gives its
    /// element type. Thus the walk finds the type of a tuple element only once, at the end,
    /// and not at each step.
    fn walk(
        &mut self,
        root: Root,
        ty: Option<TyId>,
        keyed: &[Key<'_>],
    ) -> Res<(Vec<usize>, Option<TyId>)> {
        let mut keys = Vec::with_capacity(keyed.len());
        let mut cur = self.store.current(root, &[]);
        let mut known = match ty {
            Some(t) => Known::Ty(t),
            None => Known::Absent,
        };
        for key in keyed {
            let (k, field) = match key {
                Key::Index(q, xp, i) => (self.pick_at(*q, *xp, cur, i)?, None),
                Key::Select(q, r, index) => (self.select_at(*q, *r, index, cur)?, None),
                Key::Field(q, f) => {
                    let (k, ft) = self.field_at(*q, f, cur)?;
                    (k, Some(ft))
                }
            };
            known = match (field, known, cur) {
                (Some(ft), _, _) => Known::Ty(ft),
                (None, Known::Ty(t), _) => self.tys.part(t, k).map_or(Known::Absent, Known::Ty),
                (None, Known::Element, Seen::Static(Value::Array(elem, _))) => Known::Ty(*elem),
                (None, Known::Absent | Known::Element, _) => Known::Element,
            };
            cur = self.store.step(cur, k);
            keys.push(k);
        }
        let ty = match known {
            Known::Ty(t) => Some(t),
            Known::Absent => None,
            Known::Element => cur.ty(&self.graph, &mut self.tys),
        };
        Ok((keys, ty))
    }

    /// The value of an element of a container in this phase. A hardware value is `S010`,
    /// and so is a handle until slice 3.
    fn item(&self, pos: Pos, v: Val) -> Res<Value> {
        match v {
            Val::Static(v) => Ok(v),
            Val::Hw(_) => fail(
                Code::S010,
                pos,
                "a container holds only static values in this phase".to_owned(),
            ),
            Val::Handle(h) => {
                let v = Val::Handle(h);
                fail(
                    Code::S010,
                    pos,
                    format!("{} is not an element before slice 3", self.text(v.seen())),
                )
            }
            Val::Pending(q, _) => super::no_type(q),
        }
    }
}

/// A selector in a message, with at most 256 bits of a large number.
fn selector_text(index: &Nat) -> String {
    Int::from_decimal(index.as_str()).map_or_else(|| index.as_str().to_owned(), |n| int_text(&n))
}
