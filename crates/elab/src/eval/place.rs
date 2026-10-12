// SPDX-License-Identifier: Apache-2.0
//! The index, the selector `.N`, `len`, and the places of Lean `Source.Eval`. An index and a
//! selector refer to an element, so they charge no size and copy nothing: a binding of the
//! result is the copy. An assignment to a place updates the one element in the local, because
//! no other binding shares the container.

use super::{Evaluator, Frame, Opnd, Out, Res, Slot, expr_pos, fail, need, same_form};
use crate::Code;
use crate::hw::{Ref, Root, Seen, Val};
use crate::int::Int;
use crate::ops::int_text;
use crate::value::Value;
use parse::ast::{Expr, Nat, Pos};
use resolve::Target;
use std::borrow::Cow;

/// A step of a place after its root: an index at the position with its arguments, or a
/// selector `.N` with the positions of its node and of its number literal.
enum Sel<'a> {
    Index(Pos, &'a [Expr]),
    Select(Pos, Pos, &'a Nat),
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
            Value::Array(_, xs) | Value::Tuple(xs) => match xs.get_mut(k) {
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
        Value::Array(_, xs) | Value::Tuple(xs) => xs
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

    /// The number of the element that the static index `i` at `q` picks from `base`, a result
    /// of an index at `pos`. The checks come in this order: the container (`S010`), the type
    /// of the index (`S010`), then its range (`S013`).
    pub(super) fn pick_at(&self, pos: Pos, q: Pos, base: Seen<'_>, i: &Out) -> Res<usize> {
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
        let k = match self.store.value(i) {
            Value::Int(k) => Cow::Borrowed(k),
            Value::UInt(x) => Cow::Owned(Int::from_unsigned(x)),
            v => {
                return fail(
                    Code::S010,
                    q,
                    format!("an index is a static integer, not {}", v.text(&self.tys)),
                );
            }
        };
        match k.to_u64().and_then(|k| usize::try_from(k).ok()) {
            Some(k) if k < len => Ok(k),
            _ => fail(
                Code::S013,
                q,
                format!(
                    "the index {} is out of range for {len} element(s)",
                    int_text(&k)
                ),
            ),
        }
    }

    /// The index `i` at `q` of the operand `b` of an index at `pos`.
    pub(super) fn pick_index(&self, pos: Pos, q: Pos, b: &Opnd, i: &Out) -> Res<usize> {
        self.pick_at(pos, q, self.opnd_seen(b), i)
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

    /// The selector `.index` of the operand `b`.
    pub(super) fn select_index(&self, pos: Pos, q: Pos, index: &Nat, b: &Opnd) -> Res<usize> {
        self.select_at(pos, q, index, self.opnd_seen(b))
    }

    /// The index `x` of the value `base`, an expression at `pos`. The checks come in this
    /// order: the stage of the index (`S011`), the container (`S010`), the type of the index
    /// (`S010`), then its range (`S013`).
    pub(super) fn index_value(&mut self, pos: Pos, base: &Expr, args: &[Expr]) -> Res<Option<Out>> {
        let [x] = args else {
            return fail(
                Code::S010,
                pos,
                "an index of a value has one argument".to_owned(),
            );
        };
        let b = self.eval(base)?;
        let b = need(base, b)?;
        let b = self.data(pos, b)?;
        let i = self.eval(x)?;
        let i = need(x, i)?;
        let xp = expr_pos(x);
        self.check_static(xp, &i)?;
        let k = self.pick_index(pos, xp, &b, &i)?;
        Ok(Some(elem(b, k)))
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
    /// The target is a place, so it charges nothing. Only the index expressions of the place
    /// evaluate, from left to right, and each checks when it evaluates. Then the right side
    /// evaluates, with the type of the element as its type.
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
        let mut keys: Vec<usize> = Vec::with_capacity(steps.len());
        let mut ty = slot_ty;
        for step in &steps {
            let k = match *step {
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
                    self.check_static(expr_pos(i), &o)?;
                    self.pick_at(q, expr_pos(i), self.store.current(root, &keys), &o)?
                }
                Sel::Select(q, r, index) => {
                    self.select_at(q, r, index, self.store.current(root, &keys))?
                }
            };
            keys.push(k);
            ty = match ty {
                Some(t) => self.tys.part(t, k),
                None => self
                    .store
                    .current(root, &keys)
                    .ty(&self.graph, &mut self.tys),
            };
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
