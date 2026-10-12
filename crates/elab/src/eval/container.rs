// SPDX-License-Identifier: Apache-2.0
//! The static containers of Lean `Source.Eval`: the tuple and array literals, the literals that
//! wait for the type of a typed use, and the new containers with their depth bound.
//!
//! A new container checks its depth, then pays the charge of its size, and only then copies
//! its elements. The elements stay borrowed until then, so a reference to a large value costs
//! nothing before the charge.

use super::{Evaluator, Out, Res, Store, at, fail, need};
use crate::Code;
use crate::hw::{Part, Seen, Val};
use crate::ops::{self, Fuel};
use crate::value::{Ty, TyId, Types, Value};
use parse::ast::{Expr, Pos, TypeExpr};
use std::borrow::Cow;
use std::cmp::Ordering;

/// What the construction of a container reads: the store that its references name, and the
/// nesting depth.
#[derive(Clone, Copy)]
struct Env<'x> {
    store: &'x Store,
    limit: u64,
}

/// A new value or type of the depth `depth` at `pos`. Above the nesting depth, it is `S015`.
pub(super) fn bounded(limit: u64, pos: Pos, depth: u64) -> Res<()> {
    if limit < depth {
        return fail(
            Code::S015,
            pos,
            format!("the depth {depth} goes above the nesting depth {limit}"),
        );
    }
    Ok(())
}

/// The static value of a result that is an element of a container.
fn cow(store: &Store, out: Out) -> Cow<'_, Value> {
    match out {
        Out::Made(Val::Static(v)) | Out::Named(Val::Static(v)) => Cow::Owned(v),
        Out::Ref(r) => Cow::Borrowed(store.value_at(&r)),
        Out::Made(_) | Out::Named(_) => Cow::Owned(Value::Unit),
    }
}

/// A tuple literal at `pos`: its depth, then the charge of its size.
fn tuple_of(env: Env<'_>, fuel: &mut Fuel, pos: Pos, elems: Vec<Cow<'_, Value>>) -> Res<Value> {
    let depth = 1 + elems.iter().map(|e| e.depth()).max().unwrap_or(0);
    bounded(env.limit, pos, depth)?;
    let size = 1 + elems.iter().map(|e| u128::from(e.size())).sum::<u128>();
    fuel.pay(size).map_err(at(pos))?;
    Ok(Value::Tuple(
        elems.into_iter().map(Cow::into_owned).collect(),
    ))
}

/// An array literal at `pos`. Its elements take their common type. Then it checks its depth
/// and charges its size.
fn array_of<'x>(
    env: Env<'x>,
    fuel: &mut Fuel,
    tys: &mut Types,
    pos: Pos,
    elems: Vec<Cow<'x, Value>>,
) -> Res<Value> {
    let Some(t) = ops::common_of(elems.iter().map(|e| &**e), tys) else {
        return fail(
            Code::S010,
            pos,
            "the elements of an array have no common type".to_owned(),
        );
    };
    let mut xs = Vec::with_capacity(elems.len());
    for e in elems {
        xs.push(match ops::convert(t, &e, fuel, tys).map_err(at(pos))? {
            Some(v) => Cow::Owned(v),
            None => e,
        });
    }
    let depth = 1 + xs.iter().map(|x| x.depth()).fold(t.depth(), u64::max);
    bounded(env.limit, pos, depth)?;
    let size = 1 + xs.iter().map(|x| u128::from(x.size())).sum::<u128>();
    fuel.pay(size).map_err(at(pos))?;
    Ok(Value::Array(
        t,
        xs.into_iter().map(Cow::into_owned).collect(),
    ))
}

fn mismatch<T>(pos: Pos, t: TyId, what: &str, tys: &Types) -> Res<T> {
    fail(
        Code::S010,
        pos,
        format!("expected {}, but the value is {what}", tys.text(t)),
    )
}

/// A literal that waits, at a typed use of the type `t` at `pos`. The type flows into each
/// element: `[]` takes the type `[T; 0]`, and a literal of the shape of `t` makes its elements
/// at the element types of `t`. Then the literal charges as it does at its node. Another shape
/// is `S010` at `pos`.
fn build<'x>(
    env: Env<'x>,
    fuel: &mut Fuel,
    tys: &mut Types,
    pos: Pos,
    ty: TyId,
    part: &'x Part,
) -> Res<Cow<'x, Value>> {
    match part {
        Part::Value(leaf) => Ok(Cow::Borrowed(env.store.leaf(leaf))),
        Part::Empty(node) => match tys.get(ty) {
            Ty::Array(elem, len) if len.cmp_u64(0) == Ordering::Equal => {
                let empty = Value::Array(*elem, Vec::new());
                bounded(env.limit, *node, empty.depth())?;
                Ok(Cow::Owned(empty))
            }
            _ => mismatch(pos, ty, "`[]`", tys),
        },
        Part::Array(node, parts) => match tys.get(ty) {
            Ty::Array(elem, len) if len.cmp_u64(parts.len() as u64) == Ordering::Equal => {
                let elem = *elem;
                let mut elems = Vec::with_capacity(parts.len());
                for part in parts {
                    elems.push(build(env, fuel, tys, pos, elem, part)?);
                }
                array_of(env, fuel, tys, *node, elems).map(Cow::Owned)
            }
            _ => mismatch(pos, ty, "an array literal with `[]`", tys),
        },
        Part::Tuple(node, parts) => match tys.get(ty) {
            Ty::Tuple(types) if types.len() == parts.len() => {
                let mut elems = Vec::with_capacity(parts.len());
                for (k, part) in parts.iter().enumerate() {
                    let elem_ty = tys.part(ty, k).unwrap_or(ty);
                    elems.push(build(env, fuel, tys, pos, elem_ty, part)?);
                }
                tuple_of(env, fuel, *node, elems).map(Cow::Owned)
            }
            _ => mismatch(pos, ty, "a tuple literal with `[]`", tys),
        },
    }
}

impl Evaluator<'_> {
    /// A new value or type of the depth `depth` at `pos`.
    pub(super) fn bounded(&self, pos: Pos, depth: u64) -> Res<()> {
        bounded(self.limit, pos, depth)
    }

    /// The elements of a container literal, each checked as it evaluates. In this phase a
    /// container holds only static values. A hardware value is `S010`, and a handle is `S010`
    /// until slice 3. The position is that of the first `[]` among the elements that wait.
    pub(super) fn elements(&mut self, xs: &[Expr]) -> Res<(Vec<Out>, Option<Pos>)> {
        let mut outs = Vec::with_capacity(xs.len());
        let mut waiting = None;
        for x in xs {
            let o = self.eval(x)?;
            let o = need(x, o)?;
            match self.store.seen(&o) {
                Seen::Static(_) => {}
                Seen::Pending(q, _) => {
                    waiting.get_or_insert(q);
                }
                Seen::Hw(_) => {
                    return fail(
                        Code::S010,
                        super::expr_pos(x),
                        "a container holds only static values in this phase".to_owned(),
                    );
                }
                s @ Seen::Handle(_) => {
                    return fail(
                        Code::S010,
                        super::expr_pos(x),
                        format!("{} is not an element before slice 3", self.text(s)),
                    );
                }
            }
            outs.push(o);
        }
        Ok((outs, waiting))
    }

    /// The tuple type of the element types `elems` at `pos`.
    pub(super) fn tuple_type(&mut self, pos: Pos, elems: &[TypeExpr]) -> Res<TyId> {
        let mut types = Vec::with_capacity(elems.len());
        for elem in elems {
            types.push(self.type_expr(elem)?);
        }
        let ty = self.tys.tuple(types);
        self.new_type(pos, ty)
    }

    /// The array type `[elem; len]` at `pos`. The length is a static `Nat`.
    pub(super) fn array_type(&mut self, pos: Pos, elem: &TypeExpr, len: &Expr) -> Res<TyId> {
        let elem = self.type_expr(elem)?;
        let out = self.eval(len)?;
        let out = need(len, out)?;
        let at_len = super::expr_pos(len);
        self.check_static(at_len, &out)?;
        match self.store.value(&out) {
            Value::Int(n) if n.is_negative() => fail(
                Code::S012,
                at_len,
                format!("the length {} is not a Nat", ops::int_text(n)),
            ),
            Value::Int(n) => {
                let ty = self.tys.array(elem, n.clone());
                self.new_type(pos, ty)
            }
            other => fail(
                Code::S010,
                at_len,
                format!(
                    "the length of an array is a static Nat, not {}",
                    other.text(&self.tys)
                ),
            ),
        }
    }

    /// A new container type at `pos`: its depth, then the charge of its size.
    fn new_type(&mut self, pos: Pos, ty: TyId) -> Res<TyId> {
        self.bounded(pos, ty.depth())?;
        self.charge(pos, u128::from(ty.size()))?;
        Ok(ty)
    }

    /// A container expression: `()`, a tuple or an array literal, or a selector `.N`. A literal
    /// with `[]` waits for the type of a typed use.
    pub(super) fn container(&mut self, e: &Expr) -> Res<Option<Out>> {
        match e {
            Expr::Unit { pos } => self.made(*pos, Value::Unit),
            Expr::Tuple { pos, elems } => {
                let (outs, waiting) = self.elements(elems)?;
                if let Some(q) = waiting {
                    let parts = outs.into_iter().map(Out::into_part).collect();
                    return Ok(Some(Out::Made(Val::Pending(q, Part::Tuple(*pos, parts)))));
                }
                let v = self.tuple_of(*pos, outs)?;
                Ok(Some(Out::Made(Val::Static(v))))
            }
            Expr::Array { pos, elems } if elems.is_empty() => {
                self.charge(*pos, 1)?;
                Ok(Some(Out::Made(Val::Pending(*pos, Part::Empty(*pos)))))
            }
            Expr::Array { pos, elems } => {
                let (outs, waiting) = self.elements(elems)?;
                if let Some(q) = waiting {
                    let parts = outs.into_iter().map(Out::into_part).collect();
                    return Ok(Some(Out::Made(Val::Pending(q, Part::Array(*pos, parts)))));
                }
                let v = self.array_of(*pos, outs)?;
                Ok(Some(Out::Made(Val::Static(v))))
            }
            _ => fail(
                Code::S010,
                super::expr_pos(e),
                "not a container expression".to_owned(),
            ),
        }
    }

    /// A tuple literal at `pos` whose elements are all static.
    pub(super) fn tuple_of(&mut self, pos: Pos, outs: Vec<Out>) -> Res<Value> {
        let env = Env {
            store: &self.store,
            limit: self.limit,
        };
        let elems = outs.into_iter().map(|o| cow(env.store, o)).collect();
        tuple_of(env, &mut self.fuel, pos, elems)
    }

    /// An array literal at `pos` whose elements are all static.
    pub(super) fn array_of(&mut self, pos: Pos, outs: Vec<Out>) -> Res<Value> {
        let env = Env {
            store: &self.store,
            limit: self.limit,
        };
        let elems = outs.into_iter().map(|o| cow(env.store, o)).collect();
        array_of(env, &mut self.fuel, &mut self.tys, pos, elems)
    }

    /// A typed use of the type `t` at `pos` gives a literal that waits its type.
    pub(super) fn settle(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Out> {
        let Out::Made(Val::Pending(_, part)) = out else {
            return Ok(out);
        };
        let env = Env {
            store: &self.store,
            limit: self.limit,
        };
        let v = build(env, &mut self.fuel, &mut self.tys, pos, t, &part)?.into_owned();
        Ok(Out::Made(Val::Static(v)))
    }
}
