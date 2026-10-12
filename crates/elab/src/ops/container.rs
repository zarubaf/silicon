// SPDX-License-Identifier: Apache-2.0
//! The rules of the static containers in Lean `Source.Eval`: the typed use of a container, the
//! common type of two types, and `==` on containers. A typed use and `==` check the types
//! first, then pay their charge, and only then run, as every operation of `ops` does. A
//! type error thus costs no fuel, and a value that does not fit (`S012`) fails after the
//! charge.

use super::{Fault, Fuel, finite, fits, int_text, type_error};
use crate::Code;
use crate::int::Int;
use crate::value::{Ty, TyId, Types, Value, int_size, width_size};
use parse::ast::BinOp;
use std::cmp::Ordering;

/// A container: `()`, an array, or a tuple.
pub(crate) fn composite(v: &Value) -> bool {
    matches!(v, Value::Unit | Value::Array(..) | Value::Tuple(_))
}

/// Whether the type of `v` is `t`. It is `v.ty() == Some(t)` without the type.
fn is_of(v: &Value, t: TyId, tys: &Types) -> bool {
    match (v, tys.get(t)) {
        (Value::Unit, Ty::Unit) | (Value::Int(_), Ty::Int) | (Value::Bool(_), Ty::Bool) => true,
        (Value::UInt(x), Ty::UInt(w)) | (Value::SInt(x), Ty::SInt(w)) => x.width() == *w,
        (Value::Array(e, xs), Ty::Array(te, n)) => {
            e == te && n.cmp_u64(xs.len() as u64) == Ordering::Equal
        }
        (Value::Tuple(xs), Ty::Tuple(ts)) => {
            xs.len() == ts.len() && xs.iter().zip(ts).all(|(x, t)| is_of(x, *t, tys))
        }
        _ => false,
    }
}

fn wrong<T>(t: &Ty, v: &Value, tys: &Types) -> Result<T, Fault> {
    type_error(format!(
        "expected {}, but the value is {}",
        tys.text_of(t),
        v.text(tys)
    ))
}

/// What a typed use of a scalar or `()` at a type does.
enum Leaf {
    /// The value is the result.
    Same,
    /// A static integer takes a finite type, if it fits.
    Fit,
}

/// The check of a typed use of a scalar or `()` at `t`, before any charge. A `()` part of a
/// container comes here, because it has no elements.
fn leaf(t: &Ty, v: &Value, tys: &Types) -> Result<Leaf, Fault> {
    match (t, v) {
        (Ty::Unit, Value::Unit) | (Ty::Bool, Value::Bool(_)) | (Ty::Int, Value::Int(_)) => {
            Ok(Leaf::Same)
        }
        (Ty::Nat, Value::Int(n)) => {
            if n.is_negative() {
                Err((Code::S012, format!("{} is not a Nat", int_text(n))))
            } else {
                Ok(Leaf::Same)
            }
        }
        (Ty::UInt(w), Value::UInt(x)) | (Ty::SInt(w), Value::SInt(x)) => {
            if x.width() == *w {
                Ok(Leaf::Same)
            } else {
                wrong(t, v, tys)
            }
        }
        (Ty::UInt(_) | Ty::SInt(_), Value::Int(_)) => Ok(Leaf::Fit),
        _ => wrong(t, v, tys),
    }
}

/// The finite value of the static integer `n` at the finite type `t`, if it fits.
fn fit(t: &Ty, n: &Int, tys: &Types) -> Result<Value, Fault> {
    let (Ty::UInt(w) | Ty::SInt(w)) = t else {
        return wrong(t, &Value::Int(n.clone()), tys);
    };
    if !fits(t, n) {
        return Err((
            Code::S012,
            format!("{} does not fit {}", int_text(n), tys.text_of(t)),
        ));
    }
    let bits = n
        .to_finite(*w)
        .ok_or_else(|| (Code::S012, format!("no value of {w} bits")))?;
    Ok(finite(matches!(t, Ty::SInt(_)), bits))
}

/// A typed use of a scalar at `t`: the result, or `None` if `v` itself is the result. The
/// conversion of a static integer charges the sizes of the integer and of the width.
pub(crate) fn convert_scalar(
    t: &Ty,
    v: &Value,
    fuel: &mut Fuel,
    tys: &Types,
) -> Result<Option<Value>, Fault> {
    match leaf(t, v, tys)? {
        Leaf::Same => Ok(None),
        Leaf::Fit => {
            let (Ty::UInt(w) | Ty::SInt(w), Value::Int(n)) = (t, v) else {
                return wrong(t, v, tys);
            };
            fuel.pay(u128::from(int_size(n)) + u128::from(width_size(*w)))?;
            fit(t, n, tys).map(Some)
        }
    }
}

/// The size of a scalar `v` after its typed use at `t`.
fn leaf_size(t: &Ty, v: &Value) -> u64 {
    match t {
        Ty::UInt(w) | Ty::SInt(w) => width_size(*w),
        _ => v.size(),
    }
}

/// The size of the converted container, and the check of its shape. A shape or a scalar type
/// that differs is `S010`. A negative `Nat` is `S012`. Both come before the charge.
fn plan(t: TyId, v: &Value, tys: &Types) -> Result<u64, Fault> {
    let node = tys.get(t);
    match (node, v) {
        (Ty::Array(e, n), Value::Array(_, xs)) => {
            if n.cmp_u64(xs.len() as u64) != Ordering::Equal {
                return wrong(node, v, tys);
            }
            let mut size = 1;
            for x in xs {
                size += plan(*e, x, tys)?;
            }
            Ok(size)
        }
        (Ty::Tuple(ts), Value::Tuple(xs)) => {
            if ts.len() != xs.len() {
                return wrong(node, v, tys);
            }
            let mut size = 1;
            for (t, x) in ts.iter().zip(xs) {
                size += plan(*t, x, tys)?;
            }
            Ok(size)
        }
        _ => {
            leaf(node, v, tys)?;
            Ok(leaf_size(node, v))
        }
    }
}

/// The conversion, element by element. A value that does not fit is `S012`.
fn run(t: TyId, v: &Value, tys: &Types) -> Result<Value, Fault> {
    let node = tys.get(t);
    match (node, v) {
        (Ty::Array(e, _), Value::Array(_, xs)) => {
            let ys = xs
                .iter()
                .map(|x| run(*e, x, tys))
                .collect::<Result<_, _>>()?;
            Ok(Value::Array(*e, ys))
        }
        (Ty::Tuple(ts), Value::Tuple(xs)) => {
            let ys = ts
                .iter()
                .zip(xs)
                .map(|(t, x)| run(*t, x, tys))
                .collect::<Result<_, _>>()?;
            Ok(Value::Tuple(ys))
        }
        (_, Value::Int(n)) if matches!(leaf(node, v, tys), Ok(Leaf::Fit)) => fit(node, n, tys),
        _ => Ok(v.clone()),
    }
}

/// A typed use of a container or `()` at `t`. A value of the type `t` charges nothing.
/// Another container charges its size plus the size of the result, as a scalar conversion
/// does.
pub(crate) fn convert(
    t: TyId,
    v: &Value,
    fuel: &mut Fuel,
    tys: &Types,
) -> Result<Option<Value>, Fault> {
    if is_of(v, t, tys) {
        return Ok(None);
    }
    let result = plan(t, v, tys)?;
    fuel.pay(u128::from(v.size()) + u128::from(result))?;
    run(t, v, tys).map(Some)
}

/// The common type of two types by the operand rule: a static integer takes the finite type
/// of the other side. Arrays need one length and tuples one arity. Equal ids are the common
/// type with no walk, so the walk goes only along the parts that differ.
pub(crate) fn common_ty(lhs: TyId, rhs: TyId, tys: &mut Types) -> Option<TyId> {
    if lhs == rhs {
        return Some(lhs);
    }
    match (tys.get(lhs).clone(), tys.get(rhs).clone()) {
        (Ty::Array(left, len), Ty::Array(right, other)) => {
            if len == other {
                let elem = common_ty(left, right, tys)?;
                Some(tys.array(elem, len))
            } else {
                None
            }
        }
        (Ty::Tuple(lefts), Ty::Tuple(rights)) => {
            if lefts.len() != rights.len() {
                return None;
            }
            let mut parts = Vec::with_capacity(lefts.len());
            for (left, right) in lefts.into_iter().zip(rights) {
                parts.push(common_ty(left, right, tys)?);
            }
            Some(tys.tuple(parts))
        }
        (Ty::Int, Ty::Nat) | (Ty::Nat, Ty::Int) => Some(tys.mk(Ty::Int)),
        (Ty::Int | Ty::Nat, other) => other.is_finite().then_some(rhs),
        (other, Ty::Int | Ty::Nat) => other.is_finite().then_some(lhs),
        _ => None,
    }
}

/// The common type of the elements of an array literal, if they have one. There is none for
/// no element.
pub(crate) fn common_of<'a>(
    vs: impl IntoIterator<Item = &'a Value>,
    tys: &mut Types,
) -> Option<TyId> {
    let mut vs = vs.into_iter();
    let mut t = vs.next()?.ty(tys)?;
    for w in vs {
        let u = w.ty(tys)?;
        t = common_ty(t, u, tys)?;
    }
    Some(t)
}

/// `==` on two scalars of a container: the check. A static integer takes the finite type of
/// the other side.
fn leaf_eq_check(a: &Value, b: &Value, tys: &Types) -> Result<(), Fault> {
    match (a, b, a.finite_ty(), b.finite_ty()) {
        (Value::Int(_), _, _, Some(t)) => leaf(&t, a, tys).map(|_| ()),
        (_, Value::Int(_), Some(t), _) => leaf(&t, b, tys).map(|_| ()),
        _ => super::equal_check(a, b, tys),
    }
}

/// `==` on two scalars of a container: the comparison, after the charge.
fn leaf_eq_run(a: &Value, b: &Value, tys: &Types) -> Result<bool, Fault> {
    match (a, b, a.finite_ty(), b.finite_ty()) {
        (Value::Int(n), _, _, Some(t)) => Ok(fit(&t, n, tys)? == *b),
        (_, Value::Int(n), Some(t), _) => Ok(*a == fit(&t, n, tys)?),
        _ => Ok(a == b),
    }
}

fn no_common_type<T>(a: &Value, b: &Value, tys: &Types) -> Result<T, Fault> {
    type_error(format!(
        "`==` needs a common type, not {} and {}",
        a.text(tys),
        b.text(tys)
    ))
}

/// The type check of `==` on containers, by the operand rule for each pair of elements.
fn same_check(a: &Value, b: &Value, tys: &mut Types) -> Result<(), Fault> {
    match (a, b) {
        (Value::Unit, Value::Unit) => Ok(()),
        (Value::Array(s, xs), Value::Array(t, ys)) => {
            if common_ty(*s, *t, tys).is_none() || xs.len() != ys.len() {
                return no_common_type(a, b, tys);
            }
            xs.iter()
                .zip(ys)
                .try_for_each(|(x, y)| same_check(x, y, tys))
        }
        (Value::Tuple(xs), Value::Tuple(ys)) => {
            if xs.len() != ys.len() {
                return no_common_type(a, b, tys);
            }
            xs.iter()
                .zip(ys)
                .try_for_each(|(x, y)| same_check(x, y, tys))
        }
        _ if composite(a) || composite(b) => no_common_type(a, b, tys),
        _ => leaf_eq_check(a, b, tys),
    }
}

/// The comparison, after the check and the charge. Each pair compares, so each conversion
/// checks its fit (`S012`) even after a pair that differs.
fn same_run(a: &Value, b: &Value, tys: &Types) -> Result<bool, Fault> {
    match (a, b) {
        (Value::Array(_, xs), Value::Array(_, ys)) | (Value::Tuple(xs), Value::Tuple(ys)) => {
            let mut all = true;
            for (x, y) in xs.iter().zip(ys) {
                all &= same_run(x, y, tys)?;
            }
            Ok(all)
        }
        (Value::Unit, Value::Unit) => Ok(true),
        _ => leaf_eq_run(a, b, tys),
    }
}

/// A binary operator with a container operand. `==` and `!=` read both operands in full, so
/// they charge the sum of the sizes. The orderings take no container.
pub(crate) fn container_op(
    op: BinOp,
    a: &Value,
    b: &Value,
    fuel: &mut Fuel,
    tys: &mut Types,
) -> Result<Value, Fault> {
    let text = super::binop_text(op);
    match op {
        BinOp::Eq | BinOp::Ne => {
            same_check(a, b, tys)?;
            fuel.pay(u128::from(a.size()) + u128::from(b.size()))?;
            let x = same_run(a, b, tys)?;
            Ok(Value::Bool(if op == BinOp::Eq { x } else { !x }))
        }
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            type_error(format!("`{text}` takes no container"))
        }
        _ => type_error(format!(
            "`{text}` does not accept {} and {}",
            a.text(tys),
            b.text(tys)
        )),
    }
}
