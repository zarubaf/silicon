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
    let mut work = vec![(v, t)];
    while let Some((v, t)) = work.pop() {
        let same = match (v, tys.get(t)) {
            (Value::Unit, Ty::Unit) | (Value::Int(_), Ty::Int) | (Value::Bool(_), Ty::Bool) => true,
            (Value::UInt(x), Ty::UInt(w)) | (Value::SInt(x), Ty::SInt(w)) => x.width() == *w,
            (Value::Array(e, xs), Ty::Array(te, n)) => {
                e == te && n.cmp_u64(xs.len() as u64) == Ordering::Equal
            }
            (Value::Tuple(xs), Ty::Tuple(ts)) => {
                work.extend(xs.iter().zip(ts.iter().copied()));
                xs.len() == ts.len()
            }
            _ => false,
        };
        if !same {
            return false;
        }
    }
    true
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
/// that differs is `S010`. A negative `Nat` is `S012`. Both come before the charge. The walk
/// checks each node before its elements, from left to right.
fn plan(t: TyId, v: &Value, tys: &Types) -> Result<u64, Fault> {
    let mut size = 0u64;
    let mut work = vec![(t, v)];
    while let Some((t, v)) = work.pop() {
        let node = tys.get(t);
        match (node, v) {
            (Ty::Array(e, n), Value::Array(_, xs)) => {
                if n.cmp_u64(xs.len() as u64) != Ordering::Equal {
                    return wrong(node, v, tys);
                }
                size = size.saturating_add(1);
                work.extend(xs.iter().rev().map(|x| (*e, x)));
            }
            (Ty::Tuple(ts), Value::Tuple(xs)) => {
                if ts.len() != xs.len() {
                    return wrong(node, v, tys);
                }
                size = size.saturating_add(1);
                work.extend(ts.iter().copied().zip(xs).rev());
            }
            _ => {
                leaf(node, v, tys)?;
                size = size.saturating_add(leaf_size(node, v));
            }
        }
    }
    Ok(size)
}

/// A step of the conversion: convert a value at a type, or make a container of the last `n`
/// results.
enum Step<'a> {
    Visit(TyId, &'a Value),
    Array(TyId, usize),
    Tuple(usize),
}

/// The conversion, element by element and from left to right. A value that does not fit is
/// `S012`.
fn run(t: TyId, v: &Value, tys: &Types) -> Result<Value, Fault> {
    let mut done: Vec<Value> = Vec::new();
    let mut work = vec![Step::Visit(t, v)];
    while let Some(step) = work.pop() {
        match step {
            Step::Visit(t, v) => {
                let node = tys.get(t);
                match (node, v) {
                    (Ty::Array(e, _), Value::Array(_, xs)) => {
                        work.push(Step::Array(*e, xs.len()));
                        work.extend(xs.iter().rev().map(|x| Step::Visit(*e, x)));
                    }
                    (Ty::Tuple(ts), Value::Tuple(xs)) => {
                        work.push(Step::Tuple(xs.len()));
                        work.extend(
                            ts.iter()
                                .copied()
                                .zip(xs)
                                .rev()
                                .map(|(t, x)| Step::Visit(t, x)),
                        );
                    }
                    (_, Value::Int(n)) if matches!(leaf(node, v, tys), Ok(Leaf::Fit)) => {
                        done.push(fit(node, n, tys)?);
                    }
                    _ => done.push(v.clone()),
                }
            }
            Step::Array(e, n) => {
                let xs = done.split_off(done.len().saturating_sub(n));
                done.push(Value::Array(e, xs));
            }
            Step::Tuple(n) => {
                let xs = done.split_off(done.len().saturating_sub(n));
                done.push(Value::Tuple(xs));
            }
        }
    }
    Ok(done.pop().unwrap_or(Value::Unit))
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

/// A step of the common type: join two types, or make the container type of the pair
/// `(lhs, rhs)` from the last results.
enum Join {
    Visit(TyId, TyId),
    Array(TyId, TyId, Int),
    Tuple(TyId, TyId, usize),
}

/// The common type of two types by the operand rule: a static integer takes the finite type
/// of the other side. Arrays need one length and tuples one arity. Equal ids are the common
/// type with no walk, so the walk goes only along the parts that differ. The parts join from
/// left to right, and the first part without a common type ends the walk.
///
/// A type shares its parts, so its term can be exponentially larger than its table entries.
/// The table keeps the join of each pair of ids, so each pair joins once in an elaboration
/// and the walk is in the entries, not in the term.
pub(crate) fn common_ty(lhs: TyId, rhs: TyId, tys: &mut Types) -> Option<TyId> {
    let mut done: Vec<TyId> = Vec::new();
    let mut work = vec![Join::Visit(lhs, rhs)];
    while let Some(step) = work.pop() {
        let (key, joined) = match step {
            Join::Visit(lhs, rhs) if lhs == rhs => {
                done.push(lhs);
                continue;
            }
            Join::Visit(lhs, rhs) => {
                if let Some(joined) = tys.joined(lhs, rhs) {
                    ((lhs, rhs), *joined)
                } else {
                    match (tys.get(lhs).clone(), tys.get(rhs).clone()) {
                        (Ty::Array(left, len), Ty::Array(right, other)) if len == other => {
                            work.push(Join::Array(lhs, rhs, len));
                            work.push(Join::Visit(left, right));
                            continue;
                        }
                        (Ty::Tuple(lefts), Ty::Tuple(rights)) if lefts.len() == rights.len() => {
                            work.push(Join::Tuple(lhs, rhs, lefts.len()));
                            work.extend(
                                lefts
                                    .into_iter()
                                    .zip(rights)
                                    .rev()
                                    .map(|(l, r)| Join::Visit(l, r)),
                            );
                            continue;
                        }
                        (Ty::Int, Ty::Nat) | (Ty::Nat, Ty::Int) => {
                            ((lhs, rhs), Some(tys.mk(Ty::Int)))
                        }
                        (Ty::Int | Ty::Nat, other) => {
                            ((lhs, rhs), other.is_finite().then_some(rhs))
                        }
                        (other, Ty::Int | Ty::Nat) => {
                            ((lhs, rhs), other.is_finite().then_some(lhs))
                        }
                        _ => ((lhs, rhs), None),
                    }
                }
            }
            Join::Array(lhs, rhs, len) => {
                let elem = done.pop();
                ((lhs, rhs), elem.map(|elem| tys.array(elem, len)))
            }
            Join::Tuple(lhs, rhs, n) => {
                let parts = done.split_off(done.len().saturating_sub(n));
                ((lhs, rhs), Some(tys.tuple(parts)))
            }
        };
        tys.join(key, joined);
        let Some(t) = joined else {
            // Each open pair holds this pair, so none of them has a common type.
            for open in work {
                if let Join::Array(l, r, _) | Join::Tuple(l, r, _) = open {
                    tys.join((l, r), None);
                }
            }
            return None;
        };
        done.push(t);
    }
    done.pop()
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

/// The type check of `==` on containers, by the operand rule for each pair of elements. The
/// walk checks each pair before its elements, from left to right.
fn same_check(a: &Value, b: &Value, tys: &mut Types) -> Result<(), Fault> {
    let mut work = vec![(a, b)];
    while let Some((a, b)) = work.pop() {
        match (a, b) {
            (Value::Unit, Value::Unit) => {}
            (Value::Array(s, xs), Value::Array(t, ys)) => {
                if common_ty(*s, *t, tys).is_none() || xs.len() != ys.len() {
                    return no_common_type(a, b, tys);
                }
                work.extend(xs.iter().zip(ys).rev());
            }
            (Value::Tuple(xs), Value::Tuple(ys)) => {
                if xs.len() != ys.len() {
                    return no_common_type(a, b, tys);
                }
                work.extend(xs.iter().zip(ys).rev());
            }
            _ if composite(a) || composite(b) => return no_common_type(a, b, tys),
            _ => leaf_eq_check(a, b, tys)?,
        }
    }
    Ok(())
}

/// The comparison, after the check and the charge. Each pair compares, from left to right, so
/// each conversion checks its fit (`S012`) even after a pair that differs.
fn same_run(a: &Value, b: &Value, tys: &Types) -> Result<bool, Fault> {
    let mut all = true;
    let mut work = vec![(a, b)];
    while let Some((a, b)) = work.pop() {
        match (a, b) {
            (Value::Array(_, xs), Value::Array(_, ys)) | (Value::Tuple(xs), Value::Tuple(ys)) => {
                work.extend(xs.iter().zip(ys).rev());
            }
            (Value::Unit, Value::Unit) => {}
            _ => all &= leaf_eq_run(a, b, tys)?,
        }
    }
    Ok(all)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::Fuel;

    /// Runs `f` on a thread with a small stack, so a walk that recurses over a deep value
    /// overflows it.
    fn small_stack(f: impl FnOnce() + Send) {
        std::thread::scope(|scope| {
            let worker = std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, f);
            assert!(worker.is_ok_and(|w| w.join().is_ok()));
        });
    }

    /// The tuple `((x,),)` of depth `depth` around `x`, and its type around the type `t`.
    fn deep(tys: &mut Types, depth: usize, x: Value, mut t: TyId) -> (Value, TyId) {
        let mut v = x;
        for _ in 0..depth {
            v = Value::Tuple(vec![v]);
            t = tys.tuple(vec![t]);
        }
        (v, t)
    }

    /// Each walk over a value or a type keeps its own stack, so a value of depth 100,000
    /// needs no deep stack.
    #[test]
    fn the_walks_over_a_deep_value_do_not_recurse() {
        small_stack(|| {
            const DEPTH: usize = 100_000;
            let mut tys = Types::default();
            let (int, nat) = (tys.mk(Ty::Int), tys.mk(Ty::Nat));
            let (v, t) = deep(&mut tys, DEPTH, Value::Int(Int::from_u64(7)), int);
            let (_, tn) = deep(&mut tys, DEPTH, Value::Unit, nat);
            assert_eq!(v.size(), DEPTH as u64 + 1);
            assert_eq!(v.depth(), DEPTH as u64 + 1);
            assert_eq!(v.measure_charge(), DEPTH as u128 + 1);
            let text = v.serialize(&tys);
            assert_eq!(text.len() as u64, v.serialized_len(&tys));
            assert_eq!(v.ty(&mut tys), Some(t));
            assert!(v.text(&tys).ends_with("..."));
            assert!(tys.text(t).len() < 1100);
            let w = v.clone();
            // `assert_eq` would print the deep value with the recursive `Debug`.
            let same = v == w;
            assert!(same);
            let mut fuel = Fuel::new(u64::MAX);
            let n = convert(tn, &v, &mut fuel, &tys);
            assert!(matches!(n, Ok(Some(_))));
            let eq = container_op(BinOp::Eq, &v, &w, &mut fuel, &mut tys);
            assert!(matches!(eq, Ok(Value::Bool(true))));
            assert_eq!(common_ty(t, tn, &mut tys), Some(t));
        });
    }

    /// The type `(t, t)` doubled `levels` times: its term has `2^levels` leaves, and the
    /// table has one entry for each level.
    fn doubled(tys: &mut Types, mut t: TyId, levels: usize) -> TyId {
        for _ in 0..levels {
            t = tys.tuple(vec![t, t]);
        }
        t
    }

    /// Two doubled types of 100 levels join in work linear in the levels, not in their terms.
    #[test]
    fn a_join_of_shared_types_walks_each_pair_once() {
        let mut tys = Types::default();
        let (int, byte) = (tys.mk(Ty::Int), tys.mk(Ty::UInt(8)));
        let (a, b) = (doubled(&mut tys, int, 100), doubled(&mut tys, byte, 100));
        let before = tys.work;
        assert_eq!(common_ty(a, b, &mut tys), Some(b));
        assert!(tys.work - before <= 4 * 100, "{}", tys.work - before);
        let again = tys.work;
        assert_eq!(common_ty(a, b, &mut tys), Some(b));
        assert_eq!(tys.work, again);
    }
}
