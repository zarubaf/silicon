// SPDX-License-Identifier: Apache-2.0
//! The rules of the static containers in Lean `Source.Eval`: the typed use of a container, the
//! common type of two types, and `==` on containers. A typed use and `==` check the types
//! first, then pay their charge, and only then run, as every operation of `ops` does. A
//! type error thus costs no fuel, and a value that does not fit (`S012`) fails after the
//! charge.

use super::{Fault, Fuel, finite, fits, int_text, type_error};
use crate::Code;
use crate::int::Int;
use crate::types::{Joined, Ty, TyId, Types};
use crate::value::{Value, int_size, width_size};
use parse::ast::BinOp;
use std::cmp::Ordering;

/// A container: `()`, an array, a tuple, a record, or a list.
pub(crate) fn composite(v: &Value) -> bool {
    matches!(
        v,
        Value::Unit | Value::Array(..) | Value::Tuple(_) | Value::Record(..) | Value::List(..)
    )
}

/// Whether the type of `v` is `t`. It is `v.ty() == Some(t)` without the type.
fn is_of(v: &Value, t: TyId, tys: &Types) -> bool {
    let mut work = vec![(v, t)];
    while let Some((v, t)) = work.pop() {
        let same = match (v, tys.get(t)) {
            (Value::Unit, Ty::Unit)
            | (Value::Int(_), Ty::Int)
            | (Value::Bool(_), Ty::Bool)
            | (Value::Type(_), Ty::Type)
            | (Value::Str(_), Ty::String) => true,
            (Value::Record(s, _), Ty::Struct(_)) => *s == t,
            (Value::UInt(x), Ty::UInt(w)) | (Value::SInt(x), Ty::SInt(w)) => x.width() == *w,
            (Value::Array(e, xs), Ty::Array(te, n)) => {
                e == te && n.cmp_u64(xs.len() as u64) == Ordering::Equal
            }
            (Value::List(e, _), Ty::List(te)) => e == te,
            (Value::Function(_, _, sig), Ty::Fn(..)) => *sig == t,
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
        (Ty::Unit, Value::Unit)
        | (Ty::Bool, Value::Bool(_))
        | (Ty::Int, Value::Int(_))
        | (Ty::Type, Value::Type(_))
        | (Ty::String, Value::Str(_)) => Ok(Leaf::Same),
        (Ty::Struct(_), Value::Record(s, _)) if tys.get(*s) == t => Ok(Leaf::Same),
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

/// A typed use of a function value at the function type `t`: its signature must be exactly
/// `t`, with the `mut` marks. It compares two ids and charges nothing.
pub(crate) fn convert_fn(t: TyId, v: &Value, tys: &Types) -> Result<Option<Value>, Fault> {
    match v {
        Value::Function(_, _, sig) if *sig == t => Ok(None),
        _ => wrong(tys.get(t), v, tys),
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
            (Ty::List(e), Value::List(_, xs)) => {
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
            (Ty::Fn(..), Value::Function(_, _, sig)) if *sig == t => {
                size = size.saturating_add(1);
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
    List(TyId, usize),
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
                    (Ty::List(e), Value::List(_, xs)) => {
                        work.push(Step::List(*e, xs.len()));
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
            Step::List(e, n) => {
                let xs = done.split_off(done.len().saturating_sub(n));
                done.push(Value::List(e, xs));
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

/// A container pair of types that a join has opened: its parts wait in `pairs`, and the
/// results of the parts that joined collect in `parts`.
struct Open {
    key: (TyId, TyId),
    form: Form,
    pairs: Vec<(TyId, TyId)>,
    next: usize,
    /// The units of the walk of this pair so far: 1 for the pair, and the units of its parts.
    charge: Int,
    parts: Vec<TyId>,
    failed: bool,
}

/// The form of a container pair that a join opened. An array pair keeps its length.
enum Form {
    Array(Int),
    List,
    Tuple,
}

/// The step of a join at a pair: a result, or a container pair that waits for its parts.
enum Visit {
    Done(Joined),
    Open(Open),
}

fn joined(charge: u64, ty: Option<TyId>) -> Joined {
    Joined {
        charge: Int::from_u64(charge),
        ty,
    }
}

/// A container type: an array, a tuple, a list, or a struct type.
fn container_ty(t: &Ty) -> bool {
    matches!(
        t,
        Ty::Array(..) | Ty::Tuple(_) | Ty::List(_) | Ty::Struct(_)
    )
}

/// The common type of two types that are not two arrays, two tuples, or two struct types: the
/// operand rule. A static integer takes the finite type of the other side.
fn scalar_join(lhs: TyId, rhs: TyId, tys: &mut Types) -> Option<TyId> {
    if lhs == rhs {
        return Some(lhs);
    }
    match (tys.get(lhs), tys.get(rhs)) {
        (Ty::Int, Ty::Nat) | (Ty::Nat, Ty::Int) => Some(tys.mk(Ty::Int)),
        (Ty::Int | Ty::Nat, other) => other.is_finite().then_some(rhs),
        (other, Ty::Int | Ty::Nat) => other.is_finite().then_some(lhs),
        _ => None,
    }
}

/// The step of a join at `(lhs, rhs)`. A pair of arrays or of tuples of one shape opens, and it
/// costs one unit of the `budget` of new pairs. Another pair has its result at once.
fn visit(lhs: TyId, rhs: TyId, tys: &mut Types, budget: &mut u64) -> Visit {
    #[cfg(test)]
    tys.tick(1);
    if let Some(done) = tys.joined(lhs, rhs) {
        return Visit::Done(done.clone());
    }
    let open = |form: Form, pairs: Vec<(TyId, TyId)>| Open {
        key: (lhs, rhs),
        form,
        pairs,
        next: 0,
        charge: Int::from_u64(1),
        parts: Vec::new(),
        failed: false,
    };
    let (left, right) = (tys.get(lhs).clone(), tys.get(rhs).clone());
    let shaped = match (&left, &right) {
        (Ty::Array(a, n), Ty::Array(b, m)) => {
            Some((n == m).then(|| (Form::Array(n.clone()), vec![(*a, *b)])))
        }
        (Ty::List(a), Ty::List(b)) => Some(Some((Form::List, vec![(*a, *b)]))),
        (Ty::Tuple(ls), Ty::Tuple(rs)) => Some((ls.len() == rs.len()).then(|| {
            (
                Form::Tuple,
                ls.iter().copied().zip(rs.iter().copied()).collect(),
            )
        })),
        _ => None,
    };
    match shaped {
        Some(None) => Visit::Done(joined(1, None)),
        Some(Some((form, pairs))) => {
            // The charge of this pair exceeds the units that remain, or the walk makes more
            // new pairs than the fuel holds: no fuel pays the join.
            if *budget == 0 {
                return Visit::Done(Joined {
                    charge: Int::from_u64(u64::MAX).add(&Int::from_u64(1)),
                    ty: None,
                });
            }
            *budget -= 1;
            Visit::Open(open(form, pairs))
        }
        None => match (&left, &right) {
            (Ty::Struct(_), Ty::Struct(_)) | (Ty::Fn(..), Ty::Fn(..)) => Visit::Done(Joined {
                charge: Int::from_u64(lhs.size()).add(&Int::from_u64(rhs.size())),
                ty: (lhs == rhs).then_some(lhs),
            }),
            (l, r) => {
                let units = u64::from(container_ty(l) && container_ty(r));
                Visit::Done(joined(units, scalar_join(lhs, rhs, tys)))
            }
        },
    }
}

/// The join of two types: their common type by the operand rule, and the units that the walk
/// charges (design section 5.4). The walk charges 1 before it visits each pair of container
/// types. A pair of struct types charges the sum of the two sizes and compares the ids. The
/// parts join from left to right, and the first part without a common type ends the pair.
///
/// A type shares its parts, so its term can be exponentially larger than its table entries.
/// The table keeps the join of each pair of ids with its units, so each pair joins once in an
/// elaboration and the work is in the entries, not in the term. The `budget` bounds the
/// pairs of one call, so no walk makes more work than the fuel holds. A walk above it has
/// units that no fuel pays.
pub(crate) fn common_ty(lhs: TyId, rhs: TyId, tys: &mut Types, budget: &mut u64) -> Joined {
    let mut stack: Vec<Open> = Vec::new();
    let mut delivered = match visit(lhs, rhs, tys, budget) {
        Visit::Done(done) => Some(done),
        Visit::Open(open) => {
            stack.push(open);
            None
        }
    };
    loop {
        if let Some(done) = delivered.take() {
            let Some(top) = stack.last_mut() else {
                return done;
            };
            top.charge = top.charge.add(&done.charge);
            match done.ty {
                Some(t) => top.parts.push(t),
                None => top.failed = true,
            }
            top.next += 1;
        }
        let Some(top) = stack.last_mut() else {
            return joined(0, None);
        };
        if !top.failed
            && let Some(&(l, r)) = top.pairs.get(top.next)
        {
            match visit(l, r, tys, budget) {
                Visit::Done(done) => delivered = Some(done),
                Visit::Open(open) => stack.push(open),
            }
            continue;
        }
        let Some(finished) = stack.pop() else {
            return joined(0, None);
        };
        let ty = (!finished.failed).then(|| match finished.form {
            Form::Array(len) => finished.parts.first().map(|elem| tys.array(*elem, len)),
            Form::List => finished.parts.first().map(|elem| tys.list(*elem)),
            Form::Tuple => Some(tys.tuple(finished.parts)),
        });
        let ty = ty.flatten();
        let done = Joined {
            charge: finished.charge,
            ty,
        };
        tys.join(finished.key, done.clone());
        delivered = Some(done);
    }
}

/// The common type of the elements of an array literal, if they have one, and the units of
/// the joins. It joins the type of each element after the first with the join of the earlier
/// elements. There is none for no element.
pub(crate) fn common_of<'a>(
    vs: impl IntoIterator<Item = &'a Value>,
    tys: &mut Types,
    mut budget: u64,
) -> (Int, Option<TyId>) {
    let mut charge = Int::zero();
    let mut vs = vs.into_iter();
    let Some(mut t) = vs.next().map(|v| v.ty(tys)) else {
        return (charge, None);
    };
    for w in vs {
        let u = w.ty(tys);
        let done = common_ty(t, u, tys, &mut budget);
        charge = charge.add(&done.charge);
        let Some(next) = done.ty else {
            return (charge, None);
        };
        t = next;
    }
    (charge, Some(t))
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

/// The type check of `==` on containers, by the operand rule for each pair of elements, and
/// the units of the joins that it walked (design section 5.4). The walk checks each pair
/// before its elements, from left to right, and it stops at the first pair that fails. The
/// units count the pairs up to that one.
fn same_check(a: &Value, b: &Value, tys: &mut Types, mut budget: u64) -> (Int, Result<(), Fault>) {
    let mut charge = Int::zero();
    let mut work = vec![(a, b)];
    while let Some((a, b)) = work.pop() {
        match (a, b) {
            (Value::Unit, Value::Unit) => {}
            (Value::Array(s, xs), Value::Array(t, ys))
            | (Value::Record(s, xs), Value::Record(t, ys)) => {
                let done = common_ty(*s, *t, tys, &mut budget);
                charge = charge.add(&done.charge);
                if done.ty.is_none() || (matches!(a, Value::Array(..)) && xs.len() != ys.len()) {
                    return (charge, no_common_type(a, b, tys));
                }
                work.extend(xs.iter().zip(ys).rev());
            }
            (Value::List(s, xs), Value::List(t, ys)) => {
                let done = common_ty(*s, *t, tys, &mut budget);
                charge = charge.add(&done.charge);
                if done.ty.is_none() {
                    return (charge, no_common_type(a, b, tys));
                }
                if xs.len() == ys.len() {
                    work.extend(xs.iter().zip(ys).rev());
                }
            }
            (Value::Tuple(xs), Value::Tuple(ys)) => {
                if xs.len() != ys.len() {
                    return (charge, no_common_type(a, b, tys));
                }
                work.extend(xs.iter().zip(ys).rev());
            }
            _ if composite(a) || composite(b) => return (charge, no_common_type(a, b, tys)),
            _ => {
                if let Err(fault) = leaf_eq_check(a, b, tys) {
                    return (charge, Err(fault));
                }
            }
        }
    }
    (charge, Ok(()))
}

/// The comparison, after the check and the charge. Each pair compares, from left to right, so
/// each conversion checks its fit (`S012`) even after a pair that differs.
fn same_run(a: &Value, b: &Value, tys: &Types) -> Result<bool, Fault> {
    let mut all = true;
    let mut work = vec![(a, b)];
    while let Some((a, b)) = work.pop() {
        match (a, b) {
            (Value::Array(_, xs), Value::Array(_, ys))
            | (Value::Tuple(xs), Value::Tuple(ys))
            | (Value::Record(_, xs), Value::Record(_, ys)) => {
                work.extend(xs.iter().zip(ys).rev());
            }
            (Value::List(_, xs), Value::List(_, ys)) => {
                if xs.len() == ys.len() {
                    work.extend(xs.iter().zip(ys).rev());
                } else {
                    all = false;
                }
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
            let (units, checked) = same_check(a, b, tys, fuel.left());
            fuel.pay_int(&units)?;
            checked?;
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
            assert_eq!(text.len() as u64, v.serialized_len(&mut tys));
            assert_eq!(v.ty(&mut tys), t);
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
            let mut budget = u64::MAX;
            assert_eq!(common_ty(t, tn, &mut tys, &mut budget).ty, Some(t));
        });
    }

    /// The list `[[x]]` of depth `depth` around `x` of the type `t`, and its type. A list prints
    /// its element type, so no test here prints a text.
    fn deep_list(tys: &mut Types, depth: usize, x: Value, t: TyId) -> (Value, TyId) {
        let (mut v, mut elem) = (x, t);
        for _ in 0..depth {
            v = Value::List(elem, vec![v]);
            elem = tys.list(elem);
        }
        (v, elem)
    }

    /// The walks over a list and its type keep their own stacks: a typed use, `==`, and the
    /// join of two list types.
    #[test]
    fn the_walks_over_a_deep_list_do_not_recurse() {
        small_stack(|| {
            const DEPTH: usize = 100_000;
            let mut tys = Types::default();
            let (int, nat) = (tys.mk(Ty::Int), tys.mk(Ty::Nat));
            let (v, t) = deep_list(&mut tys, DEPTH, Value::Int(Int::from_u64(7)), int);
            let (_, tn) = deep_list(&mut tys, DEPTH, Value::Int(Int::from_u64(7)), nat);
            assert_eq!(v.ty(&mut tys), t);
            let w = v.clone();
            let mut fuel = Fuel::new(u64::MAX);
            let n = convert(tn, &v, &mut fuel, &tys);
            assert!(matches!(n, Ok(Some(_))));
            assert!(matches!(convert(t, &v, &mut fuel, &tys), Ok(None)));
            let eq = container_op(BinOp::Eq, &v, &w, &mut fuel, &mut tys);
            assert!(matches!(eq, Ok(Value::Bool(true))));
            let mut budget = u64::MAX;
            assert_eq!(common_ty(t, tn, &mut tys, &mut budget).ty, Some(t));
        });
    }

    /// A record of depth 100,000 around `Bool`: `S(k+1) { f: S(k) }`, and its struct type.
    fn deep_record(tys: &mut Types, depth: usize) -> (Value, TyId) {
        let mut ty = tys.mk(Ty::Bool);
        let mut value = Value::Bool(true);
        for k in 0..depth {
            let spec = tys.begin_spec(&format!("S{k}"), k, Vec::new());
            let (meta, deepest) = tys.struct_meta(spec, &[ty]);
            ty = tys.finish_spec(spec, vec![ty], meta, deepest);
            value = Value::Record(ty, vec![value]);
        }
        (value, ty)
    }

    /// The walks over a record and its struct type keep their own stacks too.
    #[test]
    fn the_walks_over_a_deep_record_do_not_recurse() {
        small_stack(|| {
            const DEPTH: usize = 100_000;
            let mut tys = Types::default();
            let (v, t) = deep_record(&mut tys, DEPTH);
            assert_eq!(v.size(), DEPTH as u64 + 1);
            assert_eq!(t.depth(), DEPTH as u64 + 1);
            assert_eq!(v.depth(), DEPTH as u64 + 2);
            assert_eq!(v.measure_charge(), DEPTH as u128);
            let text = v.serialize(&tys);
            assert_eq!(text.len() as u64, v.serialized_len(&mut tys));
            assert_eq!(v.ty(&mut tys), t);
            assert!(v.text(&tys).len() < 1100);
            assert!(tys.text(t).len() < 1100);
            let w = v.clone();
            let same = v == w;
            assert!(same);
            let mut fuel = Fuel::new(u64::MAX);
            let eq = container_op(BinOp::Eq, &v, &w, &mut fuel, &mut tys);
            assert!(matches!(eq, Ok(Value::Bool(true))));
            assert!(matches!(convert(t, &v, &mut fuel, &tys), Ok(None)));
            let zero = tys.zero(t).map(|z| z.serialize(&tys));
            assert_eq!(zero, Some(text.replace("(bool true)", "(bool false)")));
            assert!(format!("{v:?}").len() > DEPTH);
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

    /// A join that has fewer pairs in its budget than the fuel holds stops, and its units are
    /// above any fuel. The walk makes no more than the budget of pairs.
    #[test]
    fn a_join_stops_at_its_budget() {
        let mut tys = Types::default();
        let (int, byte) = (tys.mk(Ty::Int), tys.mk(Ty::UInt(8)));
        let (a, b) = (doubled(&mut tys, int, 100), doubled(&mut tys, byte, 100));
        let before = tys.work();
        let mut budget = 10;
        let done = common_ty(a, b, &mut tys, &mut budget);
        assert!(done.charge > Int::from_u64(u64::MAX));
        assert!(tys.work() - before <= 4 * 10 + 8, "{}", tys.work() - before);
    }

    /// Two doubled types of 100 levels join in work linear in the levels, not in their terms.
    #[test]
    fn a_join_of_shared_types_walks_each_pair_once() {
        let mut tys = Types::default();
        let (int, byte) = (tys.mk(Ty::Int), tys.mk(Ty::UInt(8)));
        let (a, b) = (doubled(&mut tys, int, 100), doubled(&mut tys, byte, 100));
        let before = tys.work();
        let mut budget = u64::MAX;
        let first = common_ty(a, b, &mut tys, &mut budget);
        assert_eq!(first.ty, Some(b));
        assert!(tys.work() - before <= 6 * 100, "{}", tys.work() - before);
        // Each of the 100 levels charges 1 for its pair and the units of its 2 parts.
        assert_eq!(
            first.charge,
            Int::from_u64(1).shl(100).sub(&Int::from_u64(1))
        );
        let again = tys.work();
        let second = common_ty(a, b, &mut tys, &mut budget);
        assert_eq!(second.ty, Some(b));
        assert_eq!(second.charge, first.charge);
        // The second join finds its pair in the table: one lookup.
        assert_eq!(tys.work(), again + 1);
    }
}
