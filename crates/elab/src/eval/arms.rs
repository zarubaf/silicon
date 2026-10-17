// SPDX-License-Identifier: Apache-2.0
//! The arm walk of a hardware `if`, a hardware `match`, and a hardware equality (design section
//! 7.4): the positions of the walk with their own stack, the static parts of the arms, and the
//! leaves of an `if` and a `match`. The module `hwops` calls it and does not see its stack.

use super::hwops::{Side, hw_operands, lit_value_at};
use super::{Evaluator, Opnd, Res, at, fail};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Graph, HwId, Op, Val};
use crate::int::Int;
use crate::names::{Paths, Step};
use crate::ops::{self, Fuel, int_text};
use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use parse::ast::Pos;

/// A container position of the walk whose parts wait: the next part to visit and the count.
/// `sides` holds the container of each arm. A hardware equality has two sides.
pub(super) struct Level<'a> {
    pub(super) ty: TyId,
    pub(super) sides: Vec<Side<'a>>,
    pub(super) next: u64,
    pub(super) len: u64,
    /// The results of the parts so far, for a walk that builds a value, and the size, the depth,
    /// and the number of hardware leaves of each. A finished part keeps its numbers, so the node
    /// above it reads them and does not walk the part again.
    pub(super) parts: Vec<Agg>,
    pub(super) numbers: Vec<(u64, u64, u64)>,
}

impl Level<'_> {
    pub(super) fn push(&mut self, part: Agg, numbers: (u64, u64, u64)) {
        self.parts.push(part);
        self.numbers.push(numbers);
    }
}

/// The parts `part` of the sides of `top`, in constant work for each side. A scalar part type
/// `leaf` makes hardware leaves of a reference. The error is the index of the first side that
/// has no such part.
pub(super) fn part_sides<'a>(
    top: &Level<'a>,
    (part, step, offset, leaf, empty): (u64, &Step, u64, Option<&Ty>, bool),
    pos: Pos,
    (graph, paths): (&mut Graph, &mut Paths),
) -> Result<Vec<Side<'a>>, usize> {
    let idx = usize::try_from(part).unwrap_or(usize::MAX);
    let mut parts = Vec::with_capacity(top.sides.len());
    for (i, side) in top.sides.iter().enumerate() {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Sided, 1);
        match side.child(idx, (step, offset, leaf, empty), pos, (graph, paths)) {
            Some(child) => parts.push(child),
            None => return Err(i),
        }
    }
    Ok(parts)
}

/// The scalar type of a part type, if it is a data scalar.
pub(super) fn leaf_ty(t: &Ty) -> Option<Ty> {
    matches!(t, Ty::Bool | Ty::UInt(_) | Ty::SInt(_)).then(|| t.clone())
}

/// Whether arms of the type `t` join with the join charge and walk by the rules of section 7.4:
/// a container type, and an enum type (section 5.4).
fn arm_ty(t: &Ty) -> bool {
    ops::container_ty(t) || matches!(t, Ty::Enum(_))
}

/// The joined type of the two arms of a hardware `if`. Arms of a scalar type join with no
/// charge. Arms of a container type or of an enum type pay the join charge.
pub(super) fn arm_join(
    pos: Pos,
    (lhs, rhs): (&Side<'_>, &Side<'_>),
    (fuel, graph, tys): (&mut Fuel, &Graph, &mut Types),
) -> Res<TyId> {
    let (Some(lt), Some(rt)) = (lhs.ty(graph, tys), rhs.ty(graph, tys)) else {
        return arms_type("if", pos, &["a value".to_owned(), "a value".to_owned()], 0);
    };
    let joined = if arm_ty(tys.get(lt)) || arm_ty(tys.get(rt)) {
        let mut budget = fuel.left();
        let joined = ops::common_ty(lt, rt, tys, &mut budget);
        fuel.pay_joins(&joined.charge).map_err(at(pos))?;
        joined.ty
    } else {
        ops::scalar_join(lt, rt, tys)
    };
    match joined {
        Some(t) => Ok(t),
        None => arms_type("if", pos, &[lhs.text(graph, tys), rhs.text(graph, tys)], 0),
    }
}

/// What a position of the arm walk gives: the number of the parts of a container, or the
/// result of a position that has no parts.
enum Walked {
    Parts(u64),
    Done(Agg),
}

/// The position `sides` of the type `ty` by the rules 1 to 4 of section 7.4: a container
/// descends, `()` gives `()`, a data scalar is a leaf (`leaf`), and every other part is static
/// in each arm.
fn arm_pair(
    (kw, pos): (&str, Pos),
    leaf: &impl Fn(&Ty, &[Side<'_>], (&mut Fuel, &mut Graph, &mut Types)) -> Res<HwId>,
    ty: TyId,
    sides: &[Side<'_>],
    (fuel, graph, tys): (&mut Fuel, &mut Graph, &mut Types),
) -> Res<Walked> {
    Ok(match tys.get(ty) {
        Ty::Array(_, n) => Walked::Parts(n.to_u64().unwrap_or(u64::MAX)),
        Ty::Tuple(ts) => Walked::Parts(ts.len() as u64),
        Ty::Struct(_) | Ty::Enum(_) => {
            Walked::Parts(tys.parts(ty).map_or(0, |p| p.types.len() as u64))
        }
        Ty::Unit => Walked::Done(Agg::Static(Value::Unit)),
        Ty::Bool | Ty::UInt(_) | Ty::SInt(_) => {
            let t = tys.get(ty).clone();
            Walked::Done(Agg::Hw(leaf(&t, sides, (fuel, graph, tys))?))
        }
        _ => Walked::Done(Agg::Static(arm_static(
            (kw, pos),
            ty,
            sides,
            (fuel, graph, tys),
        )?)),
    })
}

/// The article and the noun of the arms of a hardware `kw`.
fn arms_noun(kw: &str) -> String {
    if kw == "if" {
        "an `if`".to_owned()
    } else {
        format!("a `{kw}`")
    }
}

/// `S010` at `pos` for the arms of a hardware `kw` with the texts `texts`, when the arm `i`
/// breaks the rule of one type. The text names the arm 0 and the arm `i`, or the arm 1 when `i`
/// is 0. Thus it names both arms of an `if`.
pub(super) fn arms_type<T>(kw: &str, pos: Pos, texts: &[String], i: usize) -> Res<T> {
    let text = |k: usize| texts.get(k).map_or("", String::as_str);
    fail(
        Code::S010,
        pos,
        format!(
            "the arms of {} have one type, not {} and {}",
            arms_noun(kw),
            text(0),
            text(i.max(1))
        ),
    )
}

/// The texts of the sides, for a message.
pub(super) fn side_texts(sides: &[Side<'_>], graph: &Graph, tys: &Types) -> Vec<String> {
    sides.iter().map(|side| side.text(graph, tys)).collect()
}

/// `S010` for the sides when the arm `i` breaks the rule of one type.
fn sides_type<T>(
    (kw, pos): (&str, Pos),
    sides: &[Side<'_>],
    i: usize,
    (graph, tys): (&Graph, &Types),
) -> Res<T> {
    arms_type(kw, pos, &side_texts(sides, graph, tys), i)
}

/// The text of a static side in the `S011` text of the arms (section 6.2). An integer is
/// decimal and bounded, a Boolean is `true` or `false`, and a finite value is its type with its
/// integer, for example `UInt[8](3)`. Another value is its text.
fn side_text(v: &Value, tys: &Types) -> String {
    match v {
        Value::Int(n) => int_text(n),
        Value::Bool(b) => b.to_string(),
        Value::UInt(x) => format!("UInt[{}]({})", x.width(), int_text(&Int::from_unsigned(x))),
        Value::SInt(x) => format!(
            "SInt[{}]({})",
            x.width(),
            int_text(&Int::from_signed(x, x.width()))
        ),
        v => v.text(tys),
    }
}

/// The static parts of the arms of a hardware `kw` (section 7.4) of the joined type `t`. Each
/// arm `y` after the first compares with the first arm `x` in arm order, and the compare
/// charges the sum of the two sizes, as a static equality does. Identical arms pass, so a
/// function compares by its item. Other arms compare by the static equality of `==`. Arms
/// identical to `x` give `x`. Else equal arms give the first arm of the joined type. Different
/// arms are `S011`, because a static part cannot depend on the hardware selection. Equal arms
/// without the joined type are also `S011`, because the walk makes no value conversion. The
/// text names `x` and the first arm that differs from it.
fn arm_static(
    (kw, pos): (&str, Pos),
    t: TyId,
    sides: &[Side<'_>],
    (fuel, graph, tys): (&mut Fuel, &Graph, &mut Types),
) -> Res<Value> {
    let mut values = Vec::with_capacity(sides.len());
    for (i, side) in sides.iter().enumerate() {
        match side.value() {
            Some(v) => values.push(v),
            None => return sides_type((kw, pos), sides, i, (graph, tys)),
        }
    }
    let Some((x, ys)) = values.split_first() else {
        return sides_type((kw, pos), sides, 0, (graph, tys));
    };
    let differ = |y: &Value, tys: &Types| {
        fail(
            Code::S011,
            pos,
            format!(
                "the arms of a hardware `{kw}` differ in a static part: {} and {}; give the \
                 part one value and type in each arm, or move it out of the `{kw}`",
                side_text(x, tys),
                side_text(y, tys)
            ),
        )
    };
    let mut odd: Option<&Value> = None;
    for y in ys {
        fuel.pay(u128::from(x.size()) + u128::from(y.size()))
            .map_err(at(pos))?;
        if *x == *y {
            continue;
        }
        if matches!(x, Value::Function(..)) {
            return differ(y, tys);
        }
        if !ops::same_pair(x, y, tys).map_err(at(pos))? {
            return differ(y, tys);
        }
        odd = odd.or(Some(y));
    }
    let Some(odd) = odd else {
        return Ok((**x).clone());
    };
    // The type walks enter only tuples, so the charge of the sizes covers them.
    for v in &values {
        if v.ty(tys) == t {
            return Ok((**v).clone());
        }
    }
    differ(odd, tys)
}

/// A leaf of a hardware `if` of the joined data scalar type `t`, with the arms `sides`. A
/// static leaf converts to `t`, also when both leaves are static. Then the `mux` node charges 1
/// plus 3. The walk gives an `if` two arms.
pub(super) fn if_leaf(
    pos: Pos,
    cond: HwId,
    t: &Ty,
    sides: &[Side<'_>],
    (fuel, graph, tys): (&mut Fuel, &mut Graph, &mut Types),
) -> Res<HwId> {
    let [lhs, rhs] = sides else {
        return sides_type(("if", pos), sides, 0, (graph, tys));
    };
    let pair = if let (Some(x), Some(y)) = (lhs.value(), rhs.value()) {
        let left = lit_value_at(pos, t, x, fuel, graph, tys)?;
        Some((left, lit_value_at(pos, t, y, fuel, graph, tys)?))
    } else {
        hw_operands(pos, (lhs, rhs), (fuel, graph, tys))?
    };
    let Some((left, right)) = pair else {
        return sides_type(("if", pos), sides, 0, (graph, tys));
    };
    let (ty, other) = (graph.ty(left), graph.ty(right));
    if ty != other {
        return arms_type("if", pos, &[tys.text_of(&ty), tys.text_of(&other)], 0);
    }
    fuel.pay(4).map_err(at(pos))?;
    Ok(graph.mk(pos, ty, Op::Mux, vec![cond, left, right]))
}

/// A leaf of the type `t` of a hardware `match` at `pos` with the selects `selects` and the arms
/// `sides` (section 5.4). A static leaf is a constant of `t`, also when each leaf is static. The
/// node `onehot` takes the `m` selects, then the `m` values, and charges `1 + 2m`.
pub(super) fn onehot_leaf(
    pos: Pos,
    selects: &[HwId],
    t: &Ty,
    sides: &[Side<'_>],
    (fuel, graph, tys): (&mut Fuel, &mut Graph, &mut Types),
) -> Res<HwId> {
    let mut args = selects.to_vec();
    for (i, side) in sides.iter().enumerate() {
        match (side.value(), side) {
            (Some(v), _) => args.push(lit_value_at(pos, t, v, fuel, graph, tys)?),
            (None, Side::Hw(h)) if graph.ty(*h) == *t => args.push(*h),
            _ => return sides_type(("match", pos), sides, i, (graph, tys)),
        }
    }
    fuel.pay(1 + args.len() as u128).map_err(at(pos))?;
    Ok(graph.mk(pos, t.clone(), Op::Onehot, args))
}

impl Evaluator<'_> {
    /// The walk of the arms `opnds` of a hardware `kw` at `pos` with the joined type `joined`,
    /// by the rules of section 7.4 in order. It charges the number of arms less 1 before it
    /// visits each position of a container root: 1 for an `if`. A scalar root gets no walk unit.
    /// A container descends into its positions in packing order, also a container that is not
    /// hardware data. An enum is a container with the parts `tag` and `payload`. Then it
    /// rebuilds the node in its normal form. `leaf` makes the node of a data scalar position.
    /// The walk keeps its own stack, and a reference never expands.
    pub(super) fn arm_walk(
        &mut self,
        (kw, pos): (&str, Pos),
        joined: TyId,
        opnds: &[&Opnd],
        leaf: &impl Fn(&Ty, &[Side<'_>], (&mut Fuel, &mut Graph, &mut Types)) -> Res<HwId>,
    ) -> Res<Val> {
        let root = matches!(
            self.tys.get(joined),
            Ty::Array(..) | Ty::Tuple(_) | Ty::Struct(_) | Ty::Enum(_)
        );
        let mut sides = Vec::with_capacity(opnds.len());
        for opnd in opnds {
            let Some(side) = Side::of_opnd(&self.store, opnd) else {
                return arms_type(kw, pos, &["a value".to_owned(), "a value".to_owned()], 0);
            };
            sides.push(side);
        }
        let units = (opnds.len() as u128).saturating_sub(1);
        let mut stack: Vec<Level<'_>> = Vec::new();
        let mut visit = Some((joined, sides));
        let mut delivered: Option<Agg>;
        loop {
            delivered = None;
            if let Some((ty, sides)) = visit.take() {
                if root {
                    self.fuel.pay(units).map_err(at(pos))?;
                    #[cfg(test)]
                    crate::counters::add(crate::counters::Count::Paired, 1);
                }
                let env = (&mut self.fuel, &mut self.graph, &mut self.tys);
                let len = match arm_pair((kw, pos), leaf, ty, &sides, env)? {
                    Walked::Parts(len) => Some(len),
                    Walked::Done(x) => {
                        delivered = Some(x);
                        None
                    }
                };
                if let Some(len) = len {
                    stack.push(Level {
                        ty,
                        sides,
                        next: 0,
                        len,
                        parts: Vec::new(),
                        numbers: Vec::new(),
                    });
                }
            }
            if let Some(part) = delivered.take() {
                let Some(top) = stack.last_mut() else {
                    return Ok(part.into_val());
                };
                let numbers = (
                    part.size(&self.graph, &self.tys),
                    part.depth(&self.tys),
                    part.leaves(&self.tys),
                );
                top.push(part, numbers);
            }
            let Some(top) = stack.last_mut() else {
                return arms_type(kw, pos, &["a value".to_owned(), "a value".to_owned()], 0);
            };
            if top.next >= top.len {
                let Some(done) = stack.pop() else {
                    return arms_type(kw, pos, &["a value".to_owned(), "a value".to_owned()], 0);
                };
                let len = done.parts.len();
                let Some(shape) = Agg::shape_from(&self.tys, done.ty, len, done.numbers) else {
                    return arms_type(kw, pos, &["a value".to_owned(), "a value".to_owned()], 0);
                };
                let numbers = (shape.size, shape.depth, shape.leaves);
                let node = Agg::finish(&self.tys, shape, done.parts);
                match stack.last_mut() {
                    Some(parent) => parent.push(node, numbers),
                    None => return Ok(node.into_val()),
                }
                continue;
            }
            let part = top.next;
            top.next += 1;
            let (ct, step, offset) = self.child_of(pos, top.ty, part)?;
            let leaf_ty = leaf_ty(self.tys.get(ct));
            let empty = leaf_ty.is_none() && self.tys.meta(ct).leaves.is_zero();
            let env = (&mut self.graph, &mut self.paths);
            let part = (part, &step, offset, leaf_ty.as_ref(), empty);
            match part_sides(top, part, pos, env) {
                Ok(sides) => visit = Some((ct, sides)),
                Err(i) => {
                    return sides_type((kw, pos), &top.sides, i, (&self.graph, &self.tys));
                }
            }
        }
    }
}
