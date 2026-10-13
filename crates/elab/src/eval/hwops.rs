// SPDX-License-Identifier: Apache-2.0
//! The hardware operations of Lean `Source.Eval`. A hardware operation makes one node and
//! charges 1 plus the number of its operands. Its operand trees are shared, so the work is
//! constant per node. A read of a handle and a lift of a static operand only refer, so they
//! charge nothing.
//!
//! A constant node copies a Boolean or a finite value. A finite value has at most 1024 words,
//! because a width is at most 65536, so the copy stays within a constant factor of the charge.

use super::{Evaluator, Opnd, Res, Store, at, fail};
use crate::Code;
use crate::agg::{Agg, Base};
use crate::hw::{Graph, HwId, Op, Seen, Val};
use crate::int::unsigned_size;
use crate::names::{Paths, Step};
use crate::ops::{self, Fuel, MAX_WIDTH, binop_text, int_text, unop_text};
use crate::types::{Ty, TyId, Types};
use crate::value::{Value, int_size};
use parse::ast::{BinOp, Pos, UnOp};
use resolve::Prelude;

/// The amount of a static shift count that the lowering reads: `min k 65536`.
fn amount(k: Option<u64>) -> u32 {
    let k = k.map_or(MAX_WIDTH, |k| k.min(MAX_WIDTH));
    u32::try_from(k).unwrap_or(u32::MAX)
}

/// A static value as a constant node. Only a Boolean and a finite value have a hardware type.
fn lit_of(pos: Pos, v: Value, graph: &mut Graph, tys: &Types) -> Res<HwId> {
    match v {
        Value::Bool(_) | Value::UInt(_) | Value::SInt(_) => {
            let ty = v.scalar_ty().unwrap_or(Ty::Bool);
            Ok(graph.mk(pos, ty, Op::Lit(v), Vec::new()))
        }
        v => fail(
            Code::S010,
            pos,
            format!(
                "hardware needs a Bool or a finite value, not {}",
                v.text(tys)
            ),
        ),
    }
}

/// The static value `v` as a constant node. A value that has no hardware type fails before its
/// copy.
fn lit_value(pos: Pos, v: &Value, graph: &mut Graph, tys: &Types) -> Res<HwId> {
    if !matches!(v, Value::Bool(_) | Value::UInt(_) | Value::SInt(_)) {
        return fail(
            Code::S010,
            pos,
            format!(
                "hardware needs a Bool or a finite value, not {}",
                v.text(tys)
            ),
        );
    }
    lit_of(pos, v.clone(), graph, tys)
}

/// The static value `v` next to a hardware operand of the type `t`. An integer takes the
/// type `t`, with the charge of its conversion.
fn lit_value_at(
    pos: Pos,
    t: &Ty,
    v: &Value,
    fuel: &mut Fuel,
    graph: &mut Graph,
    tys: &mut Types,
) -> Res<HwId> {
    if matches!(v, Value::Int(_)) && t.is_finite() {
        let t = tys.mk(t.clone());
        let converted = ops::convert(t, v, fuel, tys).map_err(at(pos))?;
        let v = converted.unwrap_or_else(|| v.clone());
        return lit_of(pos, v, graph, tys);
    }
    lit_value(pos, v, graph, tys)
}

/// One side of a pair in the walk of a hardware equality (section 7.4). It borrows the store,
/// so the walk copies no aggregate. A `Ref` is a reference that the walk made for a part.
enum Side<'a> {
    Val(&'a Value),
    Agg(&'a Agg),
    Hw(HwId),
    Ref(Base),
}

impl<'a> Side<'a> {
    /// The part in the form of the walk: a static part or a leaf is a value of its own.
    fn of_agg(a: &'a Agg) -> Side<'a> {
        match a {
            Agg::Static(v) => Side::Val(v),
            Agg::Hw(h) => Side::Hw(*h),
            a => Side::Agg(a),
        }
    }

    /// The operand as a side, or `None` for a handle and a literal that waits.
    fn of_opnd(store: &'a Store, o: &'a Opnd) -> Option<Side<'a>> {
        match o {
            Opnd::Hw(h) => Some(Side::Hw(*h)),
            Opnd::Static(out) => match store.seen(out) {
                Seen::Static(v) => Some(Side::Val(v)),
                Seen::Hw(h) => Some(Side::Hw(h)),
                Seen::Agg(a) => Some(Side::of_agg(a)),
                Seen::Handle(_) | Seen::Pending(..) => None,
            },
        }
    }

    /// The type of the side. A part that the walk made has none.
    fn ty(&self, g: &Graph, tys: &mut Types) -> Option<TyId> {
        match self {
            Side::Val(v) => Some(v.ty(tys)),
            Side::Hw(h) => Some(tys.mk(g.ty(*h))),
            Side::Agg(a) => Some(a.ty(g, tys)),
            Side::Ref(_) => None,
        }
    }

    fn text(&self, g: &Graph, tys: &Types) -> String {
        match self {
            Side::Val(v) => v.text(tys),
            Side::Hw(h) => format!("hardware {}", tys.text_of(&g.ty(*h))),
            Side::Agg(a) => a.stored_ty().map_or_else(
                || "hardware".to_owned(),
                |t| format!("hardware {}", tys.text(t)),
            ),
            Side::Ref(_) => "a part".to_owned(),
        }
    }

    /// The part `k` of the side, in constant work. A reference gives a reference to the part
    /// with the leaf field `step`, or a hardware leaf of the scalar type `leaf`, so it never
    /// expands. A stored node and a static container give the part they hold.
    fn child(
        &self,
        k: usize,
        step: &Step,
        leaf: Option<&Ty>,
        pos: Pos,
        (graph, paths, texts): (&mut Graph, &mut Paths, &[String]),
    ) -> Option<Side<'a>> {
        let base = match self {
            Side::Val(v) => {
                let v: &'a Value = v;
                return match v {
                    Value::Array(_, xs) | Value::Tuple(_, xs) | Value::Record(_, xs) => {
                        xs.get(k).map(Side::Val)
                    }
                    _ => None,
                };
            }
            Side::Agg(a) => {
                let a: &'a Agg = a;
                match a {
                    Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) => {
                        return p.0.get(k).map(Side::of_agg);
                    }
                    Agg::Ref(b, _) => b,
                    _ => return None,
                }
            }
            Side::Ref(b) => b,
            Side::Hw(_) => return None,
        };
        let sub = base.sub(paths, texts, step.clone());
        Some(match leaf {
            Some(t) => Side::Hw(graph.mk(pos, t.clone(), sub.op(), Vec::new())),
            None => Side::Ref(sub),
        })
    }
}

/// The units of the walk of a hardware equality: whether a static pair exists, whether all
/// static pairs are equal, and the `icmp eq` node of each leaf pair in walk order.
struct Pairs {
    statics: bool,
    equal: bool,
    nodes: Vec<HwId>,
}

/// A container pair of the walk whose parts wait: the next part to visit and the count.
struct Level<'a> {
    ty: TyId,
    a: Side<'a>,
    b: Side<'a>,
    next: u64,
    len: u64,
}

/// The message of two sides that have no common type.
fn no_common(op: BinOp, a: &str, b: &str) -> String {
    format!("`{}` needs a common type, not {a} and {b}", binop_text(op))
}

/// A static pair of the walk (section 7.4). It charges the sum of the two sizes, as a static
/// equality does, before it compares. Its result goes into `s`. The two types joined before
/// the walk, so the pair has two static values.
fn static_pair(
    pos: Pos,
    op: BinOp,
    (lhs, rhs): (&Side<'_>, &Side<'_>),
    pairs: &mut Pairs,
    (fuel, graph, tys): (&mut Fuel, &mut Graph, &mut Types),
) -> Res<()> {
    let (Side::Val(left), Side::Val(right)) = (lhs, rhs) else {
        let texts = (lhs.text(graph, tys), rhs.text(graph, tys));
        return fail(Code::S010, pos, no_common(op, &texts.0, &texts.1));
    };
    fuel.pay(u128::from(left.size()) + u128::from(right.size()))
        .map_err(at(pos))?;
    let equal = ops::same_pair(left, right, tys, fuel.left()).map_err(at(pos))?;
    pairs.statics = true;
    pairs.equal &= equal;
    Ok(())
}

/// A leaf pair of the walk: a pair of a data scalar type. Two static leaves are a static pair.
/// Another pair keeps the scalar rule of slice 1: a static leaf converts to the type of the
/// hardware leaf with its conversion charge, then the `icmp eq` node charges at the pair.
fn leaf_pair(
    pos: Pos,
    op: BinOp,
    (lhs, rhs): (&Side<'_>, &Side<'_>),
    pairs: &mut Pairs,
    (fuel, graph, tys): (&mut Fuel, &mut Graph, &mut Types),
) -> Res<()> {
    if let (Side::Val(_), Side::Val(_)) = (lhs, rhs) {
        return static_pair(pos, op, (lhs, rhs), pairs, (fuel, graph, tys));
    }
    let (left, right) = match (lhs, rhs) {
        (Side::Hw(x), Side::Hw(y)) => (*x, *y),
        (Side::Hw(hw), Side::Val(value)) => {
            let at_ty = graph.ty(*hw);
            (*hw, lit_value_at(pos, &at_ty, value, fuel, graph, tys)?)
        }
        (Side::Val(value), Side::Hw(hw)) => {
            let at_ty = graph.ty(*hw);
            (lit_value_at(pos, &at_ty, value, fuel, graph, tys)?, *hw)
        }
        _ => {
            let texts = (lhs.text(graph, tys), rhs.text(graph, tys));
            return fail(Code::S010, pos, no_common(op, &texts.0, &texts.1));
        }
    };
    let (ty, other) = (graph.ty(left), graph.ty(right));
    if ty != other {
        return fail(
            Code::S010,
            pos,
            format!(
                "`{}` does not accept {} and {}",
                binop_text(op),
                tys.text_of(&ty),
                tys.text_of(&other)
            ),
        );
    }
    fuel.pay(3).map_err(at(pos))?;
    pairs
        .nodes
        .push(graph.mk(pos, Ty::Bool, Op::Bin(BinOp::Eq), vec![left, right]));
    Ok(())
}

impl Evaluator<'_> {
    /// Makes a hardware node. It charges 1 plus the number of its operands.
    fn node(&mut self, pos: Pos, ty: Ty, op: Op, args: Vec<HwId>) -> Res<Val> {
        self.charge(pos, 1 + args.len() as u128)?;
        Ok(Val::Hw(self.graph.mk(pos, ty, op, args)))
    }

    /// A static value at a hardware use. Only a Boolean and a finite value have a hardware
    /// type.
    pub(super) fn lit(&mut self, pos: Pos, v: Value) -> Res<HwId> {
        lit_of(pos, v, &mut self.graph, &self.tys)
    }

    /// A static result at a hardware use. The copy of a constant is small, so a value that
    /// has no hardware type fails before its copy.
    fn lit_out(&mut self, pos: Pos, o: &super::Out) -> Res<HwId> {
        lit_value(pos, self.store.value(o), &mut self.graph, &self.tys)
    }

    /// A static operand next to a hardware operand of the type `t`. An integer takes the
    /// type `t`.
    fn lit_at(&mut self, pos: Pos, t: &Ty, o: &super::Out) -> Res<HwId> {
        let v = self.store.value(o);
        lit_value_at(pos, t, v, &mut self.fuel, &mut self.graph, &mut self.tys)
    }

    /// Two data operands as hardware. At least one of them is hardware.
    fn hw_pair(&mut self, pos: Pos, lhs: Opnd, rhs: Opnd) -> Res<(HwId, HwId)> {
        match (lhs, rhs) {
            (Opnd::Hw(left), Opnd::Hw(right)) => Ok((left, right)),
            (Opnd::Hw(left), Opnd::Static(right)) => {
                let ty = self.graph.ty(left);
                Ok((left, self.lit_at(pos, &ty, &right)?))
            }
            (Opnd::Static(left), Opnd::Hw(right)) => {
                let ty = self.graph.ty(right);
                Ok((self.lit_at(pos, &ty, &left)?, right))
            }
            (Opnd::Static(left), Opnd::Static(right)) => fail(
                Code::S010,
                pos,
                format!(
                    "expected data operands, not {} and {}",
                    self.store.value(&left).text(&self.tys),
                    self.store.value(&right).text(&self.tys)
                ),
            ),
        }
    }

    pub(super) fn hw_unary(&mut self, pos: Pos, op: UnOp, a: HwId) -> Res<Val> {
        let t = self.graph.ty(a);
        match (op, &t) {
            (UnOp::Not, Ty::Bool) => self.node(pos, Ty::Bool, Op::Un(op), vec![a]),
            (UnOp::Inv | UnOp::Neg, t) if t.is_finite() => {
                self.node(pos, t.clone(), Op::Un(op), vec![a])
            }
            _ => fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {}",
                    unop_text(op),
                    self.tys.text_of(&t)
                ),
            ),
        }
    }

    /// A shift with a hardware operand. A static count becomes an `Int` constant of the
    /// node, so the lowering can use the row "Shift by a static count" of section 7.4.
    fn hw_shift(&mut self, pos: Pos, op: BinOp, a: Opnd, b: &Opnd) -> Res<Val> {
        let count = match b {
            Opnd::Static(o) => match self.store.value(o) {
                Value::Int(k) if k.is_negative() => {
                    return fail(
                        Code::S013,
                        pos,
                        format!("the shift count {} is negative", int_text(k)),
                    );
                }
                Value::Int(k) => {
                    let (amount, size) = (amount(k.to_u64()), int_size(k));
                    self.graph
                        .mk(pos, Ty::Int, Op::Count { amount, size }, Vec::new())
                }
                Value::UInt(x) => {
                    let amount = crate::int::min_unsigned(x, 65536);
                    let size = unsigned_size(x);
                    self.graph
                        .mk(pos, Ty::Int, Op::Count { amount, size }, Vec::new())
                }
                v => {
                    return fail(
                        Code::S010,
                        pos,
                        format!(
                            "a shift count is UInt or a static Int, not {}",
                            v.text(&self.tys)
                        ),
                    );
                }
            },
            Opnd::Hw(c) => {
                let ty = self.graph.ty(*c);
                if matches!(ty, Ty::UInt(_)) {
                    *c
                } else {
                    return fail(
                        Code::S010,
                        pos,
                        format!(
                            "a shift count is UInt or a static Int, not {}",
                            self.tys.text_of(&ty)
                        ),
                    );
                }
            }
        };
        let left = match a {
            Opnd::Hw(x) => x,
            Opnd::Static(o) => self.lit_at(pos, &Ty::Bool, &o)?,
        };
        let t = self.graph.ty(left);
        if t.is_finite() {
            self.node(pos, t, Op::Bin(op), vec![left, count])
        } else {
            fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {}",
                    binop_text(op),
                    self.tys.text_of(&t)
                ),
            )
        }
    }

    /// A binary operator with at least one hardware operand. Both operands are data.
    pub(super) fn hw_binary(&mut self, pos: Pos, op: BinOp, lhs: Opnd, rhs: Opnd) -> Res<Val> {
        match op {
            BinOp::Shl | BinOp::Shr => return self.hw_shift(pos, op, lhs, &rhs),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "`{}` accepts only Int and Nat; hardware has `+%`, `-%`, and `*%`",
                        binop_text(op)
                    ),
                );
            }
            _ => {}
        }
        let (left, right) = self.hw_pair(pos, lhs, rhs)?;
        let (ty, other) = (self.graph.ty(left), self.graph.ty(right));
        let accepted = ty == other
            && match op {
                BinOp::Eq | BinOp::Ne => true,
                BinOp::Land | BinOp::Lor => ty == Ty::Bool,
                _ => ty.is_finite(),
            };
        if !accepted {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {} and {}",
                    binop_text(op),
                    self.tys.text_of(&ty),
                    self.tys.text_of(&other)
                ),
            );
        }
        let result = match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Land
            | BinOp::Lor
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge => Ty::Bool,
            _ => ty,
        };
        self.node(pos, result, Op::Bin(op), vec![left, right])
    }

    /// A hardware `if` with the condition `cond`. A static arm takes the type of the other
    /// arm. Both arms have one type. Two function arms are a static pair: they charge as a
    /// static equality, and one function item gives the static value. Two different functions
    /// are `S011`.
    pub(super) fn mux(&mut self, pos: Pos, cond: HwId, yes: Opnd, no: Opnd) -> Res<Val> {
        if let (Opnd::Static(y), Opnd::Static(n)) = (&yes, &no)
            && let (v @ Value::Function(i, _), w @ Value::Function(j, _)) =
                (self.store.value(y), self.store.value(n))
        {
            let (same, kept) = (i == j, v.clone());
            self.charge(pos, u128::from(v.size()) + u128::from(w.size()))?;
            if same {
                return Ok(Val::Static(kept));
            }
            return fail(
                Code::S011,
                pos,
                "the arms of a hardware `if` are two different functions".to_owned(),
            );
        }
        let (left, right) = match (yes, no) {
            (Opnd::Static(yes), Opnd::Static(no)) => {
                let yes_ty = self.store.value(&yes).finite_ty();
                let no_ty = self.store.value(&no).finite_ty();
                match (yes_ty, no_ty) {
                    (Some(ty), _) => {
                        let left = self.lit_out(pos, &yes)?;
                        (left, self.lit_at(pos, &ty, &no)?)
                    }
                    (_, Some(ty)) => {
                        let left = self.lit_at(pos, &ty, &yes)?;
                        (left, self.lit_out(pos, &no)?)
                    }
                    _ => {
                        let left = self.lit_out(pos, &yes)?;
                        (left, self.lit_out(pos, &no)?)
                    }
                }
            }
            (yes, no) => self.hw_pair(pos, yes, no)?,
        };
        let (ty, other) = (self.graph.ty(left), self.graph.ty(right));
        if ty == other {
            self.node(pos, ty, Op::Mux, vec![cond, left, right])
        } else {
            fail(
                Code::S010,
                pos,
                format!(
                    "the arms of an `if` have one type, not {} and {}",
                    self.tys.text_of(&ty),
                    self.tys.text_of(&other)
                ),
            )
        }
    }

    /// `==` or `!=` with a hardware aggregate operand (section 5.4). The function flag checked
    /// before. The two types join with the join charge (`S010` without a join). Then the walk
    /// visits the pairs by the joined type. After the walk, the chain of `and` nodes charges
    /// from `(const 1 s)` when static pairs exist, and `!=` adds an `xor` node last. A walk
    /// without a hardware pair gives a static `Bool`. The walk keeps its own stack and charges
    /// 1 before it visits each pair, so a reference of any size never expands.
    pub(super) fn agg_eq(&mut self, pos: Pos, op: BinOp, lhs: &Opnd, rhs: &Opnd) -> Res<Val> {
        let (Some(sa), Some(sb)) = (
            Side::of_opnd(&self.store, lhs),
            Side::of_opnd(&self.store, rhs),
        ) else {
            return fail(Code::S010, pos, no_common(op, "a value", "a value"));
        };
        let (graph, tys) = (&self.graph, &mut self.tys);
        let (Some(lhs_ty), Some(rhs_ty)) = (sa.ty(graph, tys), sb.ty(graph, tys)) else {
            return fail(Code::S010, pos, no_common(op, "a value", "a value"));
        };
        let mut budget = self.fuel.left();
        let joined = ops::common_ty(lhs_ty, rhs_ty, &mut self.tys, &mut budget);
        self.fuel.pay_int(&joined.charge).map_err(at(pos))?;
        let Some(joined) = joined.ty else {
            let texts = (
                sa.text(&self.graph, &self.tys),
                sb.text(&self.graph, &self.tys),
            );
            return fail(Code::S010, pos, no_common(op, &texts.0, &texts.1));
        };
        let mut pairs = Pairs {
            statics: false,
            equal: true,
            nodes: Vec::new(),
        };
        let mut stack: Vec<Level<'_>> = Vec::new();
        let mut visit = Some((joined, sa, sb));
        loop {
            if let Some((ty, a, b)) = visit.take() {
                self.fuel.pay(1).map_err(at(pos))?;
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Paired, 1);
                let len = match self.tys.get(ty) {
                    Ty::Array(_, n) => Some(n.to_u64().unwrap_or(u64::MAX)),
                    Ty::Tuple(ts) => Some(ts.len() as u64),
                    Ty::Struct(_) => Some(self.tys.fields(ty).map_or(0, |(_, fs)| fs.len() as u64)),
                    Ty::Unit => None,
                    Ty::Bool | Ty::UInt(_) | Ty::SInt(_) => {
                        let env = (&mut self.fuel, &mut self.graph, &mut self.tys);
                        leaf_pair(pos, op, (&a, &b), &mut pairs, env)?;
                        None
                    }
                    _ => {
                        let env = (&mut self.fuel, &mut self.graph, &mut self.tys);
                        static_pair(pos, op, (&a, &b), &mut pairs, env)?;
                        None
                    }
                };
                if let Some(len) = len {
                    stack.push(Level {
                        ty,
                        a,
                        b,
                        next: 0,
                        len,
                    });
                }
            }
            let Some(top) = stack.last_mut() else {
                break;
            };
            if top.next >= top.len {
                stack.pop();
                continue;
            }
            let part = top.next;
            top.next += 1;
            let (ct, step) = self.child_of(pos, top.ty, part)?;
            let leaf = match self.tys.get(ct) {
                scalar @ (Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) => Some(scalar.clone()),
                _ => None,
            };
            let idx = usize::try_from(part).unwrap_or(usize::MAX);
            let env = (&mut self.graph, &mut self.paths, &self.syms.texts[..]);
            let left = top.a.child(idx, &step, leaf.as_ref(), pos, env);
            let env = (&mut self.graph, &mut self.paths, &self.syms.texts[..]);
            let right = top.b.child(idx, &step, leaf.as_ref(), pos, env);
            let (Some(left), Some(right)) = (left, right) else {
                let texts = (
                    top.a.text(&self.graph, &self.tys),
                    top.b.text(&self.graph, &self.tys),
                );
                return fail(Code::S010, pos, no_common(op, &texts.0, &texts.1));
            };
            visit = Some((ct, left, right));
        }
        self.eq_chain(pos, op, pairs)
    }

    /// The result of the walk of a hardware equality: the chain of `and` nodes over the leaf
    /// pairs, in walk order. It charges 3 for each `and` node, after the walk. When a static
    /// pair exists, the chain starts from the free constant `s`. `!=` adds an `xor` node last.
    fn eq_chain(&mut self, pos: Pos, op: BinOp, r: Pairs) -> Res<Val> {
        let mut nodes = r.nodes.into_iter();
        let Some(first) = nodes.next() else {
            let same = if op == BinOp::Eq { r.equal } else { !r.equal };
            return Ok(Val::Static(Value::Bool(same)));
        };
        let (mut chain, mut next) = if r.statics {
            (self.lit(pos, Value::Bool(r.equal))?, Some(first))
        } else {
            (first, nodes.next())
        };
        while let Some(z) = next {
            self.charge(pos, 3)?;
            chain = self
                .graph
                .mk(pos, Ty::Bool, Op::Bin(BinOp::And), vec![chain, z]);
            next = nodes.next();
        }
        if op == BinOp::Eq {
            return Ok(Val::Hw(chain));
        }
        let one = self.lit(pos, Value::Bool(true))?;
        self.node(pos, Ty::Bool, Op::Bin(BinOp::Xor), vec![chain, one])
    }

    /// `resize` or `reinterpret` of a hardware value.
    pub(super) fn hw_convert(&mut self, pos: Pos, f: Prelude, to: TyId, arg: HwId) -> Res<Val> {
        let from = self.graph.ty(arg);
        let to = self.tys.get(to).clone();
        let to = &to;
        match (f, to, &from) {
            (Prelude::Resize, Ty::UInt(_), Ty::UInt(_))
            | (Prelude::Resize, Ty::SInt(_), Ty::SInt(_)) => {
                self.node(pos, to.clone(), Op::Resize, vec![arg])
            }
            (
                Prelude::Reinterpret,
                Ty::UInt(width) | Ty::SInt(width),
                Ty::UInt(old) | Ty::SInt(old),
            ) if old == width => self.node(pos, to.clone(), Op::Reinterpret, vec![arg]),
            _ => fail(
                Code::S010,
                pos,
                format!(
                    "no conversion of {} to {} here",
                    self.tys.text_of(&from),
                    self.tys.text_of(to)
                ),
            ),
        }
    }
}
