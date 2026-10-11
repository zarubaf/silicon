// SPDX-License-Identifier: Apache-2.0
//! Hardware expressions for a wanted type.
//!
//! A wanted type holds the concrete type in each env and, when one exists,
//! a type expression that evaluates to it. An operator node gets operands
//! of the types that it needs. Each operator node has a hardware operand on
//! the left (or its only operand), so a node never folds to a static value.
//! A static value stands only where it converts: on the right of a binary
//! operator, as a call argument, and at the root of a typed slot.

use super::stat::int;
use super::{Builder, Ctx, Hw};
use crate::program::{HBin, HExpr, Scalar, Ty, Un};

/// The depth of a hardware expression.
pub(super) const DEPTH: u32 = 4;

/// A wanted type: the concrete type in each env of the env set, and a type
/// expression for it when one is known.
#[derive(Clone, Debug)]
pub(super) struct Want {
    pub(super) types: Vec<Scalar>,
    pub(super) ty: Option<Ty>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    Bool,
    UInt,
    SInt,
}

fn shape(t: Scalar) -> Shape {
    match t {
        Scalar::Bool => Shape::Bool,
        Scalar::UInt(_) => Shape::UInt,
        Scalar::SInt(_) => Shape::SInt,
    }
}

/// The type expression of a concrete type, with a literal width.
pub(super) fn literal_ty(t: Scalar) -> Ty {
    match t {
        Scalar::Bool => Ty::Bool,
        Scalar::UInt(w) => Ty::UInt(int(i64::from(w))),
        Scalar::SInt(w) => Ty::SInt(int(i64::from(w))),
    }
}

impl Want {
    pub(super) fn of(h: &Hw) -> Want {
        Want {
            types: h.types.clone(),
            ty: h.ty.clone(),
        }
    }

    /// The same concrete type in each of `envs` envs.
    pub(super) fn uniform(t: Scalar, envs: usize) -> Want {
        Want {
            types: vec![t; envs],
            ty: Some(literal_ty(t)),
        }
    }

    fn shape(&self) -> Option<Shape> {
        self.types.first().map(|t| shape(*t))
    }

    /// A type expression for the wanted type: the known one, or a literal
    /// one when all envs agree.
    pub(super) fn printable(&self) -> Option<Ty> {
        if let Some(t) = &self.ty {
            return Some(t.clone());
        }
        let first = *self.types.first()?;
        self.types
            .iter()
            .all(|t| *t == first)
            .then(|| literal_ty(first))
    }

    /// The type of the other signedness and the same width.
    fn flip(&self) -> Want {
        let types = self
            .types
            .iter()
            .map(|t| match t {
                Scalar::Bool => Scalar::Bool,
                Scalar::UInt(w) => Scalar::SInt(*w),
                Scalar::SInt(w) => Scalar::UInt(*w),
            })
            .collect();
        let ty = self.ty.as_ref().map(|t| match t {
            Ty::Bool => Ty::Bool,
            Ty::UInt(w) => Ty::SInt(w.clone()),
            Ty::SInt(w) => Ty::UInt(w.clone()),
        });
        Want { types, ty }
    }
}

impl Builder {
    /// A value for a typed slot: a hardware expression, or a static value
    /// that converts at the typed use. Choice 0 is the static value.
    pub(super) fn value(&mut self, ctx: &Ctx, w: &Want, depth: u32) -> HExpr {
        if self.tape.below(8) != 0
            && let Some(e) = self.hw(ctx, w, depth)
        {
            return e;
        }
        HExpr::Static(self.fit(&w.types, self.reach(ctx), &ctx.envs))
    }

    /// The value of an output or a register. One that reads no name takes
    /// a name in scope instead, so that the state and the outputs depend on
    /// the inputs, and a run tests hardware, not constants.
    pub(super) fn driver(&mut self, ctx: &Ctx, w: &Want) -> HExpr {
        let e = self.value(ctx, w, DEPTH);
        if reads_name(&e) {
            return e;
        }
        let Some(h) = ctx.hw.get(self.tape.index(ctx.hw.len())) else {
            return e;
        };
        adapt(h.expr.clone(), &Want::of(h), w).unwrap_or(e)
    }

    /// A hardware expression of the wanted type, or `None` when no leaf
    /// can have it (a type without an expression that differs by env and
    /// that no name in scope has).
    pub(super) fn hw(&mut self, ctx: &Ctx, w: &Want, depth: u32) -> Option<HExpr> {
        let shape = w.shape()?;
        let choice = if depth == 0 { 0 } else { self.tape.below(12) };
        let d = depth - u32::from(depth > 0);
        let built = match (shape, choice) {
            (Shape::Bool, 1) => self
                .hw(ctx, w, d)
                .map(|a| HExpr::Unary(Un::Not, Box::new(a))),
            (Shape::Bool, 2) => {
                let op = if self.tape.flag() {
                    HBin::Lor
                } else {
                    HBin::Land
                };
                self.binary(ctx, op, w, w, d)
            }
            (Shape::Bool, 3 | 4) => self.compare(ctx, d),
            (_, 5) => self.select(ctx, w, d),
            (_, 6) => self.call(ctx, w, d),
            (Shape::UInt | Shape::SInt, 1) => {
                let op = if self.tape.flag() { Un::Inv } else { Un::Neg };
                self.hw(ctx, w, d).map(|a| HExpr::Unary(op, Box::new(a)))
            }
            (Shape::UInt | Shape::SInt, 2) => {
                const OPS: [HBin; 6] = [
                    HBin::Addw,
                    HBin::Subw,
                    HBin::Mulw,
                    HBin::And,
                    HBin::Or,
                    HBin::Xor,
                ];
                let op = self.pick(&OPS);
                self.binary(ctx, op, w, w, d)
            }
            (Shape::UInt | Shape::SInt, 3) => self.shift(ctx, w, d),
            (Shape::UInt | Shape::SInt, 4) => self.resize(ctx, w, shape, d),
            (Shape::UInt | Shape::SInt, 7) => {
                let t = w.printable()?;
                let a = self.hw(ctx, &w.flip(), d)?;
                Some(HExpr::Reinterpret(t, Box::new(a)))
            }
            _ => None,
        };
        built.or_else(|| self.leaf(ctx, w, shape))
    }

    /// `a op b` with a hardware `a` of type `l` and a value `b` of type `r`.
    fn binary(&mut self, ctx: &Ctx, op: HBin, lhs: &Want, rhs: &Want, d: u32) -> Option<HExpr> {
        let a = self.hw(ctx, lhs, d)?;
        let mut b = self.value(ctx, rhs, d);
        // `x op x` is often a constant, so the right side becomes static.
        if a == b {
            b = HExpr::Static(self.fit(&rhs.types, self.reach(ctx), &ctx.envs));
        }
        Some(HExpr::Binary(op, Box::new(a), Box::new(b)))
    }

    /// A name of the wanted type, a name of another type that `adapt`
    /// converts, or a constant `T(k)`; for a Bool with no such name, a
    /// comparison. A leaf that reads a name keeps the outputs from being
    /// constants.
    fn leaf(&mut self, ctx: &Ctx, w: &Want, shape: Shape) -> Option<HExpr> {
        let names: Vec<&Hw> = ctx.hw.iter().filter(|h| h.types == w.types).collect();
        let by_name = !names.is_empty() && (shape == Shape::Bool || self.tape.below(4) != 3);
        if by_name {
            let i = self.tape.index(names.len());
            return names.get(i).map(|h| h.expr.clone());
        }
        if shape == Shape::Bool {
            return self.compare(ctx, 0);
        }
        // A finite name converts by `resize`; a Bool only selects constants.
        let finite: Vec<&Hw> = ctx
            .hw
            .iter()
            .filter(|h| h.types.first().is_some_and(|t| *t != Scalar::Bool))
            .collect();
        let others = if finite.is_empty() {
            ctx.hw.iter().collect()
        } else {
            finite
        };
        if self.tape.below(8) != 7
            && let Some(h) = others.get(self.tape.index(others.len()))
            && let Some(e) = adapt(h.expr.clone(), &Want::of(h), w)
        {
            return Some(e);
        }
        match w.printable() {
            Some(t) => Some(self.make(ctx, t, w)),
            None => names.first().map(|h| h.expr.clone()),
        }
    }

    /// The constant `T(k)` of the wanted type `t`.
    fn make(&mut self, ctx: &Ctx, t: Ty, w: &Want) -> HExpr {
        let k = self.fit(&w.types, self.reach(ctx), &ctx.envs);
        HExpr::Make(t, k)
    }

    /// The type of a name in scope with a shape that `keep` accepts, or a
    /// new literal type of the shape `fresh`.
    fn operand(&mut self, ctx: &Ctx, keep: impl Fn(Shape) -> bool, fresh: Shape) -> Want {
        let names: Vec<&Hw> = ctx
            .hw
            .iter()
            .filter(|h| h.types.first().is_some_and(|t| keep(shape(*t))))
            .collect();
        let i = self.tape.index(names.len() + 1);
        if let Some(h) = names.get(i) {
            return Want::of(h);
        }
        let w = self.tape.between(1, 16);
        let t = match fresh {
            Shape::Bool => Scalar::Bool,
            Shape::UInt => Scalar::UInt(w),
            Shape::SInt => Scalar::SInt(w),
        };
        Want::uniform(t, ctx.envs.len())
    }

    /// A comparison of two values of one type; a Bool has no ordering.
    fn compare(&mut self, ctx: &Ctx, d: u32) -> Option<HExpr> {
        const ORDER: [HBin; 6] = [HBin::Eq, HBin::Ne, HBin::Lt, HBin::Le, HBin::Gt, HBin::Ge];
        const EQUAL: [HBin; 2] = [HBin::Eq, HBin::Ne];
        // At depth 0 the operand is finite, so its leaf is a name or `T(k)`.
        let w = self.operand(ctx, |s| d > 0 || s != Shape::Bool, Shape::UInt);
        let op = if w.shape() == Some(Shape::Bool) {
            self.pick(&EQUAL)
        } else {
            self.pick(&ORDER)
        };
        self.binary(ctx, op, &w, &w, d)
    }

    /// A hardware `if` with hardware arms. Both front ends fold a
    /// comparison of two constants `T(k)` to a static Bool, and an `if` on a
    /// static Bool selects one arm; a static arm would then make the `if`
    /// static.
    fn select(&mut self, ctx: &Ctx, w: &Want, d: u32) -> Option<HExpr> {
        let boolean = Want::uniform(Scalar::Bool, ctx.envs.len());
        let cond = self.hw(ctx, &boolean, d)?;
        let then = self.hw(ctx, w, d)?;
        let els = self.hw(ctx, w, d)?;
        Some(HExpr::If(Box::new(cond), Box::new(then), Box::new(els)))
    }

    /// A call of a helper, converted to the wanted type by `adapt`.
    fn call(&mut self, ctx: &Ctx, w: &Want, d: u32) -> Option<HExpr> {
        let n = ctx.helpers.min(self.helpers.len());
        let h = self.helpers.get(self.tape.index(n))?;
        let (name, params, ret) = (h.name.clone(), h.params.clone(), h.ret.1);
        let args = params
            .iter()
            .map(|(_, _, t)| self.value(ctx, &Want::uniform(*t, ctx.envs.len()), d))
            .collect();
        let ret = Want::uniform(ret, ctx.envs.len());
        adapt(HExpr::Call(name, args), &ret, w)
    }

    /// `a << k` or `a >> k`: the count is static or a `UInt` value.
    fn shift(&mut self, ctx: &Ctx, w: &Want, d: u32) -> Option<HExpr> {
        let op = if self.tape.flag() {
            HBin::Shr
        } else {
            HBin::Shl
        };
        let a = self.hw(ctx, w, d)?;
        let k = if self.tape.flag() {
            let c = self.operand(ctx, |s| s == Shape::UInt, Shape::UInt);
            self.hw(ctx, &c, d)?
        } else {
            HExpr::Static(self.count(self.reach(ctx), &ctx.envs))
        };
        Some(HExpr::Binary(op, Box::new(a), Box::new(k)))
    }

    /// `resize(T, a)` with `a` of the same signedness.
    fn resize(&mut self, ctx: &Ctx, w: &Want, shape: Shape, d: u32) -> Option<HExpr> {
        let ty = w.printable()?;
        let from = self.operand(ctx, |s| s == shape, shape);
        let arg = self.hw(ctx, &from, d)?;
        Some(HExpr::Resize(ty, Box::new(arg)))
    }
}

/// `e` of type `from` as a value of type `to`: `resize` within one
/// signedness, `reinterpret` across, a Bool selects all zeros or all ones,
/// and a finite value gives its low bit as a Bool.
fn adapt(e: HExpr, from: &Want, to: &Want) -> Option<HExpr> {
    if from.types == to.types {
        return Some(e);
    }
    let (Some(have), Some(want)) = (from.shape(), to.shape()) else {
        return None;
    };
    if want == Shape::Bool {
        let bit = match have {
            Shape::Bool => return None,
            Shape::UInt => Ty::UInt(int(1)),
            Shape::SInt => Ty::SInt(int(1)),
        };
        let low = HExpr::Resize(bit, Box::new(e));
        let zero = HExpr::Static(int(0));
        return Some(HExpr::Binary(HBin::Ne, Box::new(low), Box::new(zero)));
    }
    let t = to.printable()?;
    match have {
        Shape::Bool => {
            let zero = HExpr::Make(t, int(0));
            let ones = HExpr::Unary(Un::Inv, Box::new(zero.clone()));
            Some(HExpr::If(Box::new(e), Box::new(zero), Box::new(ones)))
        }
        _ if have == want => Some(HExpr::Resize(t, Box::new(e))),
        _ => {
            let flipped = from.flip().printable()?;
            let e = HExpr::Reinterpret(flipped, Box::new(e));
            Some(HExpr::Resize(t, Box::new(e)))
        }
    }
}

/// Whether `e` reads a hardware name.
pub(super) fn reads_name(e: &HExpr) -> bool {
    match e {
        HExpr::Name(_) | HExpr::Field(..) => true,
        HExpr::Static(_) | HExpr::Make(..) => false,
        HExpr::Unary(_, a) | HExpr::Resize(_, a) | HExpr::Reinterpret(_, a) => reads_name(a),
        HExpr::Binary(_, a, b) => reads_name(a) || reads_name(b),
        HExpr::If(c, t, e) => reads_name(c) || reads_name(t) || reads_name(e),
        HExpr::Call(_, args) => args.iter().any(reads_name),
    }
}
