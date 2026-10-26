// SPDX-License-Identifier: Apache-2.0
//! Static candidates and the fallbacks of the static positions.
//!
//! A position takes a random candidate and evaluates it in each env of the
//! current env set. A candidate that faults, leaves the bounds of the
//! evaluator, or misses the predicate of its position gives way to a
//! fallback literal. So the predicate holds by evaluation, never by luck.

use super::{Builder, COUNT};
use crate::eval::{BOUND, Env, Value, eval};
use crate::program::{Radix, SBin, SExpr, STy, Scalar, Un};
use num_bigint::{BigInt, BigUint};

/// The depth of a static candidate.
pub(super) const DEPTH: u32 = 2;
/// The largest static shift count of a hardware shift.
const SHIFT: i64 = 70;

/// The kind of a static value. `Nat` is an `Int` kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Int,
    Bool,
    Str,
}

/// The kind of a scalar type, or `None` for a container.
pub(super) fn kind(t: &STy) -> Option<Kind> {
    match t {
        STy::Nat | STy::Int => Some(Kind::Int),
        STy::Bool => Some(Kind::Bool),
        STy::Str => Some(Kind::Str),
        STy::Fn(_)
        | STy::Tuple(_)
        | STy::Array(..)
        | STy::UInt(_)
        | STy::SInt(_)
        | STy::Record(_)
        | STy::Enum(_)
        | STy::List(_) => None,
    }
}

/// The kind of a parameter or a formal. Those are scalars by construction
/// (`STATIC_TYS`), so a container never reaches the `Int` arm.
pub(super) fn param_kind(t: &STy) -> Kind {
    kind(t).unwrap_or(Kind::Int)
}

/// What a candidate can read: the static names, how many `comptime fn`s
/// it can call, and the envs in which each call must evaluate (none in a
/// `comptime fn` body, where the sample check of the body covers calls).
#[derive(Clone, Copy)]
pub(super) struct Reach<'a> {
    pub(super) names: &'a [(String, STy)],
    pub(super) fns: usize,
    pub(super) envs: Option<&'a [Env]>,
}

pub(super) fn int(n: i64) -> SExpr {
    SExpr::Int(BigInt::from(n), Radix::Dec)
}

pub(super) fn bin(op: SBin, a: SExpr, b: SExpr) -> SExpr {
    SExpr::Binary(op, Box::new(a), Box::new(b))
}

/// The value range of a finite type, or `None` for `Bool`.
fn range(t: Scalar) -> Option<(BigInt, BigInt)> {
    match t {
        Scalar::Bool => None,
        Scalar::UInt(w) => Some((BigInt::ZERO, (BigInt::from(1) << w) - 1)),
        Scalar::SInt(w) => {
            let half = BigInt::from(1) << (w - 1);
            Some((-half.clone(), half - 1))
        }
    }
}

fn fits(v: &Value, t: Scalar) -> bool {
    match (v, range(t)) {
        (Value::Bool(_), None) => true,
        (Value::Int(n), Some((lo, hi))) => lo <= *n && *n <= hi,
        _ => false,
    }
}

fn int_in(v: &Value, lo: i64, hi: i64) -> bool {
    matches!(v, Value::Int(n) if BigInt::from(lo) <= *n && *n <= BigInt::from(hi))
}

impl Builder {
    /// A non-negative literal with a random spelling.
    pub(super) fn literal(&mut self, n: u64) -> SExpr {
        let radix = match self.tape.below(4) {
            2 => Radix::Hex,
            3 => Radix::Bin,
            _ => Radix::Dec,
        };
        SExpr::Int(BigInt::from(n), radix)
    }

    /// A literal from `lo` to `hi`.
    pub(super) fn number(&mut self, lo: u32, hi: u32) -> SExpr {
        let n = self.tape.between(lo, hi);
        self.literal(u64::from(n))
    }

    /// A small literal, sometimes negative.
    fn small(&mut self) -> SExpr {
        match self.number(0, 16) {
            SExpr::Int(n, radix) if self.tape.below(4) == 3 => SExpr::Int(-n, radix),
            lit => lit,
        }
    }

    /// A random static expression of `kind`.
    pub(super) fn sexpr(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> SExpr {
        if kind == Kind::Str {
            return self.string_expr(depth, r);
        }
        if let Some(m) = self.static_match_gate(kind, depth, r) {
            return m;
        }
        let names: Vec<&String> = r
            .names
            .iter()
            .filter(|(_, t)| self::kind(t) == Some(kind))
            .map(|(n, _)| n)
            .collect();
        let choice = if depth == 0 {
            self.tape.below(2)
        } else {
            self.tape.below(7)
        };
        let d = depth.saturating_sub(1);
        match (kind, choice) {
            (_, 1) if !names.is_empty() => {
                let i = self.tape.index(names.len());
                names.get(i).map_or(int(0), |n| SExpr::Name((*n).clone()))
            }
            (Kind::Int, 2) => {
                let op = if self.tape.flag() { Un::Inv } else { Un::Neg };
                SExpr::Unary(op, Box::new(self.sexpr(Kind::Int, d, r)))
            }
            (Kind::Bool, 2) => SExpr::Unary(Un::Not, Box::new(self.sexpr(Kind::Bool, d, r))),
            (Kind::Int, 3) => {
                const OPS: [SBin; 10] = [
                    SBin::Add,
                    SBin::Sub,
                    SBin::Mul,
                    SBin::Div,
                    SBin::Rem,
                    SBin::And,
                    SBin::Or,
                    SBin::Xor,
                    SBin::Shl,
                    SBin::Shr,
                ];
                let op = self.pick(&OPS);
                bin(op, self.sexpr(Kind::Int, d, r), self.sexpr(Kind::Int, d, r))
            }
            (Kind::Bool, 3) => self.relation(d, r),
            (_, 4) => {
                let cond = self.sexpr(Kind::Bool, d, r);
                let then = self.sexpr(kind, d, r);
                let els = self.sexpr(kind, d, r);
                SExpr::If(Box::new(cond), Box::new(then), Box::new(els))
            }
            (Kind::Int, 5) if r.fns > 0 => self.fn_call(d, r),
            (_, 6) => match self.exit(kind, d, r) {
                Some(e) => e,
                None => self.leaf_literal(kind),
            },
            _ => self.leaf_literal(kind),
        }
    }

    /// A literal of `kind`.
    pub(super) fn leaf_literal(&mut self, kind: Kind) -> SExpr {
        match kind {
            Kind::Int => self.small(),
            Kind::Bool => SExpr::Bool(self.tape.flag()),
            Kind::Str => self.string_literal(),
        }
    }

    /// A comparison, an equality of Bools, or `&&`/`||`.
    fn relation(&mut self, d: u32, r: Reach<'_>) -> SExpr {
        const ORDER: [SBin; 6] = [SBin::Eq, SBin::Ne, SBin::Lt, SBin::Le, SBin::Gt, SBin::Ge];
        const LOGIC: [SBin; 4] = [SBin::Land, SBin::Lor, SBin::Eq, SBin::Ne];
        if self.tape.below(6) == 0 {
            return self
                .string_exit(Kind::Bool, d + 1, r)
                .unwrap_or(SExpr::Bool(true));
        }
        if self.tape.flag() {
            let op = self.pick(&LOGIC);
            bin(
                op,
                self.sexpr(Kind::Bool, d, r),
                self.sexpr(Kind::Bool, d, r),
            )
        } else {
            let op = self.pick(&ORDER);
            bin(op, self.sexpr(Kind::Int, d, r), self.sexpr(Kind::Int, d, r))
        }
    }

    /// A call of one of the first `r.fns` `comptime fn`s. In an env set, a
    /// call whose count leaves `0..=COUNT` or that faults in an env takes
    /// the arguments of its base case, which the sample check covers.
    pub(super) fn fn_call(&mut self, d: u32, r: Reach<'_>) -> SExpr {
        let i = self.tape.index(r.fns);
        let Some((name, params)) = self.fns.get(i).map(|f| (f.name.clone(), f.params.clone()))
        else {
            return int(0);
        };
        // The count leans on small literals, so that most calls hold.
        let first = if self.tape.below(4) == 3 {
            self.sexpr(Kind::Int, d, r)
        } else {
            self.number(0, COUNT)
        };
        let rest: Vec<SExpr> = params
            .iter()
            .skip(1)
            .map(|(_, t)| self.sexpr(param_kind(t), d, r))
            .collect();
        let counted = r
            .envs
            .is_none_or(|envs| self.holds(&first, envs, |v| int_in(v, 0, i64::from(COUNT))));
        let call = SExpr::Call(name.clone(), std::iter::once(first).chain(rest).collect());
        let Some(envs) = r.envs else {
            return call;
        };
        note!(self, calls);
        if counted && self.holds(&call, envs, |_| true) {
            return call;
        }
        note!(self, call_fallbacks);
        let base = params
            .iter()
            .map(|(_, t)| match param_kind(t) {
                Kind::Int => int(0),
                Kind::Bool => SExpr::Bool(false),
                Kind::Str => SExpr::Str(String::new()),
            })
            .collect();
        SExpr::Call(name, base)
    }

    /// Whether `e` evaluates in each env and its values satisfy `pred`.
    pub(super) fn holds(&self, e: &SExpr, envs: &[Env], pred: impl Fn(&Value) -> bool) -> bool {
        self.values(e, envs).is_some_and(|vs| vs.iter().all(pred))
    }

    /// The value of `e` in each env, if none faults.
    pub(super) fn values(&self, e: &SExpr, envs: &[Env]) -> Option<Vec<Value>> {
        envs.iter()
            .map(|env| eval(e, env, &self.scope).ok())
            .collect()
    }

    /// A candidate that satisfies `pred` in each env, or `fallback`.
    fn position(
        &mut self,
        kind: Kind,
        r: Reach<'_>,
        envs: &[Env],
        pred: impl Fn(&Value) -> bool,
        fallback: impl FnOnce(&mut Builder) -> SExpr,
    ) -> (SExpr, bool) {
        let e = self.sexpr(kind, DEPTH, r);
        if self.holds(&e, envs, pred) {
            (e, false)
        } else {
            (fallback(self), true)
        }
    }

    /// A width in `UInt[e]`/`SInt[e]`: `1..=64` in each env, which keeps
    /// the designs small and far from the width limit of the language.
    pub(super) fn width(&mut self, r: Reach<'_>, envs: &[Env]) -> SExpr {
        let names: Vec<String> = r
            .names
            .iter()
            .filter(|(_, t)| *t == STy::Nat)
            .map(|(n, _)| n.clone())
            .collect();
        // Widths lean on `Nat` names, so that most candidates hold.
        let e = match self.tape.below(5) {
            0 => return self.number(1, 16),
            1 | 2 if !names.is_empty() => {
                let i = self.tape.index(names.len());
                let Some(n) = names.get(i).cloned().map(SExpr::Name) else {
                    return self.number(1, 16);
                };
                if self.tape.flag() {
                    n
                } else {
                    let k = self.number(1, 8);
                    bin(SBin::Add, n, k)
                }
            }
            _ => self.sexpr(Kind::Int, DEPTH, r),
        };
        note!(self, widths);
        if self.holds(&e, envs, |v| int_in(v, 1, 64)) {
            return e;
        }
        note!(self, width_fallbacks);
        self.number(1, 16)
    }

    /// A static value that fits the type `types[i]` in env `i`: a `T(k)`
    /// argument, a reset value, or a static leaf next to a finite operand.
    pub(super) fn fit(&mut self, types: &[Scalar], r: Reach<'_>, envs: &[Env]) -> SExpr {
        let kind = match types.first() {
            Some(Scalar::Bool) => Kind::Bool,
            _ => Kind::Int,
        };
        let e = self.sexpr(kind, DEPTH, r);
        let ok = self
            .values(&e, envs)
            .is_some_and(|vs| vs.iter().zip(types).all(|(v, t)| fits(v, *t)));
        if ok {
            return e;
        }
        if kind == Kind::Bool {
            return SExpr::Bool(false);
        }
        // `0` fits each type; the tape picks up to the smallest maximum.
        let max = types
            .iter()
            .filter_map(|t| range(*t).map(|(_, hi)| hi))
            .min()
            .and_then(|hi| u32::try_from(hi.min(BigInt::from(BOUND))).ok())
            .unwrap_or(0);
        let k = self.tape.below(max.saturating_add(1));
        self.literal(u64::from(k))
    }

    /// The count of a hardware shift: `0..=SHIFT` in each env.
    pub(super) fn count(&mut self, r: Reach<'_>, envs: &[Env]) -> SExpr {
        self.position(
            Kind::Int,
            r,
            envs,
            |v| int_in(v, 0, SHIFT),
            |b| b.number(0, 8),
        )
        .0
    }

    /// The bounds of a `comptime for`: `-2 <= lo <= 4` and
    /// `0 <= hi - lo <= 4` in each env.
    pub(super) fn bounds(&mut self, r: Reach<'_>, envs: &[Env]) -> (SExpr, SExpr) {
        let (lo, _) = self.position(Kind::Int, r, envs, |v| int_in(v, -2, 4), |b| b.number(0, 2));
        let hi = self.sexpr(Kind::Int, DEPTH, r);
        let span = bin(SBin::Sub, hi.clone(), lo.clone());
        if self.holds(&span, envs, |v| int_in(v, 0, 4)) {
            return (lo, hi);
        }
        // The fallback loop runs: the candidate already gives empty loops.
        let k = self.number(1, 4);
        (lo.clone(), bin(SBin::Add, lo, k))
    }

    /// A static Bool that evaluates in each env: a `comptime if` condition.
    pub(super) fn condition(&mut self, r: Reach<'_>, envs: &[Env]) -> SExpr {
        self.position(Kind::Bool, r, envs, |_| true, |_| SExpr::Bool(true))
            .0
    }

    /// A `static_assert` condition: true in each env.
    pub(super) fn assertion(&mut self, r: Reach<'_>, envs: &[Env]) -> SExpr {
        self.position(
            Kind::Bool,
            r,
            envs,
            |v| *v == Value::Bool(true),
            |_| SExpr::Bool(true),
        )
        .0
    }

    /// A static value of `kind` that evaluates in each env, with its values
    /// and the fallback `0` or `false`.
    pub(super) fn evaluated(
        &mut self,
        kind: Kind,
        r: Reach<'_>,
        envs: &[Env],
    ) -> (SExpr, Vec<Value>) {
        let e = self.sexpr(kind, DEPTH, r);
        if let Some(vs) = self.values(&e, envs) {
            return (e, vs);
        }
        let (e, v) = match kind {
            Kind::Int => (int(0), Value::Int(BigInt::ZERO)),
            Kind::Bool => (SExpr::Bool(false), Value::Bool(false)),
            Kind::Str => Builder::empty_string(),
        };
        (e, vec![v; envs.len()])
    }

    /// An argument for a parameter of type `t`: `Nat` in `1..=12`, `Int` in
    /// `-6..=6`, or a Bool, in each env.
    pub(super) fn argument(&mut self, t: &STy, r: Reach<'_>, envs: &[Env]) -> SExpr {
        if matches!(t, STy::UInt(_) | STy::SInt(_)) {
            return self.finite_argument(t, r, envs);
        }
        if let STy::Fn(ft) = t {
            note!(self, fn_arguments);
            return self.fn_argument(ft);
        }
        let (lo, hi) = arg_range(t);
        self.position(
            param_kind(t),
            r,
            envs,
            |v| match t {
                STy::Bool => true,
                _ => int_in(v, lo, hi),
            },
            |b| value_expr(&b.top_value(t)),
        )
        .0
    }

    /// A random value in the range of a parameter of type `t`.
    pub(super) fn top_value(&mut self, t: &STy) -> Value {
        match t {
            STy::Bool => Value::Bool(self.tape.flag()),
            STy::Nat => Value::Int(BigInt::from(self.tape.between(1, 12))),
            STy::Int => {
                // 0, 1, -1, 2, -2, ...: choice 0 is the simplest.
                let k = i64::from(self.tape.below(13));
                let n = if k % 2 == 1 { (k + 1) / 2 } else { -(k / 2) };
                Value::Int(BigInt::from(n))
            }
            STy::Tuple(ts) => Value::Tuple(ts.iter().map(|t| self.top_value(t)).collect()),
            STy::Array(t, n) => Value::Array((0..*n).map(|_| self.top_value(t)).collect()),
            STy::UInt(w) => Value::UInt(*w, self.finite_value(t, 3)),
            STy::SInt(w) => Value::SInt(*w, self.finite_value(t, 3)),
            STy::Str => Value::Str(String::new()),
            STy::Fn(f) => Value::Function(String::new(), (**f).clone()),
            STy::List(t) => Value::List((**t).clone(), Vec::new()),
            STy::Record(r) => Value::Record(
                r.clone(),
                r.fields.iter().map(|(_, t)| self.top_value(t)).collect(),
            ),
            STy::Enum(d) => Value::Enum(d.clone(), BigUint::ZERO, BigUint::ZERO),
        }
    }
}

impl Builder {
    /// The type of a module parameter that takes a finite integer. The
    /// widths reach 257, so a value passes `2^256` (spec 7.1).
    pub(super) fn finite_param_ty(&mut self) -> STy {
        const WIDTHS: [u32; 8] = [1, 2, 3, 4, 8, 16, 64, 257];
        let w = self.pick(&WIDTHS);
        if self.tape.flag() {
            STy::UInt(w)
        } else {
            STy::SInt(w)
        }
    }

    /// A value of the finite type `t`: at most `small` in magnitude for most
    /// choices, and the edges of the type otherwise. A wide type also takes
    /// values on both sides of the 64 bytes of a readable name.
    pub(super) fn finite_value(&mut self, t: &STy, small: u32) -> BigInt {
        let (STy::UInt(w) | STy::SInt(w)) = t else {
            return BigInt::ZERO;
        };
        let (signed, w) = (matches!(t, STy::SInt(_)), *w);
        let one = BigInt::from(1);
        let (lo, hi): (BigInt, BigInt) = if signed {
            (-(one.clone() << (w - 1)), (one.clone() << (w - 1)) - 1)
        } else {
            (BigInt::ZERO, (one.clone() << w) - 1)
        };
        let n = match self.tape.below(8) {
            0 => BigInt::ZERO,
            1 => one.clone(),
            2 => hi.clone(),
            3 => lo.clone(),
            4 if signed => -one.clone(),
            5 if w > 210 => one.clone() << 200,
            6 if w > 210 => one << 210,
            _ => BigInt::from(self.tape.below(small + 1)),
        };
        n.clamp(lo, hi)
    }

    /// A module argument for the finite parameter type `t`: a literal or a
    /// candidate that fits, with or without the conversion `T(e)`. Both
    /// spellings name one instantiation (#188).
    fn finite_argument(&mut self, t: &STy, r: Reach<'_>, envs: &[Env]) -> SExpr {
        let n = self.finite_value(t, 12);
        let literal = self.finite_literal(n);
        let candidate = self.sexpr(Kind::Int, 1, r);
        let body = if self.tape.below(4) == 0
            && self.holds(&candidate, envs, |v| {
                crate::eval::convert(t, v.clone()).is_ok()
            }) {
            candidate
        } else {
            literal
        };
        self.conversion(t, body)
    }

    /// The argument that spells the value `v` of the parameter type `t`
    /// again, so that a context of the module is reached under a second
    /// spelling.
    pub(super) fn respelled(&mut self, t: &STy, v: &Value) -> SExpr {
        match v {
            Value::UInt(_, n) | Value::SInt(_, n) => {
                let literal = self.finite_literal(n.clone());
                self.conversion(t, literal)
            }
            v => value_expr(v),
        }
    }

    /// A literal of `n` with a random spelling; a negative one has one.
    pub(super) fn finite_literal(&mut self, n: BigInt) -> SExpr {
        let radix = match self.tape.below(4) {
            2 => Radix::Hex,
            3 => Radix::Bin,
            _ => Radix::Dec,
        };
        if n.sign() == num_bigint::Sign::Minus {
            SExpr::Int(n, Radix::Dec)
        } else {
            SExpr::Int(n, radix)
        }
    }

    /// `body`, or `T(body)`. A literal above the bound of the evaluator
    /// stands only inside a conversion.
    fn conversion(&mut self, t: &STy, body: SExpr) -> SExpr {
        let wide = matches!(&body, SExpr::Int(n, _) if n.magnitude() > &BigUint::from(BOUND));
        if wide || self.tape.flag() {
            note!(self, converted_args);
            SExpr::Convert(t.clone(), Box::new(body))
        } else {
            body
        }
    }
}

/// The range of a module argument of type `t`. Port widths hold over
/// the whole range, so every argument tuple gives valid ports.
pub(super) fn arg_range(t: &STy) -> (i64, i64) {
    match t {
        STy::Nat => (1, 12),
        STy::Int => (-6, 6),
        STy::Bool => (0, 1),
        STy::Tuple(_)
        | STy::Array(..)
        | STy::UInt(_)
        | STy::SInt(_)
        | STy::Record(_)
        | STy::Enum(_)
        | STy::Str
        | STy::Fn(_)
        | STy::List(_) => (0, 0),
    }
}

/// A literal for a value.
pub(super) fn value_expr(v: &Value) -> SExpr {
    match v {
        Value::Bool(b) => SExpr::Bool(*b),
        Value::Tuple(xs) => SExpr::Tuple(xs.iter().map(value_expr).collect()),
        Value::Array(xs) => SExpr::Array(xs.iter().map(value_expr).collect()),
        Value::Int(n) => SExpr::Int(n.clone(), Radix::Dec),
        // The conversion keeps the type and lets a wide literal stand.
        Value::UInt(_, n) | Value::SInt(_, n) => {
            SExpr::Convert(v.ty(), Box::new(SExpr::Int(n.clone(), Radix::Dec)))
        }
        Value::Str(s) => SExpr::Str(s.clone()),
        Value::Function(item, _) => SExpr::Name(item.clone()),
        Value::List(t, _) => SExpr::NewList(t.clone()),
        Value::Enum(def, ..) => SExpr::Unpack(
            def.name.clone(),
            Box::new(SExpr::BitsConv(
                def.name.clone(),
                Box::new(SExpr::Int(BigInt::from(v.bits()), Radix::Dec)),
            )),
        ),
        Value::Record(rt, xs) => {
            let targs = rt.args.iter().map(value_expr).collect();
            if rt.zeroable() && xs.iter().all(is_zero) {
                SExpr::Zero(rt.name.clone(), targs)
            } else {
                SExpr::Record(rt.name.clone(), targs, xs.iter().map(value_expr).collect())
            }
        }
    }
}

/// Whether `v` is the zero of its type: `0` or `false`.
fn is_zero(v: &Value) -> bool {
    match v {
        Value::Int(n) | Value::UInt(_, n) | Value::SInt(_, n) => *n == BigInt::ZERO,
        Value::Bool(b) => !b,
        Value::Tuple(xs) | Value::Array(xs) | Value::Record(_, xs) => xs.iter().all(is_zero),
        Value::Function(..) => false,
        Value::Enum(_, tag, payload) => *tag == BigUint::ZERO && *payload == BigUint::ZERO,
        Value::Str(s) => s.is_empty(),
        Value::List(_, xs) => xs.is_empty(),
    }
}
