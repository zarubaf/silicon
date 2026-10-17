// SPDX-License-Identifier: Apache-2.0
//! Static containers: tuple, array, and record types, literals, and the
//! scalar exits that bring a leaf back to a static position.
//!
//! A container leaves a static position only through an exit: an index,
//! a selector `.N`, a field, `len`, or `data_bits`. An index is a static position, so each index
//! is in range in each env of the env set, or it falls back to a literal.

use super::stat::{self, Kind, Reach, bin, int};
use super::{Builder, CONTAINER_LEN, CONTAINER_LEVELS};
use crate::eval::{Env, Value};
use crate::program::{Radix, SBin, SExpr, STy};

/// Whether a leaf of `kind` is inside `t`.
fn has_leaf(t: &STy, kind: Kind) -> bool {
    match t {
        STy::Nat | STy::Int => kind == Kind::Int,
        STy::Bool => kind == Kind::Bool,
        STy::Tuple(ts) => ts.iter().any(|t| has_leaf(t, kind)),
        STy::Array(t, _) => has_leaf(t, kind),
        STy::Record(r) => r.fields.iter().any(|(_, t)| has_leaf(t, kind)),
        STy::List(t) => kind == Kind::Int || has_leaf(t, kind),
        STy::UInt(_) | STy::SInt(_) | STy::Str | STy::Fn(_) | STy::Enum(_) => false,
    }
}

impl Builder {
    /// The type of a static container binding: a record, or a tuple or an
    /// array.
    pub(super) fn static_container_ty(&mut self) -> STy {
        if !self.structs.is_empty()
            && self.tape.below(3) == 0
            && let Some(record) = self.record_ty()
        {
            return record;
        }
        self.container_ty(CONTAINER_LEVELS)
    }

    /// A tuple or an array type with at most `levels` levels of nesting,
    /// a record counting for two (itself and its field container).
    /// Choice 0 is the shortest tuple of one `Int`.
    pub(super) fn container_ty(&mut self, levels: u32) -> STy {
        if self.tape.flag() {
            let n = self.tape.between(1, CONTAINER_LEN);
            STy::Tuple((0..n).map(|_| self.element_ty(levels)).collect())
        } else {
            let n = self.tape.between(1, CONTAINER_LEN);
            STy::Array(Box::new(self.element_ty(levels)), n)
        }
    }

    /// The type of an element: a scalar, a record, or a container one
    /// level deeper.
    fn element_ty(&mut self, levels: u32) -> STy {
        if levels >= 3
            && !self.structs.is_empty()
            && self.tape.below(6) == 5
            && let Some(record) = self.record_ty()
        {
            return record;
        }
        if levels > 1 && self.tape.below(4) == 3 {
            return self.container_ty(levels - 1);
        }
        if self.tape.below(3) == 2 {
            STy::Bool
        } else {
            STy::Int
        }
    }

    /// A container of the type `t`. Each leaf holds in each env of `envs`
    /// (none: a `comptime fn` body, where the sample check covers it), or
    /// it takes a literal.
    pub(super) fn container(&mut self, t: &STy, depth: u32, r: Reach<'_>) -> SExpr {
        match t {
            STy::Tuple(ts) => {
                note!(self, tuples);
                SExpr::Tuple(ts.iter().map(|t| self.container(t, depth, r)).collect())
            }
            STy::Array(t, n) => {
                note!(self, arrays);
                SExpr::Array((0..*n).map(|_| self.container(t, depth, r)).collect())
            }
            STy::Record(rt) => self.record(rt, depth, r),
            STy::Str => self.string_literal(),
            STy::List(t) => SExpr::NewList((**t).clone()),
            STy::Enum(def) => SExpr::Zero(def.name.clone(), Vec::new()),
            STy::Bool => self.element(Kind::Bool, depth, r),
            STy::Nat | STy::Int | STy::UInt(_) | STy::SInt(_) | STy::Fn(_) => {
                self.element(Kind::Int, depth, r)
            }
        }
    }

    /// A scalar leaf of a container literal.
    fn element(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> SExpr {
        note!(self, leaves);
        let e = self.sexpr(kind, depth, r);
        if r.envs.is_none_or(|envs| self.values(&e, envs).is_some()) {
            return e;
        }
        note!(self, leaf_fallbacks);
        match kind {
            Kind::Int => self.number(0, 16),
            Kind::Bool => SExpr::Bool(self.tape.flag()),
            Kind::Str => self.string_literal(),
        }
    }

    /// A scalar of `kind` from a container: a name of `r` or a fresh
    /// literal, then a chain of indexes and selectors down to a leaf, or
    /// `len` of an array. `None` if no container has such a leaf.
    pub(super) fn exit(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> Option<SExpr> {
        if kind == Kind::Int
            && self.tape.below(8) == 0
            && let Some(bits) = self.data_bits(r)
        {
            return Some(bits);
        }
        if kind != Kind::Str && self.tape.below(5) == 0 {
            return self.string_exit(kind, depth, r);
        }
        if kind != Kind::Str
            && self.tape.below(5) == 0
            && let Some(call) = self.value_call(kind, depth, r)
        {
            return Some(call);
        }
        let names: Vec<(&String, &STy)> = r
            .names
            .iter()
            .filter(|(_, t)| t.is_container() && has_leaf(t, kind))
            .map(|(n, t)| (n, t))
            .collect();
        if names.is_empty() || (depth > 0 && self.tape.below(4) == 3) {
            return self.literal_exit(kind, depth, r);
        }
        // A list is one container among many names; it gets a larger share.
        let lists: Vec<(&String, &STy)> = names
            .iter()
            .copied()
            .filter(|(_, t)| matches!(t, STy::List(_)))
            .collect();
        let pool = if !lists.is_empty() && self.tape.flag() {
            lists
        } else {
            names
        };
        let (name, t) = *pool.get(self.tape.index(pool.len()))?;
        self.descend(SExpr::Name(name.clone()), t, kind, depth, r)
    }

    /// A container as the `eval` probe, so that its serialization is
    /// compared: a container `const`, or a fresh literal. Choice 0 and a
    /// tape of no container leave the probe to the scalar forms.
    pub(super) fn container_probe(
        &mut self,
        names: &[(String, STy)],
        envs: &[Env],
    ) -> Option<SExpr> {
        let consts: Vec<&String> = names
            .iter()
            .filter(|(_, t)| t.is_container())
            .map(|(n, _)| n)
            .collect();
        if self.aside(4) {
            let r = Reach {
                names,
                fns: 0,
                envs: Some(envs),
            };
            if let Some((_, value)) = self.any_enum_value(r) {
                note!(self, enum_probes);
                return Some(value);
            }
        }
        match self.tape.below(6) {
            2 => consts
                .get(self.tape.index(consts.len()))
                .map(|n| SExpr::Name((*n).clone())),
            4 => {
                let r = Reach {
                    names,
                    fns: 0,
                    envs: Some(envs),
                };
                Some(self.sexpr(Kind::Str, stat::DEPTH, r))
            }
            5 => self.list_probe(),
            3 => {
                let t = self.static_container_ty();
                let r = Reach {
                    names,
                    fns: 0,
                    envs: Some(envs),
                };
                Some(self.container(&t, stat::DEPTH, r))
            }
            _ => None,
        }
    }

    /// The length of the shortest value of the list `base` over the envs of
    /// `r`, if it is at least 1.
    fn shortest(&self, base: &SExpr, r: Reach<'_>) -> Option<u32> {
        let default = [Env::default()];
        let envs = r.envs.unwrap_or(&default);
        let lens = self.values(&SExpr::Len(Box::new(base.clone())), envs)?;
        let mut shortest = u32::MAX;
        for v in &lens {
            let Value::Int(n) = v else { return None };
            shortest = shortest.min(u32::try_from(n).ok()?);
        }
        (1..u32::MAX).contains(&shortest).then_some(shortest)
    }

    /// An exit from a fresh literal, for example `[1, x][0]`.
    fn literal_exit(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> Option<SExpr> {
        if depth == 0 {
            return None;
        }
        let t = with_leaf(self.container_ty(CONTAINER_LEVELS), kind);
        let lit = self.container(&t, depth - 1, r);
        self.descend(lit, &t, kind, depth - 1, r)
    }

    pub(super) fn descend(
        &mut self,
        base: SExpr,
        t: &STy,
        kind: Kind,
        depth: u32,
        r: Reach<'_>,
    ) -> Option<SExpr> {
        match t {
            STy::Nat | STy::Int | STy::Bool => Some(base),
            STy::Tuple(ts) => {
                let ks: Vec<usize> = (0..ts.len())
                    .filter(|&k| ts.get(k).is_some_and(|t| has_leaf(t, kind)))
                    .collect();
                let k = *ks.get(self.tape.index(ks.len()))?;
                let radix = match self.tape.below(4) {
                    2 => Radix::Hex,
                    3 => Radix::Bin,
                    _ => Radix::Dec,
                };
                note!(self, selects);
                let sel = SExpr::Select(Box::new(base), u32::try_from(k).ok()?, radix);
                self.descend(sel, ts.get(k)?, kind, depth, r)
            }
            STy::Record(rt) => {
                let ks: Vec<usize> = (0..rt.fields.len())
                    .filter(|&k| rt.fields.get(k).is_some_and(|(_, t)| has_leaf(t, kind)))
                    .collect();
                let k = *ks.get(self.tape.index(ks.len()))?;
                let (field, ty) = rt.fields.get(k)?;
                note!(self, fields);
                let sel = SExpr::Field(Box::new(base), field.clone());
                self.descend(sel, ty, kind, depth, r)
            }
            STy::UInt(_) | STy::SInt(_) | STy::Str | STy::Fn(_) | STy::Enum(_) => None,
            STy::List(elem) => {
                if kind == Kind::Int && self.tape.below(3) == 0 {
                    note!(self, list_lens);
                    return Some(SExpr::Len(Box::new(base)));
                }
                let Some(len) = self.shortest(&base, r) else {
                    return (kind == Kind::Int).then(|| SExpr::Len(Box::new(base)));
                };
                if !has_leaf(elem, kind) {
                    return None;
                }
                note!(self, list_indexes);
                let at = self.index(len, depth, r);
                Some(SExpr::Index(Box::new(base), Box::new(at)))
            }
            STy::Array(elem, n) => {
                if kind == Kind::Int && self.tape.below(4) == 0 {
                    note!(self, lens);
                    return Some(SExpr::Len(Box::new(base)));
                }
                if !has_leaf(elem, kind) {
                    return None;
                }
                note!(self, indexes);
                let at = self.index(*n, depth, r);
                self.descend(
                    SExpr::Index(Box::new(base), Box::new(at)),
                    elem,
                    kind,
                    depth,
                    r,
                )
            }
        }
    }

    /// An index into `len` elements: a literal, or a candidate that is in
    /// `0..len` in each env of `r`. In a `comptime fn` body only the sample
    /// check covers a candidate, so a literal stands there.
    pub(super) fn index(&mut self, len: u32, depth: u32, r: Reach<'_>) -> SExpr {
        let Some(envs) = r.envs else {
            return self.number(0, len - 1);
        };
        let last = i64::from(len) - 1;
        let candidate = match self.tape.below(4) {
            0 | 1 => return self.number(0, len - 1),
            2 => {
                // `(x % n)`, in range for a non-negative `x`.
                let x = self.sexpr(Kind::Int, depth.saturating_sub(1), r);
                bin(SBin::Rem, x, int(i64::from(len)))
            }
            _ => {
                let cond = self.sexpr(Kind::Bool, depth.saturating_sub(1), r);
                let (then, els) = (self.number(0, len - 1), self.number(0, len - 1));
                SExpr::If(Box::new(cond), Box::new(then), Box::new(els))
            }
        };
        if self.holds(
            &candidate,
            envs,
            |v| matches!(v, Value::Int(k) if (0..=last).contains(&i64::try_from(k).unwrap_or(-1))),
        ) {
            return candidate;
        }
        note!(self, index_fallbacks);
        self.number(0, len - 1)
    }
}

/// `t` if it has a leaf of `kind`, else the tuple of one such leaf.
fn with_leaf(t: STy, kind: Kind) -> STy {
    if has_leaf(&t, kind) {
        return t;
    }
    match kind {
        Kind::Bool => STy::Tuple(vec![STy::Bool]),
        Kind::Int | Kind::Str => STy::Tuple(vec![STy::Int]),
    }
}
