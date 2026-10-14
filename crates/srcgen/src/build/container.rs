// SPDX-License-Identifier: Apache-2.0
//! Static containers: tuple and array types, literals, and the scalar
//! exits that bring a leaf back to a static position.
//!
//! A container leaves a static position only through an exit: an index,
//! a selector `.N`, or `len`. An index is a static position, so each index
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
    }
}

impl Builder {
    /// A tuple or an array type with at most `levels` levels of nesting.
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

    /// The type of an element: a scalar, or a container one level deeper.
    fn element_ty(&mut self, levels: u32) -> STy {
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
            STy::Bool => self.element(Kind::Bool, depth, r),
            STy::Nat | STy::Int => self.element(Kind::Int, depth, r),
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
        }
    }

    /// A scalar of `kind` from a container: a name of `r` or a fresh
    /// literal, then a chain of indexes and selectors down to a leaf, or
    /// `len` of an array. `None` if no container has such a leaf.
    pub(super) fn exit(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> Option<SExpr> {
        let names: Vec<(&String, &STy)> = r
            .names
            .iter()
            .filter(|(_, t)| t.is_container() && has_leaf(t, kind))
            .map(|(n, t)| (n, t))
            .collect();
        if names.is_empty() || (depth > 0 && self.tape.below(4) == 3) {
            return self.literal_exit(kind, depth, r);
        }
        let (name, t) = *names.get(self.tape.index(names.len()))?;
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
        match self.tape.below(4) {
            2 => consts
                .get(self.tape.index(consts.len()))
                .map(|n| SExpr::Name((*n).clone())),
            3 => {
                let t = self.container_ty(CONTAINER_LEVELS);
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

    /// An exit from a fresh literal, for example `[1, x][0]`.
    fn literal_exit(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> Option<SExpr> {
        if depth == 0 {
            return None;
        }
        let t = with_leaf(self.container_ty(CONTAINER_LEVELS), kind);
        let lit = self.container(&t, depth - 1, r);
        self.descend(lit, &t, kind, depth - 1, r)
    }

    fn descend(
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
    fn index(&mut self, len: u32, depth: u32, r: Reach<'_>) -> SExpr {
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
        Kind::Int => STy::Tuple(vec![STy::Int]),
        Kind::Bool => STy::Tuple(vec![STy::Bool]),
    }
}
