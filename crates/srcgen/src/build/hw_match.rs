// SPDX-License-Identifier: Apache-2.0
//! `match` with a hardware scrutinee.
//!
//! The scrutinee is a hardware enum (a name, a constructor with a hardware
//! payload value, or `reinterpret` of hardware bits), a `Bool`, or a finite
//! integer name. All arms evaluate and join, so each one is a hardware
//! expression of the wanted type, never a static `Int` (which would be
//! `S011`, or `S010` in the `if` chain of the twin). A binder of a variant
//! pattern is a hardware name `y<n>` of its leaf type.
//!
//! The arms follow the rule of `matches.rs`: `_` is last and is there
//! exactly when the other arms cover fewer than `2^W` values. A finite
//! scrutinee drops `_` only when all of its envs have one width `W`, and
//! the literals list each of the `2^W` values.

use super::enum_hw::is_hardware;
use super::hw::{Want, literal_ty};
use super::matches::matched;
use super::{Builder, Ctx, HW_MATCH_ODDS, Hw, NESTING};
use crate::program::{EnumDef, HExpr, Match, Pattern, Radix, Scalar, Variant};
use num_bigint::BigInt;

/// The most literal arms of a match on a finite integer.
const ARMS: u32 = 4;
/// The depth of the arms: a match is a wide node, so its arms stay shallow.
const ARM_DEPTH: u32 = 1;

impl Builder {
    /// A hardware `match` of the wanted type in one draw of `HW_MATCH_ODDS`
    /// of the side tape, if the nesting allows it.
    pub(super) fn hw_match_gate(&mut self, ctx: &Ctx, w: &Want, depth: u32) -> Option<HExpr> {
        if depth == 0
            || self.match_level >= NESTING
            || self.side_below(self.match_odds(HW_MATCH_ODDS)) != 1
        {
            return None;
        }
        self.on_side(|b| {
            let m = b.in_match(|b| b.hw_match(ctx, w, (depth - 1).min(ARM_DEPTH)));
            #[cfg(test)]
            if let Some(HExpr::Match(x)) = &m {
                b.tally(x, true);
            }
            m
        })
    }

    /// The caller is on the side tape.
    fn hw_match(&mut self, ctx: &Ctx, w: &Want, d: u32) -> Option<HExpr> {
        let hardware: Vec<usize> = (0..ctx.enums.len())
            .filter(|&i| ctx.enums.get(i).is_some_and(|e| e.hardware))
            .collect();
        let names: Vec<&Hw> = ctx.hw.iter().filter(|h| !h.types.is_empty()).collect();
        let on_enum = !hardware.is_empty() && (names.is_empty() || self.tape.below(4) != 0);
        let m = if on_enum {
            let at = *hardware.get(self.tape.index(hardware.len()))?;
            let def = ctx.enums.get(at)?.def.clone();
            let scrutinee = self.enum_scrutinee(ctx, &def, d);
            self.enum_arms(ctx, scrutinee, &def, w, d)?
        } else {
            let h = (*names.get(self.tape.index(names.len()))?).clone();
            self.scalar_arms(ctx, &h, w, d)?
        };
        Some(HExpr::Match(m))
    }

    /// A hardware value of `def` for a scrutinee: a constructor with a
    /// hardware payload, or `reinterpret` of hardware bits, sometimes; else
    /// a hardware name.
    fn enum_scrutinee(&mut self, ctx: &Ctx, def: &EnumDef, d: u32) -> HExpr {
        if self.tape.below(4) != 0 {
            for _ in 0..4 {
                let e = self.enum_expr(ctx, def, d);
                if matches!(e, HExpr::Ctor(..) | HExpr::Reinterpret(..)) && is_hardware(ctx, &e) {
                    note!(self, hw_expr_scrutinees);
                    return e;
                }
            }
        }
        let names: Vec<&HExpr> = ctx
            .enums
            .iter()
            .filter(|e| e.hardware && e.def == *def)
            .map(|e| &e.expr)
            .collect();
        let at = self.tape.index(names.len());
        let Some(name) = names.get(at) else {
            panic!(
                "the scrutinee of the builder has no hardware name of {}",
                def.name
            );
        };
        (*name).clone()
    }

    fn enum_arms(
        &mut self,
        ctx: &Ctx,
        scrutinee: HExpr,
        def: &EnumDef,
        w: &Want,
        d: u32,
    ) -> Option<Match<HExpr, HExpr>> {
        let listed = self.listed_variants(def);
        let mut arms = Vec::new();
        for v in &listed {
            let (pattern, binders) = self.hw_variant_pattern(def, v);
            let mut inner = ctx.clone();
            for (name, t) in binders {
                inner.hw.push(Hw {
                    expr: HExpr::Name(name),
                    ty: Some(literal_ty(t)),
                    types: vec![t; ctx.envs.len()],
                    mutable: false,
                });
            }
            arms.push((pattern, self.hw(&inner, w, d)?));
        }
        if listed.len() < 1usize << def.tag_width {
            arms.push((Pattern::Wild, self.hw(ctx, w, d)?));
        }
        Some(matched(scrutinee, arms))
    }

    /// `E::V(y0, _)`: a hardware binder or `_` for each payload leaf.
    fn hw_variant_pattern(
        &mut self,
        def: &EnumDef,
        v: &Variant,
    ) -> (Pattern, Vec<(String, Scalar)>) {
        let mut named = Vec::new();
        let binders = v
            .payload
            .iter()
            .map(|t| {
                if self.tape.below(4) == 0 {
                    return None;
                }
                let name = format!("y{}", self.binders);
                self.binders += 1;
                named.push((name.clone(), *t));
                Some(name)
            })
            .collect();
        (
            Pattern::Variant(def.name.clone(), v.name.clone(), binders),
            named,
        )
    }

    fn scalar_arms(&mut self, ctx: &Ctx, h: &Hw, w: &Want, d: u32) -> Option<Match<HExpr, HExpr>> {
        let first = *h.types.first()?;
        let scrutinee = h.expr.clone();
        if first == Scalar::Bool {
            let flip = self.tape.flag();
            let mut arms = Vec::new();
            match self.tape.below(3) {
                0 => {
                    for b in [flip, !flip] {
                        arms.push((Pattern::Bool(b), self.hw(ctx, w, d)?));
                    }
                }
                1 => {
                    arms.push((Pattern::Bool(flip), self.hw(ctx, w, d)?));
                    arms.push((Pattern::Wild, self.hw(ctx, w, d)?));
                }
                _ => arms.push((Pattern::Wild, self.hw(ctx, w, d)?)),
            }
            return Some(matched(scrutinee, arms));
        }
        // The literals fit the narrowest env.
        let width = h.types.iter().map(|t| t.bits()).min()?;
        let signed = matches!(first, Scalar::SInt(_));
        let uniform = h.types.iter().all(|t| *t == first);
        let (lo, space) = if signed {
            (-(1i128 << (width - 1).min(100)), 1i128 << width.min(100))
        } else {
            (0, 1i128 << width.min(100))
        };
        let full = uniform && width <= 2 && self.tape.below(3) == 0;
        let count = if full {
            space
        } else {
            i128::from(self.tape.below(ARMS + 1)).min(space - 1)
        };
        let values = self.distinct(lo, space, count);
        let complete = i128::try_from(values.len()).ok() == Some(space) && uniform;
        let mut arms = Vec::new();
        for v in values {
            let radix = match self.tape.below(4) {
                2 => Radix::Hex,
                3 => Radix::Bin,
                _ => Radix::Dec,
            };
            arms.push((Pattern::Int(BigInt::from(v), radix), self.hw(ctx, w, d)?));
        }
        if !complete {
            arms.push((Pattern::Wild, self.hw(ctx, w, d)?));
        }
        Some(matched(scrutinee, arms))
    }

    /// `count` distinct values in `lo..lo + space`, in random order.
    fn distinct(&mut self, lo: i128, space: i128, count: i128) -> Vec<i128> {
        let mut out: Vec<i128> = Vec::new();
        if space <= 16 {
            let mut all: Vec<i128> = (lo..lo + space).collect();
            for i in (1..all.len()).rev() {
                let j = self.tape.index(i + 1);
                all.swap(i, j);
            }
            all.truncate(usize::try_from(count).unwrap_or(0));
            return all;
        }
        let span = u32::try_from(space.min(1 << 20)).unwrap_or(1 << 20);
        for _ in 0..count * 4 {
            if i128::try_from(out.len()).ok() == Some(count) {
                break;
            }
            let v = lo + i128::from(self.tape.below(span));
            if !out.contains(&v) {
                out.push(v);
            }
        }
        out
    }
}
