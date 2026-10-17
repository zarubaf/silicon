// SPDX-License-Identifier: Apache-2.0
//! `match` expressions on static scrutinees.
//!
//! The arms cover every value by construction, so the static evaluator has
//! no coverage check (ADR 0018). For a scrutinee of `W` bits (`Bool`: one
//! bit; `Int`: unbounded), `_` is the last arm exactly when the other arms
//! cover fewer than `2^W` values. The literals of the arms are distinct
//! and fit. An enum scrutinee lists each variant at most once, and in
//! shuffled order. A binder of a static `match` is `B<n>`; the twin folds
//! the whole `match` to a literal, so no binder remains.

use super::stat::{Kind, Reach, int};
use super::{Builder, MATCH_ODDS};
use crate::program::{EnumDef, Match, Pattern, Radix, SExpr, STy, Scalar, Variant};
use num_bigint::BigInt;

/// The most literal arms of a match on an integer.
pub(super) const ARMS: u32 = 4;

impl Builder {
    /// A static `match` of `kind` in place of an expression, in one draw of
    /// `MATCH_ODDS` of the side tape, if `depth` allows an arm one level
    /// below.
    pub(super) fn static_match_gate(
        &mut self,
        kind: Kind,
        depth: u32,
        r: Reach<'_>,
    ) -> Option<SExpr> {
        if depth == 0 || self.side_below(MATCH_ODDS) != 1 {
            return None;
        }
        self.on_side(|b| {
            if b.match_level > 0 {
                note!(b, nested_matches);
            }
            b.match_level += 1;
            let m = b.static_match(kind, depth - 1, r);
            b.match_level -= 1;
            m
        })
    }

    /// The names of `r` that hold an enum value.
    fn enum_statics(r: Reach<'_>) -> Vec<(String, EnumDef)> {
        r.names
            .iter()
            .filter_map(|(n, t)| match t {
                STy::Enum(d) => Some((n.clone(), (**d).clone())),
                _ => None,
            })
            .collect()
    }

    /// The caller is on the side tape.
    fn static_match(&mut self, kind: Kind, d: u32, r: Reach<'_>) -> Option<SExpr> {
        note!(self, static_matches);
        match self.tape.below(5) {
            0 | 1 => Some(self.int_match(kind, d, r)),
            2 => Some(self.bool_match(kind, d, r)),
            _ => {
                let defs = Builder::enum_statics(r);
                let (scrutinee, def) = if !defs.is_empty() && self.tape.flag() {
                    let (n, def) = defs.get(self.tape.index(defs.len()))?;
                    (SExpr::Name(n.clone()), def.clone())
                } else {
                    let def = self.pick_enum()?;
                    (self.enum_value(&def, d, r), def)
                };
                Some(self.enum_match(scrutinee, &def, kind, d, r))
            }
        }
    }

    /// An arm: an expression of `kind`.
    fn arm(&mut self, kind: Kind, d: u32, r: Reach<'_>) -> SExpr {
        self.sexpr(kind, d, r)
    }

    fn int_match(&mut self, kind: Kind, d: u32, r: Reach<'_>) -> SExpr {
        let scrutinee = self.sexpr(Kind::Int, d, r);
        let mut values: Vec<i64> = (-4..=9).collect();
        for i in (1..values.len()).rev() {
            let j = self.tape.index(i + 1);
            values.swap(i, j);
        }
        let count = self.tape.below(ARMS + 1) as usize;
        let mut arms: Vec<(Pattern, SExpr)> = values
            .into_iter()
            .take(count)
            .map(|v| (self.int_pattern(v), self.arm(kind, d, r)))
            .collect();
        // An integer has no last value, so `_` is always there.
        arms.push((Pattern::Wild, self.arm(kind, d, r)));
        matched(scrutinee, arms)
    }

    fn int_pattern(&mut self, v: i64) -> Pattern {
        let radix = match self.tape.below(4) {
            2 => Radix::Hex,
            3 => Radix::Bin,
            _ => Radix::Dec,
        };
        Pattern::Int(BigInt::from(v), radix)
    }

    fn bool_match(&mut self, kind: Kind, d: u32, r: Reach<'_>) -> SExpr {
        let scrutinee = self.sexpr(Kind::Bool, d, r);
        let first = self.tape.flag();
        let mut arms = Vec::new();
        match self.tape.below(3) {
            0 => {
                note!(self, complete_matches);
                for b in [first, !first] {
                    arms.push((Pattern::Bool(b), self.arm(kind, d, r)));
                }
            }
            1 => {
                arms.push((Pattern::Bool(first), self.arm(kind, d, r)));
                arms.push((Pattern::Wild, self.arm(kind, d, r)));
            }
            _ => arms.push((Pattern::Wild, self.arm(kind, d, r))),
        }
        matched(scrutinee, arms)
    }

    /// A match on an enum value: a subset of the variants in shuffled
    /// order, and `_` unless the arms list each of the `2^W` tags.
    fn enum_match(
        &mut self,
        scrutinee: SExpr,
        def: &EnumDef,
        kind: Kind,
        d: u32,
        r: Reach<'_>,
    ) -> SExpr {
        note!(self, static_enum_matches);
        let listed = self.listed_variants(def);
        let wild = listed.len() < 1usize << def.tag_width;
        let mut arms = Vec::new();
        for v in &listed {
            let (pattern, binders) = self.variant_pattern(def, v);
            let mut names = r.names.to_vec();
            names.extend(binders.iter().map(|b| (b.clone(), STy::Bool)));
            let inner = Reach {
                names: &names,
                fns: r.fns,
                envs: r.envs,
            };
            let body = match binders.first() {
                Some(b) if kind == Kind::Bool && self.tape.flag() => SExpr::Name(b.clone()),
                _ => self.arm(kind, d, inner),
            };
            arms.push((pattern, body));
        }
        if wild {
            arms.push((Pattern::Wild, self.arm(kind, d, r)));
        } else {
            note!(self, complete_matches);
        }
        matched(scrutinee, arms)
    }

    /// A random subset of the variants, in shuffled order.
    fn listed_variants(&mut self, def: &EnumDef) -> Vec<Variant> {
        let mut vs = def.variants.clone();
        for i in (1..vs.len()).rev() {
            let j = self.tape.index(i + 1);
            vs.swap(i, j);
        }
        // Choice 0 lists the most variants, which can complete the match.
        let keep = vs.len() - self.tape.index(vs.len() + 1).min(vs.len());
        vs.truncate(keep);
        vs
    }

    /// `E::V(B0, _)`: a binder or `_` for each payload leaf. The binders
    /// of `Bool` leaves are the names that an arm of kind `Bool` reads; the
    /// others are never read, so the arm is a plain expression. The second
    /// result lists the readable binders.
    fn variant_pattern(&mut self, def: &EnumDef, v: &Variant) -> (Pattern, Vec<String>) {
        let mut readable = Vec::new();
        let binders = v
            .payload
            .iter()
            .map(|t| {
                if self.tape.flag() {
                    return None;
                }
                let name = format!("B{}", self.binders);
                self.binders += 1;
                note!(self, static_binders);
                if *t == Scalar::Bool {
                    readable.push(name.clone());
                }
                Some(name)
            })
            .collect();
        (
            Pattern::Variant(def.name.clone(), v.name.clone(), binders),
            readable,
        )
    }

    /// A static `match` on an enum value whose arms have one finite type
    /// `t`, with a payload leaf of `t` as the result in some arms. The
    /// record of a `diagnostic` shows the unpack of the leaf (ADR 0025).
    /// The caller is on the side tape.
    pub(super) fn finite_match(&mut self, r: Reach<'_>) -> Option<SExpr> {
        let def = self.pick_enum()?;
        let with: Vec<(&Variant, usize, Scalar)> = def
            .variants
            .iter()
            .flat_map(|v| v.payload.iter().enumerate().map(move |(i, t)| (v, i, *t)))
            .collect();
        let (_, _, t) = *with.get(self.tape.index(with.len()))?;
        let scrutinee = self.enum_value(&def, 1, r);
        let wild = def.variants.len() < 1usize << def.tag_width;
        let mut arms = Vec::new();
        for v in &def.variants {
            let at = v.payload.iter().position(|p| *p == t);
            let binders: Vec<Option<String>> = (0..v.payload.len())
                .map(|i| {
                    (Some(i) == at).then(|| {
                        let name = format!("B{}", self.binders);
                        self.binders += 1;
                        name
                    })
                })
                .collect();
            let body = match binders.iter().flatten().next() {
                Some(b) => {
                    note!(self, static_binders);
                    SExpr::Name(b.clone())
                }
                None => self.finite_constant(t),
            };
            arms.push((
                Pattern::Variant(def.name.clone(), v.name.clone(), binders),
                body,
            ));
        }
        if wild {
            arms.push((Pattern::Wild, self.finite_constant(t)));
        }
        note!(self, finite_matches);
        Some(matched(scrutinee, arms))
    }

    /// A static value of the finite type `t`.
    fn finite_constant(&mut self, t: Scalar) -> SExpr {
        match t {
            Scalar::Bool => SExpr::Bool(self.tape.flag()),
            Scalar::UInt(w) => SExpr::Convert(STy::UInt(w), Box::new(self.finite_in(t))),
            Scalar::SInt(w) => SExpr::Convert(STy::SInt(w), Box::new(self.finite_in(t))),
        }
    }

    /// A literal that fits `t`.
    fn finite_in(&mut self, t: Scalar) -> SExpr {
        let ty = match t {
            Scalar::UInt(w) => STy::UInt(w),
            Scalar::SInt(w) => STy::SInt(w),
            Scalar::Bool => return int(0),
        };
        let n = self.finite_value(&ty, 3);
        self.finite_literal(n)
    }
}

fn matched(scrutinee: SExpr, arms: Vec<(Pattern, SExpr)>) -> SExpr {
    SExpr::Match(Match {
        scrutinee: Box::new(scrutinee),
        arms,
    })
}
