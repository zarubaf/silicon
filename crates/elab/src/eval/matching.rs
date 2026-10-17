// SPDX-License-Identifier: Apache-2.0
//! The `match` of Lean `Source.Eval` (design sections 5.4 and 5.6). The scrutinee evaluates in a
//! data context, and its type is `Bool`, `UInt`, `SInt`, `Int`, `Nat`, or an enum. Then each arm
//! runs its pattern charge, its kind and fit checks, and its coverage share, and it inserts its
//! key into one ordered map. The coverage check follows, with no walk over the values of the
//! type. A static scrutinee selects one arm by the map.
//!
//! No check loops over the values of a type, and no key makes a number `2^W`. The insert of a
//! key makes up to `1 + log n` compares, each at most 1024 words: a log factor above its share
//! of the coverage charge.

use super::{Evaluator, Names, Opnd, Out, Res, Slot, at, expr_pos, fail};
use crate::Code;
use crate::cover::{Cover, all_keys, key_bits, key_lo};
use crate::hw::{Seen, Val};
use crate::int::{Int, words};
use crate::limit;
use crate::ops;
use crate::types::{Ty, TyId};
use crate::unpack::unpack;
use crate::value::{Value, int_size, width_size};
use parse::ast::{Arm, Expr, Ident, Item, Pattern, Pos};

/// A binder of a variant pattern: its name, its type, and the bit offset of its value in the
/// pack of the payload tuple.
pub(super) struct Binder<'p> {
    pub name: &'p Ident,
    pub ty: TyId,
    pub off: u64,
}

/// The kind `{k}` of a pattern of the scrutinee type `t` in the `S010` text (section 6.2).
fn kind_text(t: &Ty, text: &str) -> String {
    match t {
        Ty::Bool => "`true` or `false`".to_owned(),
        Ty::Enum(_) => format!("a variant of `{text}`"),
        _ => "an integer".to_owned(),
    }
}

/// The text `{p}` of a pattern in the `S010` text of its kind (section 6.2). A literal is
/// written as `{v}`, and a variant pattern as its path with its binders and `_`.
fn pattern_text(pat: &Pattern, value: Option<&Int>) -> String {
    match pat {
        Pattern::Wild { .. } => "_".to_owned(),
        Pattern::Int { .. } => value.map_or_else(String::new, ToString::to_string),
        Pattern::Bool { value, .. } => value.to_string(),
        Pattern::Variant {
            ty,
            variant,
            binders,
            ..
        } => {
            let names: Vec<&str> = binders
                .iter()
                .map(|b| b.as_ref().map_or("_", |b| b.name.as_str()))
                .collect();
            let tail = if names.is_empty() {
                String::new()
            } else {
                format!("({})", names.join(", "))
            };
            format!("{}::{}{tail}", ty.name, variant.name)
        }
    }
}

impl Evaluator<'_> {
    /// A `match` at `pos` (section 5.4). The node charged before. The scrutinee evaluates in a
    /// data context, and its type is checked (`scrut_ty`). Then the arm checks and the coverage
    /// check run (`match_arms`), before an arm evaluates. A static scrutinee selects one arm by
    /// the map, else `_`. Its binders get a static unpack of the payload (`bind_static`). Then
    /// only that arm evaluates.
    pub(super) fn match_expr(&mut self, pos: Pos, scrut: &Expr, arms: &[Arm]) -> Res<Option<Out>> {
        let sp = expr_pos(scrut);
        let d = self.operand(sp, scrut)?;
        let t = self.scrut_ty(sp, &d)?;
        let cover = self.match_arms(pos, t, arms)?;
        let out = match d {
            Opnd::Static(out) if !self.is_agg(&out) => out,
            // TODO(#272): evaluate a hardware `match` (marks, binders, selects, join, and walk).
            _ => {
                return fail(
                    Code::S010,
                    pos,
                    "a hardware `match` is not supported yet".to_owned(),
                );
            }
        };
        // The coverage check passed, so the map or `_` selects an arm.
        let value = self.store.value(&out);
        let j = cover.arm_of(value.key().as_deref());
        let bits = match value {
            Value::Enum(_, _, payload) => Some(payload.as_ref().map(words).unwrap_or_default()),
            _ => None,
        };
        let Some(j) = j else {
            return fail(
                Code::S021,
                pos,
                "the `match` has no arm for its value".to_owned(),
            );
        };
        let Some(arm) = arms.get(j) else {
            return fail(Code::S021, pos, format!("the `match` has no arm {j}"));
        };
        if let Some(bits) = bits {
            let binders = self.binder_tys(t, &arm.pat)?;
            self.bind_static(&bits, binders)?;
        }
        self.eval(&arm.value)
    }

    /// The type check of the scrutinee `d` of a `match` at `sp` (section 5.6). The type is
    /// `Bool`, `UInt[W]`, `SInt[W]`, `Int`, `Nat`, or an enum, else `S010` with the text of
    /// section 6.2. A scalar answers in constant work, and a reference to a large container
    /// walks nothing before the error.
    fn scrut_ty(&mut self, sp: Pos, d: &Opnd) -> Res<TyId> {
        let seen = match d {
            Opnd::Hw(h) => {
                let ty = self.graph.ty(*h);
                return Ok(self.tys.mk(ty));
            }
            Opnd::Static(out) => self.store.seen(out),
        };
        let fast = match seen {
            Seen::Static(v) => match v {
                Value::Bool(_) | Value::UInt(_) | Value::SInt(_) | Value::Int(_) => {
                    Some(v.ty(&mut self.tys))
                }
                Value::Enum(t, ..) => Some(*t),
                _ => None,
            },
            Seen::Agg(a) => a
                .stored_ty()
                .filter(|t| matches!(self.tys.get(*t), Ty::Enum(_))),
            Seen::Hw(_) | Seen::Handle(_) | Seen::Pending(..) => None,
        };
        if let Some(t) = fast {
            return Ok(t);
        }
        let text = match seen.ty(&self.graph, &mut self.tys) {
            Some(t) => self.tys.text(t),
            None => self.text(seen),
        };
        fail(
            Code::S010,
            sp,
            format!(
                "a `match` takes `Bool`, `UInt`, `SInt`, `Int`, `Nat`, or an enum, not `{text}`; \
                 match on a part of the value"
            ),
        )
    }

    /// `S010` at `qp` for a pattern of another kind than the scrutinee type `t` takes.
    fn kind_fail<T>(&self, qp: Pos, t: TyId, pat: &Pattern, value: Option<&Int>) -> Res<T> {
        let text = self.tys.text(t);
        let kind = kind_text(self.tys.get(t), &text);
        fail(
            Code::S010,
            qp,
            format!(
                "a pattern of `{text}` is {kind}, not `{}`; write {kind}, or `_`",
                pattern_text(pat, value)
            ),
        )
    }

    /// The value of the literal of a pattern, with its sign.
    fn pattern_value(&self, pos: Pos, id: parse::ast::NodeId, neg: bool) -> Res<Int> {
        let Some(n) = self.numbers.get(&(self.names == Names::Top, id)) else {
            return fail(Code::S010, pos, "the literal has no value".to_owned());
        };
        Ok(if neg { n.neg() } else { n.clone() })
    }

    /// Steps 1 to 3 of the arm checks of a `match` with the scrutinee type `t` (section 5.6),
    /// for the pattern `pat`:
    ///
    /// 1. The pattern charge at the pattern (section 5.4). `_` charges 1, and a literal
    ///    `1 + s`. A variant pattern charges `1 + s` and 1 for each binder and each `_`. `s` is
    ///    the size of the value of a literal. For a variant, it is `tag_size`, the size of a
    ///    value of the tag type of the scrutinee. It is 1 when the scrutinee is not an enum.
    /// 2. The kind of the pattern (`S010`). A variant pattern compares the resolved enum items.
    ///    Thus it is no use of the enum of the pattern: no first use, no charge, and no error
    ///    of it.
    /// 3. The fit of a literal (`S012`).
    ///
    /// The result is the position of the pattern, its key in the order of the type (none for
    /// `_`), and `s`.
    fn pattern_key(
        &mut self,
        t: TyId,
        tag_size: u64,
        pat: &Pattern,
    ) -> Res<(Pos, Option<Int>, u64)> {
        match pat {
            Pattern::Wild { pos } => {
                self.charge(*pos, 1)?;
                Ok((*pos, None, 0))
            }
            Pattern::Int { pos, id, neg, .. } => {
                let k = self.pattern_value(*pos, *id, *neg)?;
                let s = int_size(&k);
                self.charge(*pos, 1 + u128::from(s))?;
                let ty = self.tys.get(t).clone();
                if !matches!(ty, Ty::UInt(_) | Ty::SInt(_) | Ty::Int | Ty::Nat) {
                    return self.kind_fail(*pos, t, pat, Some(&k));
                }
                if !ops::fits(&ty, &k) {
                    return fail(Code::S012, *pos, ops::fit_text(&ty, &k, &self.tys));
                }
                Ok((*pos, Some(k), s))
            }
            Pattern::Bool { pos, value } => {
                self.charge(*pos, 2)?;
                if !matches!(self.tys.get(t), Ty::Bool) {
                    return self.kind_fail(*pos, t, pat, None);
                }
                Ok((*pos, Some(Int::from_u64(u64::from(*value))), 1))
            }
            Pattern::Variant {
                pos, ty, binders, ..
            } => {
                self.charge(*pos, 1 + u128::from(tag_size) + binders.len() as u128)?;
                let found = self.variant_ref(ty);
                let same = match (self.tys.get(t), found) {
                    (Ty::Enum(e), Some(found)) => e.item() == found.item,
                    _ => false,
                };
                let (true, Some(found)) = (same, found) else {
                    return self.kind_fail(*pos, t, pat, None);
                };
                let Some(variant) = self.tys.variants(t).and_then(|vs| vs.get(found.index)) else {
                    return fail(
                        Code::S010,
                        *pos,
                        format!("{} has no variant {}", self.tys.text(t), found.index),
                    );
                };
                Ok((*pos, Some(Int::from_unsigned(&variant.tag)), tag_size))
            }
        }
    }

    /// The arm checks of the arm `i` with the pattern `pat` (section 5.6): steps 1 to 3
    /// (`pattern_key`), then these steps:
    ///
    /// 4. The coverage share `1 + log + s` of a pattern that is not `_` (section 5.4). `log` is
    ///    `floor(log2 n)`, with `n` the number of the arms that are not `_` in the syntax.
    /// 5. An arm after `_` is `S021`. Then a key in the map is a second match (`S021`, with the
    ///    position of the first arm), else the key goes into the map. The insert makes up to
    ///    `1 + log` compares: a log factor above its share (section 5.4).
    fn cover_arm(
        &mut self,
        (t, log, tag_size): (TyId, u32, u64),
        cover: &mut Cover,
        i: usize,
        pat: &Pattern,
    ) -> Res<()> {
        let (qp, key, s) = self.pattern_key(t, tag_size, pat)?;
        if key.is_some() {
            self.charge(qp, 1 + u128::from(log) + u128::from(s))?;
        }
        if cover.wild.is_some() {
            return fail(
                Code::S021,
                qp,
                "this arm comes after `_`, so it matches no value; move `_` to the end, or \
                 remove this arm"
                    .to_owned(),
            );
        }
        cover.arms.push(key.clone());
        let Some(k) = key else {
            cover.wild = Some((i, qp));
            return Ok(());
        };
        if let Some((_, b)) = cover.keys.get(&k) {
            return fail(
                Code::S021,
                qp,
                format!(
                    "this arm matches `{}`, and the arm at {}:{} matches it too; remove one of \
                     the two patterns",
                    self.key_text(t, &k),
                    b.line,
                    b.col
                ),
            );
        }
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Covered, 1);
        cover.keys.insert(k, (i, qp));
        Ok(())
    }

    /// The source text of the variant `j` of the enum item `i` in the `S021` texts (section
    /// 6.2): its path, with one `_` for each payload value.
    fn variant_text(&self, i: usize, j: usize) -> String {
        match self.file.ast().get(i) {
            Some(Item::Enum { name, variants, .. }) => match variants.get(j) {
                Some(v) => {
                    let tail = if v.payload.is_empty() {
                        String::new()
                    } else {
                        format!("({})", vec!["_"; v.payload.len()].join(", "))
                    };
                    format!("{}::{}{tail}", name.name, v.name.name)
                }
                None => j.to_string(),
            },
            _ => j.to_string(),
        }
    }

    /// The text `{v}` of the key `k` of the scrutinee type `t` (section 6.2). A `Bool` is `true`
    /// or `false`, the tag of a variant is the variant, and another key is a decimal integer
    /// with its sign. The tag map of the enum gives the variant of a tag.
    fn key_text(&self, t: TyId, k: &Int) -> String {
        match self.tys.get(t) {
            Ty::Bool => (*k == Int::from_u64(1)).to_string(),
            Ty::Enum(e) => match self.tys.variant_of_tag(t, k) {
                Some(j) => self.variant_text(e.item(), j),
                None => k.to_string(),
            },
            _ => k.to_string(),
        }
    }

    /// The coverage check of a `match` at `pos` with the scrutinee type `t` after its last arm
    /// (section 5.6), with no charge. A `_` without values is `S021` at the `_`. Then a value
    /// that no arm matches is `S021` at `pos`. The count of the keys compares with `2^W` by
    /// `all_keys`, and the smallest uncovered value comes from one pass over the ordered keys. A
    /// tag without a variant has its own text.
    fn cover_check(&self, pos: Pos, t: TyId, cover: &Cover) -> Res<()> {
        let text = self.tys.text(t);
        match (cover.wild, key_bits(&self.tys, t)) {
            (Some((_, wp)), Some(w)) => {
                if all_keys(cover.keys.len(), w) {
                    return fail(
                        Code::S021,
                        wp,
                        format!(
                            "the arms before `_` cover each value of `{text}`; remove the `_` arm"
                        ),
                    );
                }
            }
            (Some(_), None) => {}
            (None, None) => {
                return fail(
                    Code::S021,
                    pos,
                    format!(
                        "a `match` on `{text}` has no finite set of values; add `_ => ...` as \
                         the last arm"
                    ),
                );
            }
            (None, Some(w)) => {
                if !all_keys(cover.keys.len(), w) {
                    let u = cover.smallest_uncovered(key_lo(&self.tys, t, w));
                    if matches!(self.tys.get(t), Ty::Enum(_))
                        && self.tys.variant_of_tag(t, &u).is_none()
                    {
                        return fail(
                            Code::S021,
                            pos,
                            format!(
                                "the tag `{u}` of `{text}` has no variant, but a port or a \
                                 memory can hold it; add `_ => ...` as the last arm"
                            ),
                        );
                    }
                    return fail(
                        Code::S021,
                        pos,
                        format!(
                            "the `match` does not cover `{}` of `{text}`; add an arm for it, or \
                             add `_ => ...` as the last arm",
                            self.key_text(t, &u)
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    /// The arm checks of the arms `arms` of a `match` at `pos` with the scrutinee type `t`, in
    /// arm order (`cover_arm`), then its coverage check (`cover_check`). They all run before an
    /// arm evaluates (section 5.6). The result is the ordered map.
    fn match_arms(&mut self, pos: Pos, t: TyId, arms: &[Arm]) -> Res<Cover> {
        let others = arms
            .iter()
            .filter(|a| !matches!(a.pat, Pattern::Wild { .. }))
            .count();
        let log = others.checked_ilog2().unwrap_or(0);
        let tag_size = self
            .tys
            .widths(t)
            .map_or(1, |widths| width_size(widths.tag));
        let mut cover = Cover::default();
        for (i, arm) in arms.iter().enumerate() {
            self.cover_arm((t, log, tag_size), &mut cover, i, &arm.pat)?;
        }
        self.cover_check(pos, t, &cover)?;
        Ok(cover)
    }

    /// The binders of the pattern `pat` of a scrutinee of the enum type `t`, each with its type
    /// and the bit offset of its value in the pack of the payload tuple. The offset counts the
    /// width of each payload value, also one that has no binder. `_` and the other patterns
    /// bind nothing.
    pub(super) fn binder_tys<'p>(&self, t: TyId, pat: &'p Pattern) -> Res<Vec<Binder<'p>>> {
        let Pattern::Variant {
            pos, ty, binders, ..
        } = pat
        else {
            return Ok(Vec::new());
        };
        let found = self.variant_ref(ty);
        let payload = found
            .and_then(|found| self.tys.variants(t)?.get(found.index))
            .map(|v| &v.payload);
        let Some(payload) = payload else {
            return fail(Code::S010, *pos, "the variant has no entry".to_owned());
        };
        // Pass 4 reports each arity (`S007`), so this is a defect.
        if payload.len() != binders.len() {
            return fail(
                Code::S010,
                *pos,
                format!("the variant has {} payload type(s) here", payload.len()),
            );
        }
        let mut off = 0u64;
        let mut out = Vec::new();
        for (binder, u) in binders.iter().zip(payload) {
            if let Some(name) = binder {
                out.push(Binder { name, ty: *u, off });
            }
            off = off.saturating_add(self.tys.meta(*u).width.to_u64().unwrap_or(u64::MAX));
        }
        Ok(out)
    }

    /// The size check and the charge of the zero size of the type `u` of a binder (section
    /// 5.4): `S015` at the binder above the limit, then the charge of the zero size. Both come
    /// before the unpack, which does work in the zero size.
    pub(super) fn charge_zero(&mut self, pos: Pos, u: TyId) -> Res<()> {
        limit::zero(&self.tys.meta(u).zero_size).map_err(at(pos))?;
        self.fuel
            .pay_int(&self.tys.meta(u).zero_size)
            .map_err(at(pos))
    }

    /// The binders `binders` of an arm with the static payload bits `bits` (section 5.4). Each
    /// binder checks the size limit at the zero size of its type, then charges that zero size.
    /// Then it binds the static unpack of its value, at its offset.
    fn bind_static(&mut self, bits: &[u64], binders: Vec<Binder<'_>>) -> Res<()> {
        for Binder { name, ty, off } in binders {
            self.charge_zero(name.pos, ty)?;
            let Some(x) = unpack(&self.tys, bits, ty, off) else {
                return fail(
                    Code::S010,
                    name.pos,
                    format!("{} has no static unpack", self.tys.text(ty)),
                );
            };
            let id = self.decl(name)?;
            self.bind(
                id,
                Slot {
                    ty: Some(ty),
                    mutable: false,
                    value: Val::Static(x),
                },
            );
        }
        Ok(())
    }
}
