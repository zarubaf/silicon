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

use super::arms::onehot_leaf;
use super::container::Piece;
use super::hwops::{Side, share};
use super::{Evaluator, Guard, GuardKind, Names, Opnd, Out, Res, Slot, at, fail, need};
use crate::Code;
use crate::cover::{Cover, all_keys, key_bits, key_lo};
use crate::hw::Graph;
use crate::hw::{HwId, Op, Seen, Val};
use crate::int::{Int, words};
use crate::limit;
use crate::ops::{self, Fuel, int_text};
use crate::types::{Ty, TyId, Types};
use crate::unpack::unpack;
use crate::value::{Value, int_size, width_size};
use parse::ast::{Arm, BinOp, Expr, Ident, Item, Pattern, Pos};

/// The payload of a scrutinee for its binders: the words of a static payload, or the hardware
/// `payload` leaf of a hardware enum.
pub(super) enum Payload {
    Static(Vec<u64>),
    Hw(HwId),
}

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
        Pattern::Int { .. } => value.map_or_else(String::new, int_text),
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
        let sp = scrut.pos();
        let d = self.operand(sp, scrut)?;
        let t = self.scrut_ty(sp, &d)?;
        let cover = self.match_arms(pos, t, arms)?;
        let out = match d {
            Opnd::Static(out) if !self.is_agg(&out) => out,
            d => return self.hw_match((pos, sp), t, &d, arms, &cover),
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
            self.bind_binders(&Payload::Static(bits), binders)?;
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
                None => int_text(k),
            },
            _ => int_text(k),
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
                                "the tag `{}` of `{text}` has no variant, but a port or a \
                                 memory can hold it; add `_ => ...` as the last arm",
                                int_text(&u)
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

    /// The checks and the charge of the type `u` of a binder (sections 5.4 and 5.5): `S015` at
    /// the binder above the depth of a zero of `u`, `S015` above the size limit, then the charge
    /// of the zero size. All come before the unpack, which does work in the zero size.
    pub(super) fn charge_zero(&mut self, pos: Pos, u: TyId) -> Res<()> {
        self.bounded(pos, self.tys.zero_depth(u))?;
        limit::zero(&self.tys.meta(u).zero_size).map_err(at(pos))?;
        self.fuel
            .pay_int(&self.tys.meta(u).zero_size)
            .map_err(at(pos))
    }

    /// The binders `binders` of an arm with the payload `payload` (section 5.4). Each binder
    /// checks the depth and the size limit of its type, then charges that zero size. A static
    /// payload binds the static unpack of its value, at its offset. A hardware payload binds its
    /// hardware unpack (`unpack_hw`), each `extract` charged 2, and the value gets its core name
    /// as a `let` does.
    fn bind_binders(&mut self, payload: &Payload, binders: Vec<Binder<'_>>) -> Res<()> {
        for Binder { name, ty, off } in binders {
            self.charge_zero(name.pos, ty)?;
            let value = match payload {
                Payload::Static(bits) => {
                    let Some(x) = unpack(&self.tys, bits, ty, off) else {
                        return fail(
                            Code::S010,
                            name.pos,
                            format!("{} has no static unpack", self.tys.text(ty)),
                        );
                    };
                    Val::Static(x)
                }
                Payload::Hw(y) => {
                    let a = self.unpack_hw(name.pos, *y, ty, off)?;
                    let id = self.decl(name)?;
                    self.named(name.pos, id, a.into_val())?
                }
            };
            let id = self.decl(name)?;
            self.bind(
                id,
                Slot {
                    ty: Some(ty),
                    mutable: false,
                    value,
                },
            );
        }
        Ok(())
    }

    /// The selector leaf and the payload of the hardware scrutinee `d` of the type `t`: the
    /// scalar itself, or the `tag` and `payload` leaves of an enum (section 5.4). A static tag
    /// is a constant, so its selects compare two constants (section 5.6). A part of a reference
    /// is a leaf that refers to its core name.
    fn scrut_parts(&mut self, sp: Pos, t: TyId, d: &Opnd) -> Res<(HwId, Payload)> {
        if let Opnd::Hw(h) = d {
            return Ok((*h, Payload::Static(Vec::new())));
        }
        let Some(widths) = self.tys.widths(t) else {
            return fail(Code::S010, sp, format!("{} has no entry", self.tys.text(t)));
        };
        let (_, tag_step, tag_off) = self.child_of(sp, t, 0)?;
        let payload_part = if widths.payload > 0 {
            Some(self.child_of(sp, t, 1)?)
        } else {
            None
        };
        let Some(side) = Side::of_opnd(&self.store, d) else {
            return fail(Code::S010, sp, "the scrutinee is not data".to_owned());
        };
        let tag_ty = Ty::UInt(widths.tag);
        let env = (&mut self.graph, &mut self.paths);
        let tag = match side.child(0, (&tag_step, tag_off, Some(&tag_ty), false), sp, env) {
            Some(Side::Hw(h)) => h,
            Some(part) => match part.value() {
                Some(v) => super::hwops::lit_of(sp, v.clone(), &mut self.graph, &self.tys)?,
                None => return fail(Code::S010, sp, no_leaf(&self.tys, t, "tag")),
            },
            None => return fail(Code::S010, sp, no_leaf(&self.tys, t, "tag")),
        };
        let Some((_, payload_step, payload_off)) = payload_part else {
            return Ok((tag, Payload::Static(Vec::new())));
        };
        let payload_ty = Ty::UInt(widths.payload);
        let env = (&mut self.graph, &mut self.paths);
        let part = side.child(
            1,
            (&payload_step, payload_off, Some(&payload_ty), false),
            sp,
            env,
        );
        match part {
            Some(Side::Hw(h)) => Ok((tag, Payload::Hw(h))),
            Some(part) => match part.value() {
                Some(Value::UInt(y)) => Ok((tag, Payload::Static(words(y)))),
                _ => fail(Code::S010, sp, no_leaf(&self.tys, t, "payload")),
            },
            None => fail(Code::S010, sp, no_leaf(&self.tys, t, "payload")),
        }
    }

    /// A mark of the operand `h` at `pos` that `uses` leaf statements read (section 5.4).
    fn mark(&mut self, pos: Pos, uses: u64, h: HwId) -> Res<HwId> {
        let env = (&mut self.fuel, &mut self.graph, &mut self.naming);
        share(pos, uses, env, h)
    }

    /// A hardware `match` at `pos` with the scrutinee `d` of the type `t`, after the checks of
    /// its arms (section 5.4). These steps run:
    ///
    /// 1. The selector leaf gets a mark when two or more arms are not `_`. The payload leaf of
    ///    a hardware enum gets a mark when the binders of all arms have two or more leaves.
    /// 2. Each arm evaluates in source order under the guard `arm`, its binders first. The
    ///    results wait while the later arms evaluate.
    /// 3. One arm `_` gives its value, with no node. Else the arms join (`match_join`).
    fn hw_match(
        &mut self,
        (pos, sp): (Pos, Pos),
        t: TyId,
        d: &Opnd,
        arms: &[Arm],
        cover: &Cover,
    ) -> Res<Option<Out>> {
        let (sel, payload) = self.scrut_parts(sp, t, d)?;
        let keys = &cover.arms;
        let others = keys.iter().flatten().count() as u64;
        let sel = self.mark(pos, others, sel)?;
        let mut binders = Vec::with_capacity(arms.len());
        for arm in arms {
            binders.push(self.binder_tys(t, &arm.pat)?);
        }
        let payload = match payload {
            Payload::Hw(h) => {
                let leaves = binders
                    .iter()
                    .flatten()
                    .map(|b| self.tys.meta(b.ty).leaves.to_u64().unwrap_or(u64::MAX))
                    .fold(0u64, u64::saturating_add);
                Payload::Hw(self.mark(pos, leaves, h)?)
            }
            payload @ Payload::Static(_) => payload,
        };
        let mut outs = self.hw_arms(pos, &payload, arms, binders)?;
        match outs.pop() {
            Some(only) if outs.is_empty() => Ok(Some(only)),
            Some(last) => {
                outs.push(last);
                let val = self.match_join(pos, sel, keys, outs)?;
                Ok(Some(Out::Made(val)))
            }
            None => fail(Code::S021, pos, "the `match` has no arm".to_owned()),
        }
    }

    /// The results of the arms in source order. Each arm runs under the guard `arm`: its binders
    /// bind first, then its value evaluates in a data context. The result of an arm waits while
    /// the later arms evaluate.
    fn hw_arms(
        &mut self,
        pos: Pos,
        payload: &Payload,
        arms: &[Arm],
        binders: Vec<Vec<Binder<'_>>>,
    ) -> Res<Vec<Out>> {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Guarded, 1);
        let saved = self.guard.replace(Guard {
            kind: GuardKind::Arm,
            depth: self.depth,
        });
        let base = self.store.parked_len();
        let ran = self.run_arms(pos, payload, arms, binders);
        self.guard = saved;
        ran?;
        Ok(self.store.resume(base))
    }

    fn run_arms(
        &mut self,
        pos: Pos,
        payload: &Payload,
        arms: &[Arm],
        binders: Vec<Vec<Binder<'_>>>,
    ) -> Res<()> {
        for (arm, bs) in arms.iter().zip(binders) {
            self.bind_binders(payload, bs)?;
            let o = self.eval(&arm.value)?;
            let o = need(&arm.value, o)?;
            let was_ref = o.is_ref();
            let o = match self.data(pos, o)? {
                Opnd::Hw(h) if was_ref => Out::Named(Val::Hw(h)),
                Opnd::Hw(h) => Out::Made(Val::Hw(h)),
                Opnd::Static(Out::Made(v)) if was_ref => Out::Named(v),
                Opnd::Static(o) => o,
            };
            self.store.park(o);
        }
        Ok(())
    }

    /// The constant of the key `k` of a select on a leaf of the type `ty` (section 5.6). The
    /// size of a finite value of `ty` charges first.
    fn key_lit(&mut self, pos: Pos, ty: &Ty, k: &Int) -> Res<HwId> {
        if let Ty::Bool | Ty::UInt(_) | Ty::SInt(_) = ty {
            let size = match ty {
                Ty::UInt(w) | Ty::SInt(w) => width_size(*w),
                _ => 1,
            };
            self.charge(pos, u128::from(size))?;
        }
        let value = match ty {
            Ty::Bool => Some(Value::Bool(*k == Int::from_u64(1))),
            Ty::UInt(w) => k.to_finite(*w).map(Value::UInt),
            Ty::SInt(w) => k.to_finite(*w).map(Value::SInt),
            _ => None,
        };
        match value {
            Some(v) => Ok(self.graph.mk(pos, ty.clone(), Op::Lit(v), Vec::new())),
            None => fail(
                Code::S010,
                pos,
                format!("{} has no key literal", self.tys.text_of(ty)),
            ),
        }
    }

    /// Steps 3 to 6 of a hardware `match` at `pos` (section 5.4). `sel` is the selector leaf with
    /// its mark, `keys` the key of each arm in arm order (none for `_`), and `outs` the arm
    /// values:
    ///
    /// 3. The arm types join as the elements of an array literal, with the join charge (`S010`
    ///    without a join). Then each arm converts to the joined type.
    /// 4. The selects `(icmp eq sel k)` build in arm order. Each select first charges the size of
    ///    a finite value of the type of `sel`, for its key constant, before the constant exists. A
    ///    select has `u = L + 1` uses with an arm `_`, else `L`, with `L` the leaf count of the
    ///    joined type. At `u >= 2` it then gets a mark.
    /// 5. The select of `_` is one node `rest` over the selects, charged `1 + n` before it
    ///    exists. Then it gets a mark at `L >= 2`.
    /// 6. The walk over the arms (`arm_walk`), with one `onehot` node for each leaf
    ///    (`onehot_leaf`). A root of a scalar type gets no walk charge.
    pub(super) fn match_join(
        &mut self,
        pos: Pos,
        sel: HwId,
        keys: &[Option<Int>],
        outs: Vec<Out>,
    ) -> Res<Val> {
        let pieces: Vec<Piece<'_>> = outs.into_iter().map(Piece::Out).collect();
        let mut types = Vec::with_capacity(pieces.len());
        for p in &pieces {
            types.push(self.piece_ty(pos, p)?);
        }
        let (units, common, clash) =
            ops::common_of(types, |t, _| *t, &mut self.tys, self.fuel.left());
        self.fuel.pay_joins(&units).map_err(at(pos))?;
        if let Some(fault) = clash {
            return Err(at(pos)(fault));
        }
        let Some(joined) = common else {
            return fail(
                Code::S010,
                pos,
                "the arms of a hardware `match` have no common type; convert each arm to one type"
                    .to_owned(),
            );
        };
        let mut opnds = Vec::with_capacity(pieces.len());
        for p in pieces {
            let p = self.conform_piece(pos, joined, p)?;
            opnds.push(match p {
                Piece::Out(o) => Opnd::of_out(o),
                Piece::New(a) => Opnd::of_out(Out::Made(a.into_val())),
                Piece::Part(a) => Opnd::of_out(Out::Made(a.clone().into_val())),
            });
        }
        let leaves = self.tys.meta(joined).leaves.to_u64().unwrap_or(u64::MAX);
        let wild = keys.iter().any(Option::is_none);
        let uses = leaves.saturating_add(u64::from(wild));
        let sel_ty = self.graph.ty(sel);
        let mut selects = Vec::new();
        for k in keys.iter().flatten() {
            let key = self.key_lit(pos, &sel_ty, k)?;
            let eq = self
                .graph
                .mk(pos, Ty::Bool, Op::Bin(BinOp::Eq), vec![sel, key]);
            selects.push(self.mark(pos, uses, eq)?);
        }
        let rest = if wild {
            let Val::Hw(r) = self.node(pos, Ty::Bool, Op::Rest, selects.clone())? else {
                return fail(Code::S010, pos, "a select is hardware".to_owned());
            };
            Some(self.mark(pos, leaves, r)?)
        } else {
            None
        };
        let mut next = selects.iter();
        let mut selected = Vec::with_capacity(keys.len());
        for key in keys {
            let s = match (key, rest) {
                (Some(_), _) => next.next().copied(),
                (None, r) => r,
            };
            let Some(s) = s else {
                return fail(Code::S010, pos, "an arm has no select".to_owned());
            };
            selected.push(s);
        }
        let leaf = |t: &Ty, sides: &[Side<'_>], env: (&mut Fuel, &mut Graph, &mut Types)| {
            onehot_leaf(pos, &selected, t, sides, env)
        };
        let refs: Vec<&Opnd> = opnds.iter().collect();
        self.arm_walk(("match", pos), joined, &refs, &leaf)
    }
}

/// The text of a leaf `name` of the enum type `t` that the scrutinee does not have.
fn no_leaf(tys: &Types, t: TyId, name: &str) -> String {
    format!("{} has no {name} leaf", tys.text(t))
}
