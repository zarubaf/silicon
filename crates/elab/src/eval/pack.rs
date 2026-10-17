// SPDX-License-Identifier: Apache-2.0
//! The packed-value operations of the evaluator: the hardware pack of the leaves of a value
//! into `UInt[W]` (`Op::Pack`), the hardware unpack of bits into a value (`Op::Extract`), and
//! `reinterpret` between an enum and its bits (F26). Each walk keeps its own stack.

use super::arms::leaf_ty;
use super::hwops::{Side, lit_of, share};
use super::{Evaluator, Opnd, Res, fail};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{HwId, Node, Op, Seen, Val};
use crate::types::{Ty, TyId};
use crate::value::{Value, width_size};
use parse::ast::Pos;

impl Evaluator<'_> {
    /// The hardware leaf of the scalar type `ty` that the side gives: a constant for a static
    /// leaf, the node itself for a hardware leaf.
    fn pack_leaf(&mut self, pos: Pos, side: &Side<'_>, width: u32) -> Res<HwId> {
        match (side, side.value()) {
            (Side::Hw(h), _) => Ok(*h),
            (_, Some(v)) => lit_of(pos, v.clone(), &mut self.graph, &self.tys),
            _ => fail(
                Code::S010,
                pos,
                format!("a part of UInt[{width}] has no leaves"),
            ),
        }
    }

    /// Pushes the hardware leaves of the part `side` of the type `ty` onto `leaves`, in packing
    /// order (section 7.4). A static leaf is a constant, and a leaf of a reference refers to its
    /// name, so the walk never expands a reference into a node. A part without a leaf adds
    /// nothing, and the metadata tells it with no walk. The walk keeps its own stack. The copies
    /// of the payload values paid for each part that it visits.
    fn pack_collect(
        &mut self,
        pos: Pos,
        width: u32,
        (ty, side): (TyId, Side<'_>),
        leaves: &mut Vec<HwId>,
    ) -> Res<()> {
        /// A container whose parts wait: the next part to visit and the count.
        struct Frame<'a> {
            ty: TyId,
            side: Side<'a>,
            next: u64,
            len: u64,
        }
        let mut stack: Vec<Frame<'_>> = Vec::new();
        let mut visit = Some((ty, side));
        loop {
            if let Some((t, side)) = visit.take()
                && !self.tys.meta(t).leaves.is_zero()
            {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Packed, 1);
                let len = match self.tys.get(t) {
                    Ty::Bool | Ty::UInt(_) | Ty::SInt(_) => {
                        leaves.push(self.pack_leaf(pos, &side, width)?);
                        None
                    }
                    Ty::Array(_, n) => Some(n.to_u64().unwrap_or(u64::MAX)),
                    Ty::Tuple(ts) => Some(ts.len() as u64),
                    Ty::Struct(_) | Ty::Enum(_) => {
                        Some(self.tys.parts(t).map_or(0, |p| p.types.len() as u64))
                    }
                    _ => {
                        return fail(
                            Code::S010,
                            pos,
                            format!("a part of UInt[{width}] has no leaves"),
                        );
                    }
                };
                if let Some(len) = len {
                    stack.push(Frame {
                        ty: t,
                        side,
                        next: 0,
                        len,
                    });
                }
            }
            let Some(top) = stack.last_mut() else {
                return Ok(());
            };
            if top.next >= top.len {
                stack.pop();
                continue;
            }
            let part = top.next;
            top.next += 1;
            let (ct, step, offset) = self.child_of(pos, top.ty, part)?;
            let leaf = leaf_ty(self.tys.get(ct));
            let empty = leaf.is_none() && self.tys.meta(ct).leaves.is_zero();
            let env = (&mut self.graph, &mut self.paths);
            let idx = usize::try_from(part).unwrap_or(usize::MAX);
            let Some(child) = top
                .side
                .child(idx, (&step, offset, leaf.as_ref(), empty), pos, env)
            else {
                return fail(
                    Code::S010,
                    pos,
                    format!("a part of UInt[{width}] has no leaves"),
                );
            };
            visit = Some((ct, child));
        }
    }

    /// The hardware pack at `pos` into `UInt[width]` of the leaves of the parts `parts`, each
    /// with its type, in packing order (`Op::Pack`, section 7.4). The node has no charge here:
    /// the lowering charges each core node of a pack.
    pub(super) fn pack_hw(&mut self, pos: Pos, width: u32, parts: &[(TyId, Val)]) -> Res<HwId> {
        let mut leaves = Vec::new();
        for (ty, val) in parts {
            let side = match val {
                Val::Static(v) => Side::Val(v),
                Val::Hw(h) => Side::Hw(*h),
                Val::Agg(a) => Side::of_agg(a),
                Val::Handle(_) | Val::Pending(..) => {
                    return fail(
                        Code::S010,
                        pos,
                        format!("a part of UInt[{width}] has no leaves"),
                    );
                }
            };
            self.pack_collect(pos, width, (*ty, side), &mut leaves)?;
        }
        Ok(self.graph.mk(pos, Ty::UInt(width), Op::Pack(width), leaves))
    }

    /// The enum type that the data `d` has, if any.
    pub(super) fn enum_of(&self, d: &Opnd) -> Option<TyId> {
        let Opnd::Static(out) = d else {
            return None;
        };
        let t = match self.store.seen(out) {
            Seen::Static(Value::Enum(t, ..)) => *t,
            Seen::Agg(a) => a.stored_ty()?,
            _ => return None,
        };
        matches!(self.tys.get(t), Ty::Enum(_)).then_some(t)
    }

    /// `reinterpret` at `pos` between an enum and its bits (F26), after the copies of its
    /// arguments. The other side has exactly the type `UInt[W + P]`, else `S010` at the call.
    /// The tag is in the low `W` bits, and the payload in the next `P` bits.
    ///
    /// - A static unpack or pack charges the size of its result, as a conversion does
    ///   (section 5.4). It splits or joins the bits with no loop over the bits.
    /// - A hardware unpack of `b` gives an enum node with `(extract b 0 W)` and
    ///   `(extract b W P)`. Both leaves read `b`, so `b` gets one mark of a shared operand. The
    ///   mark charges the size of `b` after the type check. With `P` 0, the tag is `b`.
    /// - A hardware pack gives `(pack (W + P) tag payload)`. With `P` 0, it gives the tag leaf.
    /// - A hardware node has no charge here: the lowering charges each core node (section 7.4).
    pub(super) fn recast(&mut self, pos: Pos, to: TyId, d: Opnd) -> Res<Val> {
        if matches!(self.tys.get(to), Ty::Enum(_)) {
            return self.unpack(pos, to, &d);
        }
        let Some(from) = self.enum_of(&d) else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`reinterpret` needs an enum here, not {}",
                    self.opnd_text(&d)
                ),
            );
        };
        self.pack(pos, to, from, d)
    }

    /// The depth check of a new enum value of the type `t` at `pos` (section 5.5): 1 more than
    /// its type. It comes before the value, the charge, and the shared mark exist.
    pub(super) fn enum_depth(&self, pos: Pos, t: TyId) -> Res<()> {
        self.bounded(pos, 1 + t.depth().max(1))
    }

    /// The enum value of the type `to` from the bits `d`.
    pub(super) fn unpack(&mut self, pos: Pos, to: TyId, d: &Opnd) -> Res<Val> {
        let Some(widths) = self.tys.widths(to) else {
            return fail(
                Code::S010,
                pos,
                format!("{} has no entry", self.tys.text(to)),
            );
        };
        let total = widths.tag + widths.payload;
        let bad = |ev: &Self| {
            fail(
                Code::S010,
                pos,
                format!(
                    "`reinterpret` makes {} only from UInt[{total}], not {}",
                    ev.tys.text(to),
                    ev.opnd_text(d)
                ),
            )
        };
        match d {
            Opnd::Static(out) => {
                let Seen::Static(Value::UInt(x)) = self.store.seen(out) else {
                    return bad(self);
                };
                if x.width() != total {
                    return bad(self);
                }
                self.enum_depth(pos, to)?;
                let x = x.clone();
                // The size does not read the bits, so the charge comes before the split.
                let size = 1
                    + width_size(widths.tag)
                    + if widths.payload == 0 {
                        0
                    } else {
                        width_size(widths.payload)
                    };
                self.charge(pos, u128::from(size))?;
                let tag = x.extract(0, widths.tag);
                let payload = (widths.payload > 0).then(|| x.extract(widths.tag, widths.payload));
                Ok(Val::Static(Value::Enum(to, tag, payload)))
            }
            Opnd::Hw(b) => {
                let b = *b;
                if self.graph.ty(b) != Ty::UInt(total) {
                    return bad(self);
                }
                self.enum_depth(pos, to)?;
                let parts = if widths.payload == 0 {
                    vec![Agg::Hw(b)]
                } else {
                    let env = (&mut self.fuel, &mut self.graph, &mut self.naming);
                    let b = share(pos, 2, env, b)?;
                    let tag_ty = Ty::UInt(widths.tag);
                    let extract = Op::Extract {
                        off: 0,
                        w: widths.tag,
                    };
                    let tag = self.graph.mk(pos, tag_ty, extract, vec![b]);
                    let payload_ty = Ty::UInt(widths.payload);
                    let extract = Op::Extract {
                        off: widths.tag,
                        w: widths.payload,
                    };
                    let payload = self.graph.mk(pos, payload_ty, extract, vec![b]);
                    vec![Agg::Hw(tag), Agg::Hw(payload)]
                };
                let Some(node) = Agg::node(&self.graph, &self.tys, to, parts) else {
                    return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
                };
                Ok(node.into_val())
            }
        }
    }

    /// The bits `UInt[W + P]` of the enum value `d` of the enum type `from`.
    fn pack(&mut self, pos: Pos, to: TyId, from: TyId, d: Opnd) -> Res<Val> {
        let Some(widths) = self.tys.widths(from) else {
            return fail(
                Code::S010,
                pos,
                format!("{} has no entry", self.tys.text(from)),
            );
        };
        let total = widths.tag + widths.payload;
        if *self.tys.get(to) != Ty::UInt(total) {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`reinterpret` gives the bits of {} only as UInt[{total}], not {}",
                    self.tys.text(from),
                    self.tys.text(to)
                ),
            );
        }
        let Opnd::Static(out) = d else {
            return fail(Code::S010, pos, "an enum is not hardware data".to_owned());
        };
        if let Seen::Static(Value::Enum(_, tag, payload)) = self.store.seen(&out) {
            let bits = match payload {
                Some(p) => p.concat(tag),
                None => tag.clone(),
            };
            self.charge(pos, u128::from(width_size(total)))?;
            return Ok(Val::Static(Value::UInt(bits)));
        }
        let val = self.store.take(out);
        let h = self.pack_hw(pos, total, &[(from, val)])?;
        if widths.payload == 0
            && let Some(Node { args, .. }) = self.graph.node(h)
            && let [tag] = args.as_slice()
        {
            return Ok(Val::Hw(*tag));
        }
        Ok(Val::Hw(h))
    }

    /// The hardware unpack of the payload leaf `y` from the bit `off` into a value of the type
    /// `t` at `pos` (section 7.4). A data scalar is one `extract` node of `y`, charged as a
    /// hardware operation with one operand: 2. A part without a leaf is its static value, which
    /// the metadata tells with no walk. The other parts keep the packing order. The zero size of
    /// the binder type paid for the walk before (section 5.4). The walk keeps its own stack.
    pub(super) fn unpack_hw(&mut self, pos: Pos, y: HwId, t: TyId, off: u64) -> Res<Agg> {
        enum Step {
            Visit(TyId, u64),
            Node(TyId, usize),
        }
        let mut done: Vec<Agg> = Vec::new();
        let mut work = vec![Step::Visit(t, off)];
        while let Some(step) = work.pop() {
            let (t, off) = match step {
                Step::Visit(t, off) => (t, off),
                Step::Node(t, n) => {
                    let xs = done.split_off(done.len().saturating_sub(n));
                    let Some(node) = Agg::node(&self.graph, &self.tys, t, xs) else {
                        return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
                    };
                    done.push(node);
                    continue;
                }
            };
            if self.tys.meta(t).leaves.is_zero() {
                let Some(v) = crate::unpack::unpack(&self.tys, &[], t, off) else {
                    return fail(
                        Code::S010,
                        pos,
                        format!("{} has no static unpack", self.tys.text(t)),
                    );
                };
                done.push(Agg::Static(v));
                continue;
            }
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Unpacked, 1);
            match self.tys.get(t).clone() {
                scalar @ (Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) => {
                    let width = u32::try_from(self.tys.meta(t).width.to_u64().unwrap_or(0))
                        .unwrap_or(u32::MAX);
                    let start = u32::try_from(off).unwrap_or(u32::MAX);
                    let op = Op::Extract {
                        off: start,
                        w: width,
                    };
                    let Val::Hw(h) = self.node(pos, scalar, op, vec![y])? else {
                        return fail(Code::S010, pos, "an extract is hardware".to_owned());
                    };
                    done.push(Agg::Hw(h));
                }
                Ty::Array(elem, len) => {
                    let n = usize::try_from(len.to_u64().unwrap_or(0)).unwrap_or(0);
                    let width = self.tys.meta(elem).width.to_u64().unwrap_or(0);
                    work.push(Step::Node(t, n));
                    work.extend(
                        (0..n as u64).rev().map(|k| {
                            Step::Visit(elem, off.saturating_add(k.saturating_mul(width)))
                        }),
                    );
                }
                Ty::Tuple(parts) => {
                    work.push(Step::Node(t, parts.len()));
                    work.extend(parts.iter().enumerate().rev().map(|(k, part)| {
                        Step::Visit(*part, off.saturating_add(self.tys.offset(t, k as u64)))
                    }));
                }
                Ty::Struct(_) | Ty::Enum(_) => {
                    let Some(parts) = self.tys.parts(t) else {
                        return fail(
                            Code::S010,
                            pos,
                            format!("{} has no specialization", self.tys.text(t)),
                        );
                    };
                    let parts = parts.types.to_vec();
                    work.push(Step::Node(t, parts.len()));
                    work.extend(parts.iter().enumerate().rev().map(|(k, part)| {
                        Step::Visit(*part, off.saturating_add(self.tys.offset(t, k as u64)))
                    }));
                }
                other => {
                    return fail(
                        Code::S010,
                        pos,
                        format!("{} is not hardware data", self.tys.text_of(&other)),
                    );
                }
            }
        }
        match done.pop() {
            Some(a) => Ok(a),
            None => fail(Code::S010, pos, "the unpack has no value".to_owned()),
        }
    }
}
