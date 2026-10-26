// SPDX-License-Identifier: Apache-2.0
//! A wire or a register of a record type of hardware data, read through
//! `@field` (front-end spec 9.3, #399).
//!
//! ```text
//! struct I0 { d0: UInt[4], d1: SInt[3] }
//! struct R0 { d0: I0, d1: UInt[5] }
//! wire w0: R0;
//! w0 := R0(I0(i0, 1), i1);
//! let l0 = @field(@field(w0, "d0"), ("d" + str(f0(2) + 1)));
//! ```
//!
//! The wire is a handle, so the first step of a chain reads its base as a
//! handle, and the name of the step pays before the next key evaluates. A
//! key with a call in the later step thus tests the order of the charges. A
//! leaf joins the pool of the port tape, so `mix_port` mixes it into an
//! output and the main tape never sees it.
//!
//! A group draws from its own tape alone, and every group holds at least
//! one `@field`, so a program without one is the program of the other tapes.

use super::held::EFFECT;
use super::hw::{DEPTH, Want, literal_ty};
use super::reflect::RTy;
use super::stat::Reach;
use super::stat::{bin, int};
use super::{Builder, Built, Ctx, Helper, Hw, Lane, Module};
use crate::program::{
    FieldTy, HExpr, Item, Place, RecTy, SBin, SExpr, STy, Scalar, Stmt, StructDef, Ty,
};

/// One statement of the top frame in this many is followed by a group, and
/// the most groups of one program.
const REC_ODDS: u32 = 48;
const MAX_RECS: u32 = 1;

/// What a record name is: a register, a wire, or a `let mut` value.
#[derive(Clone, Copy)]
enum Held {
    Reg,
    Wire,
    Value,
}

/// The leaves of a record `R<k>`: the fields `d0.d0`, `d0.d1`, and `d1`.
const LEAVES: usize = 3;

impl Builder {
    /// A group of statements after a statement of the top frame of a module,
    /// if the record tape says so.
    pub(super) fn record_group(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        if self.recs >= MAX_RECS || ctx.envs.is_empty() {
            return Ok(());
        }
        self.isolated(Lane::Rec, |b| {
            if b.tape.below(REC_ODDS) != REC_ODDS - 1 {
                return Ok(());
            }
            b.recs += 1;
            b.record_stmts(ctx, m, out);
            if b.tape.flag() {
                b.record_double(m, out)?;
            }
            Ok(())
        })
    }

    /// The structs, the declaration, the `:=`, and the reads of one group.
    fn record_stmts(&mut self, ctx: &mut Ctx, m: &mut Module, out: &mut Vec<Stmt>) {
        let envs = ctx.envs.len();
        let id = self.rec_defs.len() / 2;
        let (inner, outer) = (format!("I{id}"), format!("R{id}"));
        let mut leaves: Vec<Scalar> = (0..LEAVES)
            .map(|_| {
                let w = self.tape.between(1, 8);
                if self.tape.flag() {
                    Scalar::UInt(w)
                } else {
                    Scalar::SInt(w)
                }
            })
            .collect();
        // Three groups in four, where a helper exists, pass a leaf to a helper with a `mut` formal
        // of the type of that leaf.
        let helper = self.record_helper().filter(|_| self.tape.below(4) != 0);
        let mut_leaf = helper.as_ref().map(|(_, root)| {
            let at = 1 + self.tape.index(2);
            if let Some(slot) = leaves.get_mut(at) {
                *slot = *root;
            }
            at
        });
        let field = |t: Scalar| match t {
            Scalar::SInt(_) => FieldTy::SInt(width(t)),
            _ => FieldTy::UInt(width(t)),
        };
        let at = |i: usize| leaves.get(i).copied().unwrap_or(Scalar::Bool);
        self.rec_defs.push(StructDef {
            name: inner.clone(),
            params: Vec::new(),
            fields: vec![
                ("d0".to_owned(), field(at(0))),
                ("d1".to_owned(), field(at(1))),
            ],
        });
        self.rec_defs.push(StructDef {
            name: outer.clone(),
            params: Vec::new(),
            fields: vec![
                ("d0".to_owned(), FieldTy::Rec(inner.clone())),
                ("d1".to_owned(), field(at(2))),
            ],
        });
        if let (Some((h, _)), Some(at)) = (&helper, mut_leaf) {
            let name = m.names.fresh("v");
            let [x, y, z] = [0, 1, 2]
                .map(|i| self.driver_at(ctx, &Want::uniform(at_leaf(&leaves, i), envs), 2));
            let value = HExpr::Record(
                outer.clone(),
                vec![HExpr::Record(inner.clone(), vec![x, y]), z],
            );
            out.push(Stmt::Let {
                name: name.clone(),
                mutable: true,
                ty: Some(Ty::Rec(outer.clone())),
                value,
            });
            self.record_ops(&name, Held::Value, (&inner, &outer), &leaves);
            self.probe_field(ctx, &name, out);
            self.record_mut_call(ctx, m, (h, &name, at), out);
            for _ in 0..self.tape.between(1, 2) {
                self.record_read(ctx, m, &name, (&leaves, envs), out);
            }
            return;
        }
        let register = m.clocked && self.tape.below(3) != 0;
        let name = m.names.fresh(if register { "r" } else { "w" });
        if register {
            let reach = self.reach(ctx);
            let [x, y, z] = [0, 1, 2].map(|i| self.fit(&vec![at(i); envs], reach, &ctx.envs));
            let inner_reset = SExpr::Record(inner.clone(), Vec::new(), vec![x, y]);
            let reset = SExpr::Record(outer.clone(), Vec::new(), vec![inner_reset, z]);
            out.push(Stmt::Reg(name.clone(), Ty::Rec(outer.clone()), reset));
            self.record_ops(&name, Held::Reg, (&inner, &outer), &leaves);
            self.probe_field(ctx, &name, out);
            note!(self, rec_regs);
        } else {
            out.push(Stmt::Wire(name.clone(), Ty::Rec(outer.clone())));
            self.record_ops(&name, Held::Wire, (&inner, &outer), &leaves);
            self.probe_field(ctx, &name, out);
            note!(self, rec_wires);
        }
        let [x, y, z] = [0, 1, 2].map(|i| self.driver_at(ctx, &Want::uniform(at(i), envs), 2));
        let value = HExpr::Record(
            outer.clone(),
            vec![HExpr::Record(inner.clone(), vec![x, y]), z],
        );
        out.push(Stmt::Connect(Place::Name(name.clone()), value));
        for _ in 0..self.tape.between(1, 2) {
            self.record_read(ctx, m, &name, (&leaves, envs), out);
        }
    }

    /// Two calls of the function that runs a `diagnostic` in one chain, one
    /// in the key of each step, each on a local of its own:
    ///
    /// ```text
    /// let s5: Int = @field(@field(s2, k0(s3, 1)), k0(s4, 2));
    /// diagnostic("d3", (s5, s3, s4));
    /// ```
    ///
    /// The records come in the order of the base, then the key.
    fn record_double(&mut self, m: &mut Module, out: &mut Vec<Stmt>) -> Built {
        let func = self.key_fn(EFFECT)?;
        let names = [(); 4].map(|()| m.names.fresh("s"));
        let [cont, first, second, got] = names.clone();
        let name = |n: &String| SExpr::Name(n.clone());
        let (ty, value, tuple) = self.small_container();
        let call = |b: &mut Builder, root: &String| {
            let arg = i64::from(b.tape.between(0, 5));
            SExpr::KeyCall(func.clone(), root.clone(), Box::new(int(arg)))
        };
        let (k1, k2) = (call(self, &first), call(self, &second));
        let inner = SExpr::At(Box::new(name(&cont)), Box::new(k1));
        let read = if tuple || self.tape.flag() {
            SExpr::At(Box::new(inner), Box::new(k2))
        } else {
            SExpr::Index(Box::new(inner), Box::new(k2))
        };
        let start = |b: &mut Builder| int(i64::from(b.tape.between(0, 1)));
        let (a, b) = (start(self), start(self));
        let shown = SExpr::Tuple(vec![name(&got), name(&first), name(&second)]);
        out.extend([
            Stmt::StaticLet(cont, ty, value),
            Stmt::MutLet(first, STy::Int, a),
            Stmt::MutLet(second, STy::Int, b),
            Stmt::StaticLet(got, STy::Int, read),
            Stmt::Diagnostic(self.next_message(), shown),
        ]);
        note!(self, double_calls);
        Ok(())
    }

    /// `let l = g(<leaf>, e);` or `let l = <leaf>.g(e);`: the leaf `at` of
    /// the record `name` is the `mut` actual of the helper `h`.
    fn record_mut_call(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        (h, name, at): (&Helper, &str, usize),
        out: &mut Vec<Stmt>,
    ) {
        let envs = ctx.envs.len();
        let reach = self.reach(ctx);
        let place = self.record_place(name, at, reach);
        let (extra_ty, extra) = h.params.get(1).map(|(_, t, s)| (t.clone(), *s)).unzip();
        let want = Want {
            types: vec![extra.unwrap_or(Scalar::Bool); envs],
            ty: extra_ty,
        };
        let arg = self.value(ctx, &want, DEPTH);
        let call = if self.tape.flag() {
            HExpr::Receiver(Box::new(place), h.name.clone(), vec![arg])
        } else {
            HExpr::Call(h.name.clone(), vec![place, arg])
        };
        let result = m.names.fresh("l");
        out.push(Stmt::Let {
            name: result.clone(),
            mutable: false,
            ty: None,
            value: call,
        });
        ctx.port.push(Hw {
            expr: HExpr::Name(result),
            ty: Some(h.ret.0.clone()),
            types: vec![h.ret.1; envs],
            mutable: false,
        });
        note!(self, rec_mut_calls);
    }

    /// `let l = <leaf>;` for a leaf of the record `name`, read through a
    /// chain of `@field`, and the leaf as a hardware value of the frame.
    fn record_read(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        name: &str,
        (leaves, envs): (&[Scalar], usize),
        out: &mut Vec<Stmt>,
    ) {
        let i = self.tape.index(LEAVES);
        let Some(&t) = leaves.get(i) else { return };
        let r = self.reach(ctx);
        let read = self.record_place(name, i, r);
        let local = m.names.fresh("l");
        self.add_root(&local, RTy::of(&literal_ty(t)));
        out.push(Stmt::Let {
            name: local.clone(),
            mutable: false,
            ty: None,
            value: read,
        });
        ctx.port.push(Hw {
            expr: HExpr::Name(local),
            ty: Some(literal_ty(t)),
            types: vec![t; envs],
            mutable: false,
        });
    }

    /// The chain of `@field` from the record `name` to its leaf `i`: two
    /// steps for a leaf of the inner record, one for the other.
    fn record_place(&mut self, name: &str, i: usize, r: Reach<'_>) -> HExpr {
        let root = HExpr::Name(name.to_owned());
        if i < 2 {
            note!(self, rec_chains);
            let first = self.leaf_key("d0", r);
            let base = HExpr::FieldOf(Box::new(root), first);
            let second = self.leaf_key(&format!("d{i}"), r);
            HExpr::FieldOf(Box::new(base), second)
        } else {
            let key = self.leaf_key("d1", r);
            HExpr::FieldOf(Box::new(root), key)
        }
    }

    /// A helper with a `mut` first formal of a finite integer type, and the
    /// concrete type of that formal.
    fn record_helper(&mut self) -> Option<(Helper, Scalar)> {
        let found: Vec<(Helper, Scalar)> = self
            .mut_helpers
            .iter()
            .filter_map(|h| {
                let (_, _, root) = h.params.first()?;
                matches!(root, Scalar::UInt(_) | Scalar::SInt(_)).then(|| (h.clone(), *root))
            })
            .collect();
        found.get(self.tape.index(found.len())).cloned()
    }

    /// The names of a record that `@TypeOf` reflects, with no read: the
    /// record as a register, a wire, or a value, its inner record, and each
    /// leaf (front-end spec 9.3).
    fn record_ops(
        &mut self,
        name: &str,
        held: Held,
        (inner, outer): (&str, &str),
        leaves: &[Scalar],
    ) {
        let leaf = |i: usize| match at_leaf(leaves, i) {
            Scalar::UInt(w) => STy::UInt(w),
            Scalar::SInt(w) => STy::SInt(w),
            Scalar::Bool => STy::Bool,
        };
        let record = |name: &str, fields: Vec<(&str, STy)>| {
            STy::Record(Box::new(RecTy {
                name: name.to_owned(),
                args: Vec::new(),
                fields: fields.into_iter().map(|(f, t)| (f.to_owned(), t)).collect(),
            }))
        };
        let inner_ty = record(inner, vec![("d0", leaf(0)), ("d1", leaf(1))]);
        let whole = RTy::from_static(&record(
            outer,
            vec![("d0", inner_ty.clone()), ("d1", leaf(2))],
        ));
        let top = match held {
            Held::Reg => RTy::Reg(Box::new(whole)),
            Held::Wire => RTy::Wire(Box::new(whole)),
            Held::Value => whole,
        };
        self.add_root(name, Some(top));
        self.add_root(&format!("{name}.d1"), Some(RTy::from_static(&leaf(2))));
        self.add_root(&format!("{name}.d0"), Some(RTy::from_static(&inner_ty)));
        self.add_root(&format!("{name}.d0.d0"), Some(RTy::from_static(&leaf(0))));
        self.add_root(&format!("{name}.d0.d1"), Some(RTy::from_static(&leaf(1))));
    }

    /// A record with a read of the type of a field of the record `name`,
    /// which no read of the value comes before: the whole record, the inner
    /// record, or a leaf.
    fn probe_field(&mut self, ctx: &Ctx, name: &str, out: &mut Vec<Stmt>) {
        let paths = ["", ".d1", ".d0", ".d0.d0", ".d0.d1"];
        let at = self.tape.index(paths.len());
        let path = paths.get(at).copied().unwrap_or_default();
        self.probe_root(ctx, &format!("{name}{path}"), out);
    }

    /// The key of the leaf of a chain: half of them call a function, so that
    /// the key evaluates after the name of the step before it pays.
    fn leaf_key(&mut self, field: &str, r: Reach<'_>) -> SExpr {
        let literal = SExpr::Str(field.to_owned());
        let (letter, digits) = field.split_at(field.len().min(1));
        match (self.tape.below(4), digits.parse::<i64>()) {
            (1, Ok(k)) => bin(
                SBin::Add,
                SExpr::Str(letter.to_owned()),
                SExpr::StrOf(Box::new(int(k))),
            ),
            (2 | 3, _) => self.call_name_key(field, r).unwrap_or(literal),
            _ => literal,
        }
    }

    /// The items of the records so far.
    pub(super) fn rec_items(&self) -> impl Iterator<Item = Item> + '_ {
        self.rec_defs.iter().cloned().map(Item::Struct)
    }
}

/// The type of the leaf `i`.
fn at_leaf(leaves: &[Scalar], i: usize) -> Scalar {
    leaves.get(i).copied().unwrap_or(Scalar::Bool)
}

/// The literal width of a leaf.
fn width(t: Scalar) -> SExpr {
    match t {
        Scalar::UInt(w) | Scalar::SInt(w) => super::stat::int(i64::from(w)),
        Scalar::Bool => super::stat::int(1),
    }
}

#[cfg(test)]
mod tests {
    use super::super::build;
    use super::super::tests::tapes;

    /// A group declares two structs, a wire, a register, or a `let mut` of the
    /// outer one, and reads a leaf with `@field`. The twin has one wire or register for
    /// each leaf and no struct of hardware data.
    #[test]
    fn a_group_declares_a_record_and_the_twin_flattens_it() {
        let mut found = 0;
        for tape in tapes(256) {
            let Ok(p) = build(tape) else { continue };
            let text = p.text();
            if !text.contains("struct R0 {") {
                continue;
            }
            found += 1;
            assert!(text.contains("struct I0 {"), "{text}");
            assert!(text.contains(": R0"), "{text}");
            assert!(text.contains("@field("), "{text}");
            let twin = crate::twin(&p).text;
            assert!(!twin.contains("struct R0"), "{twin}");
            assert!(twin.contains("_d1"), "{twin}");
        }
        assert!(found >= 10, "{found}");
    }
}
