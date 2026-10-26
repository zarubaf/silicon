// SPDX-License-Identifier: Apache-2.0
//! The queries `@TypeOf` and `@typeInfo` of a hardware name (front-end spec
//! 9.3, ADR 0032).
//!
//! A query reads a name that the builder declared, so the builder knows the
//! type and writes the static result as the value of the query node. Three
//! forms use it:
//!
//! - a group, `let s0: Nat = @typeInfo(@TypeOf(w0)).width;` with a
//!   `diagnostic` of the result;
//! - a width, `wire w1: UInt[data_bits(@TypeOf(i0))];`, which a port or a
//!   vector then shows;
//! - a mix of the low bit of a result into an output, so that the twin and
//!   the run oracle see the value: `o0 := o1 ^ UInt[4](@typeInfo(@TypeOf(w0)).width & 1)`.
//!
//! Every draw comes from the query tape (`on_query`), which no other form
//! reads, and the names that a query can read live in `Builder::ops`, which
//! only this tape reads. A program with no query is thus the program of the
//! other tapes alone.

use super::hw::Want;
use super::inst::Child;
use super::reflect::{self, RTy};
use super::{Builder, Built, Ctx, Lane, Names};
use crate::eval::Value;
use crate::program::{HBin, HExpr, QExpr, Query, SBin, SExpr, STy, Scalar, Stmt, Ty, Un, string};
use num_bigint::BigInt;

/// A name that a query can read: its text and the type that the builder
/// drew for it.
#[derive(Clone, Debug)]
pub(super) struct Op {
    text: String,
    ty: RTy,
}

/// One statement of a frame in this many is followed by a group, and the
/// most groups of a program.
const GROUP_ODDS: u32 = 36;
const MAX_GROUPS: u32 = 12;
/// A module mixes a query into its outputs in this many modules.
const MIX_ODDS: u32 = 8;
/// A wire or a register takes a query as its width in this many.
const WIDTH_ODDS: u32 = 1;

/// The tags of the kinds that the operands have.
const KINDS: [&str; 6] = ["bool", "uint", "sint", "reg", "wire", "input"];

/// `e` with the arguments `args` for the parameters `params`, or `None` for
/// a form that a width of a port does not take.
fn substitute(e: &SExpr, params: &[(String, STy)], args: &[SExpr]) -> Option<SExpr> {
    let sub = |e: &SExpr| substitute(e, params, args).map(Box::new);
    Some(match e {
        SExpr::Int(..) | SExpr::Bool(_) => e.clone(),
        SExpr::Name(n) => match params.iter().position(|(p, _)| p == n) {
            Some(at) => args.get(at)?.clone(),
            None => e.clone(),
        },
        SExpr::Unary(op, a) => SExpr::Unary(*op, sub(a)?),
        SExpr::Binary(op, a, b) => SExpr::Binary(*op, sub(a)?, sub(b)?),
        SExpr::If(c, t, f) => SExpr::If(sub(c)?, sub(t)?, sub(f)?),
        SExpr::Call(f, xs) => SExpr::Call(
            f.clone(),
            xs.iter()
                .map(|x| substitute(x, params, args))
                .collect::<Option<_>>()?,
        ),
        _ => return None,
    })
}

fn int(n: usize) -> SExpr {
    SExpr::Int(BigInt::from(n), crate::program::Radix::Dec)
}

fn builtin(name: &str, arg: QExpr) -> QExpr {
    QExpr::Builtin(name.to_owned(), vec![arg])
}

fn read(base: QExpr, suffix: &str) -> QExpr {
    QExpr::Read(Box::new(base), suffix.to_owned())
}

impl Builder {
    /// Runs `f` on the query tape, isolated from the other tapes.
    pub(super) fn on_query<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        self.isolated(Lane::Query, f)
    }

    /// Makes the name `text` of the type `t` readable to the queries of the
    /// frame, if the type is one that a query reflects.
    pub(super) fn add_op(&mut self, text: &str, ty: Option<RTy>) {
        if let Some(ty) = ty {
            self.ops.push(Op {
                text: text.to_owned(),
                ty,
            });
        }
    }

    /// A write to the root `root` changes what a width over it means: the
    /// names whose type reads it leave the pool.
    pub(super) fn forget_ops(&mut self, root: &str) {
        self.ops.retain(|op| !op.ty.reads(root));
    }

    /// Makes the outputs and the inputs of the child readable to queries:
    /// the type of a port with the arguments of the instance in place of the
    /// parameters of the child.
    pub(super) fn expose_child_ops(&mut self, child: &Child) {
        let outer = |t: &Ty| {
            let (Ty::UInt(w) | Ty::SInt(w)) = t else {
                return RTy::of(t);
            };
            let w = substitute(w, &child.sig.params, &child.args)?;
            let t = if matches!(t, Ty::SInt(_)) {
                Ty::SInt(w)
            } else {
                Ty::UInt(w)
            };
            RTy::of(&t)
        };
        for (q, t) in &child.sig.outputs {
            self.add_op(&format!("{}.{q}", child.name), outer(t));
        }
        for (p, t) in &child.sig.inputs {
            let ty = outer(t).map(|t| RTy::Input(Box::new(t)));
            self.add_op(&format!("{}.{p}", child.name), ty);
        }
    }

    /// A name of the pool. Half of the draws take a handle, if there is one,
    /// because only a handle has an `element`.
    fn pick_op(&mut self) -> Option<Op> {
        let handles: Vec<&Op> = self
            .ops
            .iter()
            .filter(|op| reflect::info(&op.ty).element.is_some())
            .collect();
        let handle = self.tape.flag();
        let at = self.tape.index(self.ops.len());
        let pick = self.tape.index(handles.len());
        match handles.get(pick) {
            Some(op) if handle => Some((*op).clone()),
            _ => self.ops.get(at).cloned(),
        }
    }

    /// The type value of `op`: `@TypeOf(x)`, or the `element` of that type
    /// if it has one. With `data`, a handle gives its element.
    fn type_value(&mut self, op: &Op, data: bool) -> (QExpr, RTy) {
        let of = builtin("TypeOf", QExpr::Text(op.text.clone()));
        let element = reflect::info(&op.ty).element;
        if let Some(element) = element
            && (data || self.tape.below(4) != 0)
        {
            let info = builtin("typeInfo", of);
            return (read(info, ".element"), element);
        }
        (of, op.ty.clone())
    }

    /// A numeric read of the type value `tq` of the drawn type `t`: the
    /// query and its static result. A `varying` read is a width, which
    /// differs between names, not a length that is mostly 0.
    fn size(&mut self, tq: QExpr, t: &RTy, varying: bool) -> (QExpr, SExpr) {
        let info = reflect::info(t);
        let reads = |suffix| read(builtin("typeInfo", tq.clone()), suffix);
        let pick = if varying {
            2 + self.tape.below(2)
        } else {
            self.tape.below(4)
        };
        match pick {
            0 => (reads(".length"), info.length),
            1 => (
                QExpr::Call("len", Box::new(reads(".fields"))),
                int(info.fields),
            ),
            2 => match reflect::data_bits(t) {
                Some(bits) => (QExpr::Call("data_bits", Box::new(tq)), bits),
                None => (reads(".width"), info.width),
            },
            _ => (reads(".width"), info.width),
        }
    }

    /// The `.kind` test of the type value `tq`: it holds for the true tag
    /// and fails for another one.
    fn kind(&mut self, tq: QExpr, t: &RTy) -> (QExpr, SExpr) {
        let truth = reflect::info(t).kind;
        let tag = if self.tape.flag() {
            truth
        } else {
            let others: Vec<&str> = KINDS.iter().copied().filter(|k| *k != truth).collect();
            others
                .get(self.tape.index(others.len()))
                .copied()
                .unwrap_or(truth)
        };
        let kind = read(builtin("typeInfo", tq), ".kind");
        let test = QExpr::Eq(Box::new(kind), Box::new(QExpr::Text(string(tag))));
        (test, SExpr::Bool(tag == truth))
    }

    /// A group of statements after a statement of the frame, if the query
    /// tape says so: a static `let` of one query, and its record.
    pub(super) fn query_group(
        &mut self,
        ctx: &Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> Built {
        if self.queries >= MAX_GROUPS || self.ops.is_empty() || ctx.envs.is_empty() {
            return Ok(());
        }
        self.on_query(|b| {
            if b.tape.below(GROUP_ODDS) != GROUP_ODDS - 1 {
                return Ok(());
            }
            let Some(op) = b.pick_op() else {
                return Ok(());
            };
            let (tq, t) = b.type_value(&op, false);
            let boolean = b.tape.flag();
            let (form, value) = if boolean {
                b.kind(tq, &t)
            } else {
                b.size(tq, &t, false)
            };
            if b.values(&value, &ctx.envs).is_none() {
                return Ok(());
            }
            b.queries += 1;
            note!(b, query_groups);
            let name = names.fresh("s");
            let ty = if boolean { STy::Bool } else { STy::Nat };
            let query = SExpr::Query(Box::new(Query { form, value }));
            out.push(Stmt::StaticLet(name.clone(), ty, query));
            let message = b.next_message();
            out.push(Stmt::Diagnostic(message, SExpr::Name(name)));
            Ok(())
        })
    }

    /// The width `w` of a wire or a register as a query on a name of the
    /// same width, in one declaration in `WIDTH_ODDS`: the result of the
    /// query is `w` in each env of the frame.
    pub(super) fn query_ty(&mut self, ctx: &Ctx, ty: Ty, want: &Want) -> Ty {
        let (Ty::UInt(w) | Ty::SInt(w)) = &ty else {
            return ty;
        };
        let signed = matches!(ty, Ty::SInt(_));
        let widths: Vec<u32> = want
            .types
            .iter()
            .filter_map(|t| match t {
                Scalar::UInt(w) | Scalar::SInt(w) => Some(*w),
                Scalar::Bool => None,
            })
            .collect();
        if self.ops.is_empty() || widths.len() != ctx.envs.len() {
            return ty;
        }
        let w = w.clone();
        let query = self.on_query(|b| {
            if b.tape.below(WIDTH_ODDS) != 0 {
                return None;
            }
            let same = |op: &&Op| {
                let Some((bits, is_signed)) = op.ty.data() else {
                    return false;
                };
                is_signed == signed
                    && b.values(&bits, &ctx.envs).is_some_and(|vs| {
                        vs.iter()
                            .zip(&widths)
                            .all(|(v, w)| *v == Value::Int(BigInt::from(*w)))
                    })
            };
            let ops: Vec<Op> = b.ops.iter().filter(same).cloned().collect();
            let op = ops.get(b.tape.index(ops.len()))?;
            let (tq, _) = b.type_value(op, true);
            note!(b, query_widths);
            Some(SExpr::Query(Box::new(Query {
                form: QExpr::Call("data_bits", Box::new(tq)),
                value: w,
            })))
        });
        match (query, signed) {
            (Some(q), false) => Ty::UInt(q),
            (Some(q), true) => Ty::SInt(q),
            (None, _) => ty,
        }
    }

    /// The outputs with the low bit of a query mixed into one of them, in
    /// one module in `MIX_ODDS`: `old ^ T(query & 1)`, or `old != (query & 1) == 1`
    /// for a `Bool`. The twin writes the result of the query, so its outputs
    /// differ from the program if the generator and a front end disagree
    /// on a type that the output reads.
    pub(super) fn mix_query(&mut self, outputs: &mut [(String, Want, HExpr)]) {
        if self.ops.is_empty() || outputs.is_empty() {
            return;
        }
        let ops = self.ops.clone();
        self.on_query(|b| {
            if b.tape.below(MIX_ODDS) != 0 {
                return;
            }
            let at = b.tape.index(outputs.len());
            let Some(op) = ops.get(b.tape.index(ops.len())) else {
                return;
            };
            let Some((_, want, driver)) = outputs.get_mut(at) else {
                return;
            };
            let Some(ty) = want.printable() else { return };
            let (tq, t) = b.type_value(op, false);
            let (form, value) = b.size(tq, &t, true);
            let number = SExpr::Query(Box::new(Query { form, value }));
            let low = SExpr::Binary(SBin::And, Box::new(number), Box::new(int(1)));
            let (op, mixed) = match ty {
                Ty::Bool => {
                    let one = SExpr::Binary(SBin::Eq, Box::new(low), Box::new(int(1)));
                    (HBin::Ne, HExpr::Static(one))
                }
                Ty::UInt(_) => (HBin::Xor, HExpr::Make(ty, low)),
                Ty::SInt(_) => {
                    let negative = SExpr::Unary(Un::Neg, Box::new(low));
                    (HBin::Xor, HExpr::Make(ty, negative))
                }
                Ty::Enum(_) => return,
            };
            let old = std::mem::replace(driver, HExpr::Unit);
            *driver = HExpr::Binary(op, Box::new(old), Box::new(mixed));
            note!(b, query_mixes);
        });
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::tapes;
    use super::*;
    use std::collections::BTreeMap;

    /// The forms of the queries in a program.
    fn forms(text: &str, s: &super::super::Stats) -> [(&'static str, bool); 6] {
        [
            ("any query", text.contains("@TypeOf")),
            ("group", s.query_groups > 0),
            ("width", s.query_widths > 0),
            ("mix", s.query_mixes > 0),
            ("kind test", text.contains(".kind == ")),
            ("element", text.contains(".element")),
        ]
    }

    /// Each form of the queries occurs in at least 10% of 256 programs, and
    /// some program has no query.
    #[test]
    fn programs_cover_the_queries() {
        const TAPES: usize = 256;
        let mut with = BTreeMap::<&str, usize>::new();
        for tape in tapes(TAPES) {
            let mut b = Builder::new(tape);
            let p = b.program();
            assert!(p.is_ok(), "a program faults: {p:?}");
            let Ok(p) = p else { continue };
            assert!(b.queries <= MAX_GROUPS, "{} groups", b.queries);
            for (form, seen) in forms(&p.text(), &b.stats) {
                *with.entry(form).or_default() += usize::from(seen);
            }
        }
        for (form, n) in &with {
            assert!(n * 10 >= TAPES, "{form} occurs in {n} of {TAPES}: {with:?}");
        }
    }
}
