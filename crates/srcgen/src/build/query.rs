// SPDX-License-Identifier: Apache-2.0
//! The queries `@TypeOf` and `@typeInfo` (front-end spec 9.3, ADR 0032).
//!
//! A query reads a name or a type that the builder drew, so the builder
//! knows the answer and writes it as the value of the query node. The
//! sources are the hardware names of the open frames (inputs, registers,
//! wires, the ports of a child, the child itself), the static names (a
//! parameter, a `const`, a static `let`, and the parts of a container), the
//! functions, and type literals. The builder picks the kind of the type
//! first, then a source of that kind, so that each kind is as likely as
//! another. Three forms use a query:
//!
//! - a group, `let s0: Nat = @typeInfo(@TypeOf(z0)).width;` with a
//!   `diagnostic` of the result;
//! - a width, `wire z1: UInt[data_bits(@TypeOf(i0))];`, which a port or a
//!   vector then shows;
//! - a mix of the low bit of a result into an output, so that the twin and
//!   the run oracle see the value: `o0 := o1 ^ UInt[4](@typeInfo(@TypeOf(z0)).width & 1)`.
//!
//! Every draw comes from the query tape (`on_query`), which no other form
//! reads, and the names that a query can read live in `Builder::ops`, which
//! only this tape reads. One program in two has no query at all. A wire, a
//! register, and a static `let` that only queries read have their own names
//! (`z<n>`, `N<n>`), and a module takes them only if one of its queries was
//! drawn. A program with no query text is thus the program of the other
//! tapes alone.

use super::hw::Want;
use super::inst::Child;
use super::portinfo::Kid;
use super::reflect::{self, RTy};
use super::{Builder, Built, Ctx, Lane, Module, Names};
use crate::eval::Value;
use crate::program::{
    FnTy, HBin, HExpr, Place, QExpr, Query, SBin, SExpr, STy, Scalar, Stmt, Ty, Un, sexpr, string,
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

/// What a query reads: a place and the type that the builder drew for it
/// (`@TypeOf(text)`), or a type literal (`text`).
#[derive(Clone, Debug)]
pub(super) struct Op {
    text: String,
    ty: RTy,
    place: bool,
    /// Whether a declaration took its type from this name: the outputs then
    /// mix in its `data_bits`.
    paired: bool,
}

/// One statement of a frame in this many is followed by a group, and the
/// most groups of a program.
const GROUP_ODDS: u32 = 2;
const MAX_GROUPS: u32 = 24;
/// The most groups at the end of a module body.
const TAIL: u32 = 4;
/// A module mixes a query into its outputs in this many modules.
const MIX_ODDS: u32 = 3;
/// A wire or a register takes a query as its width in this many.
const WIDTH_ODDS: u32 = 1;
/// The most steps of a place and of a type value.
const STEPS: u32 = 3;
/// The most results that one `diagnostic` shows.
const PER_RECORD: u32 = 3;
/// A group reads a child through `@ports` in this many groups, if the frame
/// has a child.
const PORTS_ODDS: u32 = 2;
/// The most text that the queries of a program add, in bytes: the largest
/// program stays below its cap.
const QUERY_BYTES: usize = 1300;
/// A group uses a generated type in this many groups, if there is one.
const STRUCT_ODDS: u32 = 2;
/// The most low bits of a query that an unsigned output takes. A signed output
/// takes `-(query & 1)`, which fits each `SInt`.
const MASK_BITS: u32 = 3;

/// The tags of the kinds: the true tag of a type and another one make a
/// test that holds and a test that fails.
const KINDS: [&str; 19] = [
    "bool", "uint", "sint", "unit", "array", "tuple", "record", "int", "nat", "string", "type",
    "function", "list", "reg", "wire", "mem", "input", "instance", "enum",
];

/// The type of a port of `child` as its parent sees it: the arguments of the
/// instance stand for the parameters of the child.
pub(super) fn outer_ty(child: &Child, t: &Ty) -> Option<RTy> {
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
}

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

pub(super) fn builtin(name: &str, arg: QExpr) -> QExpr {
    QExpr::Builtin(name.to_owned(), vec![arg])
}

pub(super) fn read(base: QExpr, suffix: &str) -> QExpr {
    QExpr::Read(Box::new(base), suffix.to_owned())
}

/// The text of the type of `op` in a type position: `@TypeOf(x)`, or the
/// element of its handle. A type position takes no `.element` after a
/// call, so the element is `@field(@typeInfo(T), "element")`.
fn type_text(op: &Op) -> QExpr {
    let of = builtin("TypeOf", QExpr::Text(op.text.clone()));
    if op.ty.handled().is_none() {
        return of;
    }
    QExpr::Builtin(
        "field".to_owned(),
        vec![builtin("typeInfo", of), QExpr::Text(string("element"))],
    )
}

pub(super) fn is(base: QExpr, text: &str) -> QExpr {
    QExpr::Eq(Box::new(base), Box::new(QExpr::Text(string(text))))
}

impl Builder {
    /// Runs `f` on the query tape, isolated from the other tapes.
    pub(super) fn on_query<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        #[cfg(test)]
        let outside = self.stats.clone();
        let out = self.isolated(Lane::Query, f);
        #[cfg(test)]
        {
            self.stats = outside.with_queries_of(&self.stats);
        }
        out
    }

    /// Makes the name `text` of the type `t` readable to the queries of the
    /// frame, if the type is one that a query reflects.
    pub(super) fn add_op(&mut self, text: &str, ty: Option<RTy>) {
        if let Some(ty) = ty {
            self.ops.push(Op {
                text: text.to_owned(),
                ty,
                place: true,
                paired: false,
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
        // The instance by its name, and through the local container that its
        // inputs go through: `l.0` selects it, and a wrong index selects
        // another instance.
        let mut places = vec![child.name.clone()];
        if let Some(route) = &child.via {
            places.push(crate::program::hexpr(&route.base));
        }
        for place in places {
            self.add_op(&place, Some(RTy::Instance));
            for (q, t) in &child.sig.outputs {
                self.add_op(&format!("{place}.{q}"), outer_ty(child, t));
            }
            for (p, t) in &child.sig.inputs {
                let ty = outer_ty(child, t).map(|t| RTy::Input(Box::new(t)));
                self.add_op(&format!("{place}.{p}"), ty);
            }
            let rows = self.kid_rows(child);
            let domain = if child.sig.clocked { "clock" } else { "" };
            self.kids.push(Kid {
                name: place,
                rows,
                domain,
            });
        }
    }

    /// The places that the static names of the frame give. A parameter, a
    /// `const`, and a static `let` have a declared type (spec 9.3). A loop
    /// binder and a binder of a `match` have none, so they stay out. A step
    /// stops at a list, which checks its length at run time, and at a
    /// string, which has no element type.
    fn static_ops(&mut self, ctx: &Ctx) -> Vec<Op> {
        let mut out = Vec::new();
        let names: Vec<(String, STy)> = ctx
            .statics
            .iter()
            .filter(|(n, _)| n.starts_with(['P', 'C', 's']))
            .cloned()
            .collect();
        for (name, ty) in names {
            self.chain(&name, &ty, STEPS, &mut out);
        }
        out
    }

    /// The place `text` of the declared type `ty`, and the places of its
    /// parts, `levels` steps deep. A tuple gives each part, and an array
    /// one.
    fn chain(&mut self, text: &str, ty: &STy, levels: u32, out: &mut Vec<Op>) {
        out.push(Op {
            text: if self.tape.below(8) == 0 {
                format!("({text})")
            } else {
                text.to_owned()
            },
            ty: RTy::from_static(ty),
            place: true,
            paired: false,
        });
        if levels == 0 {
            return;
        }
        match ty {
            STy::Tuple(ts) => {
                for (k, t) in ts.iter().enumerate() {
                    let step = self.step_key(text, &k.to_string(), false);
                    self.chain(&step, t, levels - 1, out);
                }
            }
            STy::Array(t, n) => {
                let k = self.tape.index(*n as usize);
                let step = self.step_key(text, &k.to_string(), true);
                self.chain(&step, t, levels - 1, out);
            }
            STy::Record(r) => {
                for (f, t) in &r.fields {
                    let step = self.step_name(text, f);
                    self.chain(&step, t, levels - 1, out);
                }
            }
            _ => {}
        }
    }

    /// The step `.k`, `[k]`, or `@field(base, k)` of a tuple or an array.
    fn step_key(&mut self, base: &str, k: &str, array: bool) -> String {
        match self.tape.below(3) {
            0 => format!("@field({base}, {k})"),
            _ if array => format!("{base}[{k}]"),
            _ => format!("{base}.{k}"),
        }
    }

    /// The step `.f` or `@field(base, "f")` of a record.
    fn step_name(&mut self, base: &str, f: &str) -> String {
        if self.tape.below(3) == 0 {
            format!("@field({base}, {})", string(f))
        } else {
            format!("{base}.{f}")
        }
    }

    /// The type literals, and the roots that name no binding: a function,
    /// and a type under `@TypeOf`.
    fn root_ops(&mut self) -> Vec<Op> {
        let width = self.tape.between(1, 16);
        let len = self.tape.between(1, 4);
        let literal = |text: String, ty: RTy| Op {
            text,
            ty,
            place: false,
            paired: false,
        };
        let data = RTy::UInt(int(width as usize));
        let array = STy::Array(Box::new(STy::Int), len);
        let list = STy::List(Box::new(STy::Nat));
        let mut out = vec![
            Op {
                text: format!("UInt[{width}]"),
                ty: RTy::Type,
                place: true,
                paired: false,
            },
            literal("Bool".to_owned(), RTy::Bool),
            literal(format!("UInt[{width}]"), data.clone()),
            literal(format!("SInt[{width}]"), RTy::SInt(int(width as usize))),
            literal("Nat".to_owned(), RTy::Static(STy::Nat)),
            literal("Int".to_owned(), RTy::Static(STy::Int)),
            literal("String".to_owned(), RTy::Static(STy::Str)),
            literal("Unit".to_owned(), RTy::Unit),
            literal("Type".to_owned(), RTy::Type),
            literal(array.text(), RTy::from_static(&array)),
            literal(list.text(), RTy::from_static(&list)),
            literal(
                format!("Reg[UInt[{width}]]"),
                RTy::Reg(Box::new(data.clone())),
            ),
            literal(
                format!("Wire[UInt[{width}]]"),
                RTy::Wire(Box::new(data.clone())),
            ),
            literal(
                format!("Input[UInt[{width}]]"),
                RTy::Input(Box::new(data.clone())),
            ),
            literal(
                format!("Mem[UInt[{width}], {len}]"),
                RTy::Mem(Box::new(data), len),
            ),
        ];
        for f in &self.fns {
            let params = f.params.iter().map(|(_, t)| (false, t.clone())).collect();
            let ty = STy::Fn(Box::new(FnTy {
                params,
                ret: f.ret.clone(),
            }));
            out.push(Op {
                text: f.name.clone(),
                ty: RTy::from_static(&ty),
                place: true,
                paired: false,
            });
        }
        for def in &self.enums {
            out.push(literal(
                def.name.clone(),
                RTy::Static(STy::Enum(Box::new(def.clone()))),
            ));
        }
        for g in &self.gens {
            let rec = STy::Record(Box::new(g.rec.clone()));
            out.push(Op {
                text: g.def.name.clone(),
                ty: RTy::from_static(&rec),
                place: false,
                paired: false,
            });
        }
        if let Some(record) = self.record_ty() {
            out.push(literal(record.text(), RTy::from_static(&record)));
        }
        out
    }

    /// What a query reads: a hardware name, a static name, or a type
    /// literal. The kind comes first, so that each kind of the source is as
    /// likely as another; then a name of that kind.
    fn source(&mut self, ctx: &Ctx) -> Option<Op> {
        let statics = self.static_ops(ctx);
        let roots = self.root_ops();
        // The hardware names weigh 3, the static names 3, and the literals 5.
        let pools = [(self.ops.clone(), 3), (statics, 3), (roots, 5)];
        let total: u32 = pools
            .iter()
            .filter(|(p, _)| !p.is_empty())
            .map(|(_, w)| w)
            .sum();
        let mut at = self.tape.below(total.max(1));
        let (pool, _) = pools
            .into_iter()
            .filter(|(p, _)| !p.is_empty())
            .find(|(_, w)| {
                if at < *w {
                    true
                } else {
                    at -= w;
                    false
                }
            })?;
        let kinds: BTreeSet<&str> = pool.iter().map(|op| reflect::info(&op.ty).kind).collect();
        // A kind that few sources have counts more: an instance comes with a
        // child only, and a tuple, a record, and an enum have names to read.
        let weight = |k: &str| match k {
            "instance" => 4,
            "mem" | "function" | "type" | "list" => 3,
            "tuple" | "record" | "enum" | "reg" | "wire" | "input" => 2,
            _ => 1,
        };
        let kinds: Vec<&str> = kinds
            .into_iter()
            .flat_map(|k| std::iter::repeat_n(k, weight(k)))
            .collect();
        let kind = *kinds.get(self.tape.index(kinds.len()))?;
        let of_kind: Vec<Op> = pool
            .into_iter()
            .filter(|op| reflect::info(&op.ty).kind == kind)
            .collect();
        of_kind.get(self.tape.index(of_kind.len())).cloned()
    }

    /// The type value of `op`: `@TypeOf(x)` or the literal, and then steps
    /// to the `element` or to the type of a field. With `data`, a handle
    /// gives its element and nothing else.
    fn type_value(&mut self, op: &Op, data: bool) -> (QExpr, RTy) {
        let mut tq = if op.place {
            builtin("TypeOf", QExpr::Text(op.text.clone()))
        } else {
            QExpr::Text(op.text.clone())
        };
        let mut t = op.ty.clone();
        let (element, steps) = if data {
            (t.handled().cloned(), 1)
        } else {
            (None, self.tape.below(STEPS))
        };
        if let Some(element) = element {
            return (read(builtin("typeInfo", tq), ".element"), element);
        }
        if data {
            return (tq, t);
        }
        for _ in 0..steps {
            let info = reflect::info(&t);
            let typed = builtin("typeInfo", tq.clone());
            if !info.fields.is_empty() && self.tape.below(3) != 0 {
                let i = self.tape.index(info.fields.len());
                tq = read(typed, &format!(".fields[{i}].ty"));
                t = info.fields[i].1.clone();
            } else if info.element != RTy::Unit || self.tape.flag() {
                tq = read(typed, ".element");
                t = info.element;
            }
        }
        (tq, t)
    }

    /// A numeric read of the type value `tq` of the drawn type `t`: the
    /// query and its static result. A `varying` read is a width, a number of
    /// bits, or a tag, which differ between names, not a length that is
    /// mostly 0.
    pub(super) fn size(&mut self, tq: &QExpr, t: &RTy, varying: bool) -> (QExpr, SExpr) {
        let info = reflect::info(t);
        let typed = || builtin("typeInfo", tq.clone());
        let nat = |n: usize| int(n);
        let mut reads = Vec::new();
        reads.push((read(typed(), ".width"), info.width.clone()));
        if let Some(bits) = reflect::data_bits(t) {
            reads.push((QExpr::Call("data_bits", Box::new(tq.clone())), bits));
        }
        if !info.variants.is_empty() {
            let i = self.tape.index(info.variants.len());
            let tag = SExpr::Int(
                BigInt::from(info.variants[i].1.clone()),
                crate::program::Radix::Dec,
            );
            reads.push((read(typed(), &format!(".variants[{i}].tag")), tag));
        }
        if !varying {
            reads.push((read(typed(), ".length"), info.length.clone()));
            let fields = read(typed(), ".fields");
            reads.push((QExpr::Call("len", Box::new(fields)), nat(info.fields.len())));
            let variants = read(typed(), ".variants");
            reads.push((
                QExpr::Call("len", Box::new(variants)),
                nat(info.variants.len()),
            ));
        }
        let at = self.tape.index(reads.len());
        reads.swap_remove(at)
    }

    /// A test of the type value `tq` of the drawn type `t`: the kind, or the
    /// name of a field, or the name of a variant. It holds for the true text
    /// and fails for another one.
    pub(super) fn test(&mut self, tq: QExpr, t: &RTy) -> (QExpr, SExpr) {
        let info = reflect::info(t);
        let typed = builtin("typeInfo", tq);
        let names: Vec<(String, String)> = info
            .fields
            .iter()
            .enumerate()
            .map(|(i, (n, _))| (format!(".fields[{i}].name"), n.clone()))
            .chain(
                info.variants
                    .iter()
                    .enumerate()
                    .map(|(i, (n, _))| (format!(".variants[{i}].name"), n.clone())),
            )
            .collect();
        let (suffix, truth) = if !names.is_empty() && self.tape.below(4) != 0 {
            names[self.tape.index(names.len())].clone()
        } else {
            (".kind".to_owned(), info.kind.to_owned())
        };
        let tag = if self.tape.flag() {
            truth.clone()
        } else if suffix == ".kind" {
            let others: Vec<&str> = KINDS.iter().copied().filter(|k| *k != truth).collect();
            others[self.tape.index(others.len())].to_owned()
        } else {
            format!("{truth}x")
        };
        let held = tag == truth;
        (is(read(typed, &suffix), &tag), SExpr::Bool(held))
    }

    /// A group of statements after a statement of the frame, if the query
    /// tape says so.
    pub(super) fn query_group(
        &mut self,
        ctx: &Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> Built {
        if !self.query_on {
            return Ok(());
        }
        self.on_query(|b| {
            if b.tape.below(GROUP_ODDS) == GROUP_ODDS - 1 {
                b.one_group(ctx, names, out);
            }
            Ok(())
        })
    }

    /// Up to `TAIL` groups at the end of a module body, which sees each name
    /// of the top frame.
    pub(super) fn query_tail(&mut self, ctx: &Ctx, names: &mut Names, out: &mut Vec<Stmt>) {
        if !self.query_on {
            return;
        }
        self.on_query(|b| {
            if b.tape.flag() {
                b.wide_group(ctx, out);
            }
            if b.tape.flag() {
                b.handle_group(ctx, out);
            }
            for _ in 0..b.tape.below(TAIL + 1) {
                b.one_group(ctx, names, out);
            }
        });
    }

    /// A record with a read of a handle of the top frame: an instance, a
    /// register, a wire, or a child input. A handle is rare among the
    /// sources, so a module reads one of them at its end.
    fn handle_group(&mut self, ctx: &Ctx, out: &mut Vec<Stmt>) {
        if self.queries >= MAX_GROUPS || self.query_bytes > QUERY_BYTES || ctx.envs.is_empty() {
            return;
        }
        let handles: Vec<Op> = self
            .ops
            .iter()
            .filter(|op| {
                matches!(
                    reflect::info(&op.ty).kind,
                    "instance" | "reg" | "wire" | "input"
                )
            })
            .cloned()
            .collect();
        let Some(op) = handles.get(self.tape.index(handles.len())).cloned() else {
            return;
        };
        let (tq, t) = self.type_value(&op, false);
        let (form, value) = if self.tape.flag() {
            self.test(tq, &t)
        } else {
            self.size(&tq, &t, false)
        };
        if self.values(&value, &ctx.envs).is_none() {
            return;
        }
        self.queries += 1;
        self.emitted += 1;
        note!(self, query_groups);
        #[cfg(test)]
        self.stats.query_kinds.insert(reflect::info(&t).kind);
        let query = SExpr::Query(Box::new(Query { form, value }));
        self.query_bytes += sexpr(&query).len() + 28;
        let message = self.next_message();
        out.push(Stmt::Diagnostic(message, query));
    }

    /// A record with a read of a wide result: the number of fields of a type
    /// with 3 fields or more, or of the ports of a child with 3 ports or
    /// more. The budget mode reads the cost of such a program.
    fn wide_group(&mut self, ctx: &Ctx, out: &mut Vec<Stmt>) {
        if self.queries >= MAX_GROUPS || self.query_bytes > QUERY_BYTES || ctx.envs.is_empty() {
            return;
        }
        let mut pool = self.static_ops(ctx);
        pool.extend(self.root_ops());
        let wide: Vec<Op> = pool
            .into_iter()
            .filter(|op| reflect::info(&op.ty).fields.len() >= 3)
            .collect();
        let kids: Vec<Kid> = self
            .kids
            .iter()
            .filter(|k| k.rows.len() >= 3)
            .cloned()
            .collect();
        let (form, value) = match (wide.get(self.tape.index(wide.len())), kids.first()) {
            (Some(op), _) if self.tape.flag() || kids.is_empty() => {
                let tq = if op.place {
                    builtin("TypeOf", QExpr::Text(op.text.clone()))
                } else {
                    QExpr::Text(op.text.clone())
                };
                let fields = read(builtin("typeInfo", tq), ".fields");
                (
                    QExpr::Call("len", Box::new(fields)),
                    int(reflect::info(&op.ty).fields.len()),
                )
            }
            (_, Some(kid)) => {
                let kid = kids.get(self.tape.index(kids.len())).unwrap_or(kid);
                let list = builtin("ports", QExpr::Text(kid.name.clone()));
                (QExpr::Call("len", Box::new(list)), int(kid.rows.len()))
            }
            _ => return,
        };
        if self.values(&value, &ctx.envs).is_none() {
            return;
        }
        self.queries += 1;
        self.emitted += 1;
        note!(self, query_groups);
        note!(self, query_wide);
        let query = SExpr::Query(Box::new(Query { form, value }));
        self.query_bytes += sexpr(&query).len() + 28;
        let message = self.next_message();
        out.push(Stmt::Diagnostic(message, query));
    }

    /// A wire and a register that only the queries read, and a static `let`
    /// of a container, for the start of a module body. A wire and a register
    /// have a `:=` at once, so no binding is missing. They have names of their
    /// own (`z<n>`, `N<n>`), and the module takes them only if one of its
    /// queries was drawn: a program with no query text is thus the program of
    /// the other tapes alone.
    pub(super) fn query_decls(&mut self, ctx: &Ctx, m: &mut Module) -> Built<Vec<Stmt>> {
        if !self.query_on || ctx.envs.is_empty() {
            return Ok(Vec::new());
        }
        let mut out = Vec::new();
        self.on_query(|b| {
            for _ in 0..b.tape.below(3) {
                // Half of the declarations copy the width of a name, so that
                // the width can be a query on that name.
                let widths: Vec<(SExpr, bool)> =
                    b.ops.iter().filter_map(|op| op.ty.data()).collect();
                let copy = widths.get(b.tape.index(widths.len())).cloned();
                // A type of hardware data gives a width: `data_bits(D0)`.
                let data: Vec<&str> = b
                    .gens
                    .iter()
                    .filter(|g| g.data())
                    .map(|g| g.def.name.as_str())
                    .collect();
                let bits = data
                    .get(b.tape.index(data.len()))
                    .map(|name| SExpr::DataBits((*name).to_owned(), Vec::new()));
                let ty = match (copy, bits) {
                    (_, Some(bits)) if b.tape.below(3) == 0 => Ty::UInt(bits),
                    (Some((w, true)), _) if b.tape.flag() => Ty::SInt(w),
                    (Some((w, false)), _) if b.tape.flag() => Ty::UInt(w),
                    _ => b.decl_ty(b.reach(ctx), &ctx.envs),
                };
                let types = b.types(&ty, &ctx.envs)?;
                let want = Want {
                    types,
                    ty: Some(ty.clone()),
                };
                let register = m.clocked && b.tape.flag();
                let name = format!("z{}", b.query_decls);
                b.query_decls += 1;
                let handle = RTy::of(&ty).map(|t| {
                    if register {
                        RTy::Reg(Box::new(t))
                    } else {
                        RTy::Wire(Box::new(t))
                    }
                });
                let shown = b.query_ty(ctx, ty, &want);
                if register {
                    let reset = b.fit(&want.types, b.reach(ctx), &ctx.envs);
                    out.push(Stmt::Reg(name.clone(), shown, reset));
                } else {
                    out.push(Stmt::Wire(name.clone(), shown));
                }
                let driver = b.driver_at(ctx, &want, 1);
                b.query_bytes += 40 + crate::program::hexpr(&driver).len();
                out.push(Stmt::Connect(Place::Name(name.clone()), driver));
                b.add_op(&name, handle);
            }
            if b.tape.flag() {
                let ty = b.static_container_ty();
                let value = b.container(&ty, super::stat::DEPTH, b.reach(ctx));
                if b.values(&value, &ctx.envs).is_some() {
                    let name = format!("N{}", b.query_decls);
                    b.query_decls += 1;
                    b.query_bytes += sexpr(&value).len() + 24;
                    let mut ops = Vec::new();
                    b.chain(&name, &ty, STEPS, &mut ops);
                    b.ops.extend(ops);
                    out.push(Stmt::StaticLet(name, ty, value));
                }
            }
            Ok(out)
        })
    }

    /// A static `let` of one query, and its record, if the frame can
    /// reflect something.
    fn one_group(&mut self, ctx: &Ctx, names: &mut Names, out: &mut Vec<Stmt>) {
        if self.queries >= MAX_GROUPS || self.query_bytes > QUERY_BYTES || ctx.envs.is_empty() {
            return;
        }
        if !self.gens.is_empty()
            && self.tape.below(STRUCT_ODDS) == 0
            && self.struct_group(ctx, names, out)
        {
            self.queries += 1;
            self.emitted += 1;
            return;
        }
        // A record shows up to `PER_RECORD` results, as a tuple.
        let mut results = Vec::new();
        for _ in 0..self.tape.between(1, PER_RECORD) {
            if let Some(query) = self.one_query(ctx) {
                results.push(query);
            }
        }
        let Some(first) = results.first().cloned() else {
            return;
        };
        let message = self.next_message();
        self.query_bytes += 28;
        // One record in four binds a lone result at its type first.
        if results.len() == 1 && self.tape.below(4) == 0 {
            let name = names.fresh("s");
            let ty = if matches!(first.1, SExpr::Bool(_)) {
                STy::Bool
            } else {
                STy::Nat
            };
            self.query_bytes += 24;
            out.push(Stmt::StaticLet(name.clone(), ty, first.0));
            out.push(Stmt::Diagnostic(message, SExpr::Name(name)));
        } else if results.len() == 1 {
            out.push(Stmt::Diagnostic(message, first.0));
        } else {
            let values = results.into_iter().map(|(q, _)| q).collect();
            out.push(Stmt::Diagnostic(message, SExpr::Tuple(values)));
        }
    }

    /// One query: a read of a type of a source, or of a child through
    /// `@ports`. Gives the node and its result, which holds in each env.
    fn one_query(&mut self, ctx: &Ctx) -> Option<(SExpr, SExpr)> {
        if self.queries >= MAX_GROUPS || self.query_bytes > QUERY_BYTES {
            return None;
        }
        let ports = if self.kids.is_empty() || self.tape.below(PORTS_ODDS) != 0 {
            None
        } else {
            self.ports_group()
        };
        let (form, value, t) = if let Some((form, value, t)) = ports {
            (form, value, t)
        } else {
            let op = self.source(ctx)?;
            let (tq, t) = self.type_value(&op, false);
            let (form, value) = if self.tape.flag() {
                self.test(tq, &t)
            } else {
                self.size(&tq, &t, false)
            };
            (form, value, Some(t))
        };
        self.values(&value, &ctx.envs)?;
        self.queries += 1;
        self.emitted += 1;
        note!(self, query_groups);
        #[cfg(test)]
        if let Some(t) = &t {
            self.stats.query_kinds.insert(reflect::info(t).kind);
            note!(self, query_wide, reflect::info(t).fields.len() >= 3);
        }
        #[cfg(not(test))]
        let _ = t;
        let query = SExpr::Query(Box::new(Query {
            form,
            value: value.clone(),
        }));
        self.query_bytes += sexpr(&query).len() + 4;
        Some((query, value))
    }

    /// The type `ty` of a wire or a register as a query on a name of the same
    /// type, in one declaration in `WIDTH_ODDS`: `@TypeOf(x)` for the whole
    /// type, or `data_bits(@TypeOf(x))` for the width of a finite integer.
    /// The type that the query gives is `ty` in each env of the frame. A name
    /// that a type stands for is *paired*: `mix_query` mixes its
    /// `data_bits` into an output, so that a wrong type shows in a vector
    /// and not only in a check.
    pub(super) fn query_ty(&mut self, ctx: &Ctx, ty: Ty, want: &Want) -> Ty {
        if !self.query_on || self.ops.is_empty() || want.types.len() != ctx.envs.len() {
            return ty;
        }
        self.on_query(|b| {
            if b.tape.below(WIDTH_ODDS) != 0 {
                return ty;
            }
            let same: Vec<usize> = (0..b.ops.len())
                .filter(|&i| b.ops.get(i).is_some_and(|op| b.has_type(op, want, ctx)))
                .collect();
            let Some(&at) = same.get(b.tape.index(same.len())) else {
                return ty;
            };
            let Some(op) = b.ops.get(at).cloned() else {
                return ty;
            };
            let whole = matches!(ty, Ty::Bool) || b.tape.flag();
            b.emitted += 1;
            if whole {
                note!(b, query_types);
                if let Some(paired) = b.ops.get_mut(at) {
                    paired.paired = true;
                }
                return Ty::Query(Box::new(ty), type_text(&op));
            }
            note!(b, query_widths);
            let (tq, _) = b.type_value(&op, true);
            let form = QExpr::Call("data_bits", Box::new(tq));
            match ty {
                Ty::UInt(w) => Ty::UInt(SExpr::Query(Box::new(Query { form, value: w }))),
                Ty::SInt(w) => Ty::SInt(SExpr::Query(Box::new(Query { form, value: w }))),
                other => other,
            }
        })
    }

    /// Whether the type of `op`, or of the element of its handle, is the
    /// wanted type in each env.
    fn has_type(&self, op: &Op, want: &Want, ctx: &Ctx) -> bool {
        let Some(t) = op.ty.data_ty() else {
            return false;
        };
        let (width, signed) = match t {
            RTy::Bool => {
                return want.types.iter().all(|w| *w == Scalar::Bool);
            }
            RTy::UInt(w) => (w, false),
            RTy::SInt(w) => (w, true),
            _ => return false,
        };
        self.values(width, &ctx.envs).is_some_and(|vs| {
            vs.iter().zip(&want.types).all(|(v, w)| match (v, w) {
                (Value::Int(n), Scalar::UInt(w)) => !signed && *n == BigInt::from(*w),
                (Value::Int(n), Scalar::SInt(w)) => signed && *n == BigInt::from(*w),
                _ => false,
            })
        })
    }

    /// The outputs with the low bits of a query mixed into one of them, in
    /// one module in `MIX_ODDS`: `old ^ T(query & mask)`, or
    /// `old != ((query & 1) == 1)` for a `Bool`. The twin writes the result
    /// of the query, so its outputs differ from the program if the generator
    /// and a front end disagree on a type that the output reads. A name that
    /// a type position paired in the body of the module gets its `data_bits`
    /// mixed in first. A pair of a nested frame ends with the frame, so no
    /// mix reads it.
    pub(super) fn mix_query(&mut self, ctx: &Ctx, outputs: &mut [(String, Want, HExpr)]) {
        if !self.query_on || outputs.is_empty() {
            return;
        }
        self.on_query(|b| {
            let paired: Vec<Op> = b.ops.iter().filter(|op| op.paired).cloned().collect();
            // A paired name always mixes, and mixes its `data_bits`: the type
            // position is the reason.
            if paired.is_empty() && (b.query_bytes > QUERY_BYTES || b.tape.below(MIX_ODDS) != 0) {
                return;
            }
            let at = b.tape.index(outputs.len());
            let (form, value) = if let Some(op) = paired.get(b.tape.index(paired.len())) {
                let (tq, t) = b.type_value(op, true);
                let Some(bits) = reflect::data_bits(&t) else {
                    return;
                };
                (QExpr::Call("data_bits", Box::new(tq)), bits)
            } else {
                let kid = b.kids.get(b.tape.index(b.kids.len())).cloned();
                let ports = match kid {
                    Some(kid) if b.tape.below(3) == 0 => b.ports_read(&kid, true),
                    _ => None,
                };
                if let Some(read) = ports {
                    read
                } else {
                    let Some(op) = b.source(ctx) else {
                        return;
                    };
                    let (tq, t) = b.type_value(&op, false);
                    b.size(&tq, &t, true)
                }
            };
            let Some((_, want, driver)) = outputs.get_mut(at) else {
                return;
            };
            let Some(ty) = want.printable() else { return };
            let widths: Vec<u32> = want
                .types
                .iter()
                .map(|t| match t {
                    Scalar::Bool => 1,
                    Scalar::UInt(w) | Scalar::SInt(w) => *w,
                })
                .collect();
            let signed = matches!(ty.resolved(), Ty::SInt(_));
            let bits = if signed {
                1
            } else {
                widths.iter().copied().min().unwrap_or(1).min(MASK_BITS)
            };
            let number = SExpr::Query(Box::new(Query { form, value }));
            b.query_bytes += sexpr(&number).len() + 24;
            let mask = int((1usize << bits) - 1);
            let low = SExpr::Binary(SBin::And, Box::new(number), Box::new(mask));
            let (op, mixed) = match ty.resolved() {
                Ty::Bool => {
                    let one = SExpr::Binary(SBin::Eq, Box::new(low), Box::new(int(1)));
                    (HBin::Ne, HExpr::Static(one))
                }
                Ty::UInt(_) => (HBin::Xor, HExpr::Make(ty, low)),
                Ty::SInt(_) => {
                    let negative = SExpr::Unary(Un::Neg, Box::new(low));
                    (HBin::Xor, HExpr::Make(ty, negative))
                }
                Ty::Enum(_) | Ty::Rec(_) | Ty::Query(..) => return,
            };
            let old = std::mem::replace(driver, HExpr::Unit);
            *driver = HExpr::Binary(op, Box::new(old), Box::new(mixed));
            note!(b, query_mixes);
            note!(b, query_pairs, !paired.is_empty());
            b.emitted += 1;
        });
    }
}

#[cfg(test)]
mod tests {
    use super::super::Stats;
    use super::super::tests::tapes;
    use super::*;
    use std::collections::BTreeMap;

    /// The roots of the operands of the `@TypeOf` queries in `text`.
    fn roots(text: &str) -> Vec<&'static str> {
        let mut out = Vec::new();
        for part in text.split("@TypeOf(").skip(1) {
            let mut at = part;
            while let Some(rest) = at.strip_prefix('(').or_else(|| at.strip_prefix("@field(")) {
                at = rest;
            }
            let name: String = at.chars().take_while(char::is_ascii_alphanumeric).collect();
            out.push(match at.bytes().next().unwrap_or(b' ') {
                b'z' if text.contains(&format!("reg {name}:")) => "reg",
                b'z' | b'w' => "wire",
                b'N' | b's' => "static let",
                b'i' => "input",
                b'r' => "reg",
                b'P' => "param",
                b'C' => "const",
                b'f' => "function",
                b'U' => "type",
                b'u' => match at.split_once('.').and_then(|(_, r)| r.bytes().next()) {
                    Some(b'i') => "child input",
                    Some(_) => "child output",
                    None => "instance",
                },
                _ => "other",
            });
        }
        out
    }

    /// The forms of the queries in a program.
    fn forms(text: &str, s: &Stats) -> Vec<(String, bool)> {
        let literal = [
            "@typeInfo(Nat)",
            "@typeInfo(Int)",
            "@typeInfo(String)",
            "@typeInfo(Unit)",
            "@typeInfo(Type)",
            "@typeInfo(Bool)",
            "@typeInfo(UInt[",
            "@typeInfo(SInt[",
            "@typeInfo([",
            "@typeInfo(List[",
            "@typeInfo(Reg[",
            "@typeInfo(Wire[",
            "@typeInfo(Input[",
            "@typeInfo(Mem[",
        ];
        let mut forms = vec![
            ("group".to_owned(), s.query_groups > 0),
            ("width".to_owned(), s.query_widths > 0),
            ("mix".to_owned(), s.query_mixes > 0),
            ("type position".to_owned(), s.query_types > 0),
            ("paired output".to_owned(), s.query_pairs > 0),
            ("kind test".to_owned(), text.contains(".kind == ")),
            ("element".to_owned(), text.contains(".element")),
            (
                "field or variant".to_owned(),
                text.contains(".name == ") || text.contains(".ty)") || text.contains(".variants["),
            ),
            (
                "type literal".to_owned(),
                literal.iter().any(|l| text.contains(l)),
            ),
        ];
        let found = roots(text);
        for root in [
            "input",
            "reg",
            "wire",
            "param",
            "const",
            "static let",
            "function",
            "type",
            "child input",
            "child output",
        ] {
            forms.push((format!("root {root}"), found.contains(&root)));
        }
        for kind in KINDS {
            forms.push((format!("kind {kind}"), s.query_kinds.contains(kind)));
        }
        forms.push(("ports".to_owned(), text.contains("@ports(")));
        forms.push(("wide result".to_owned(), s.query_wide > 0));
        forms.push((
            "ports container".to_owned(),
            text.contains("@TypeOf(l") || text.contains("@ports(l"),
        ));
        forms.push(("wrapper".to_owned(), text.contains("module W0(")));
        forms.push((
            "wrapper used".to_owned(),
            text.contains("module W0(") && text.contains(" = W0("),
        ));
        for (name, seen) in [
            ("length", text.contains("len(@ports(")),
            ("direction", text.contains(".is_input")),
            ("key index", text.contains(".key.index")),
            ("key indexed", text.contains(".key.indexed")),
            ("key name", text.contains(".key.name == ")),
            ("domain", text.contains(".domain")),
            ("type", text.contains("\"ty\")") || text.contains("].ty)")),
        ] {
            forms.push((format!("ports {name}"), seen));
        }
        let aliases = text.contains("\ntype D");
        forms.push(("generated type".to_owned(), aliases));
        forms.push(("struct group".to_owned(), s.struct_groups > 0));
        for (name, seen) in [
            ("spelling literal", text.contains("= @Struct([FieldInfo(")),
            ("spelling empty", text.contains("= @Struct([]);")),
            ("spelling push", text.contains("    push(fs, FieldInfo(")),
            ("spelling struct", text.contains("= @Struct(@typeInfo(S")),
            (
                "spelling round trip",
                text.contains("= @Struct(@typeInfo(D"),
            ),
            (
                "identity test",
                text.contains(".fields) == D") || text.contains(".fields) == S"),
            ),
            (
                "alias test",
                text.contains("(D0 == D") || text.contains("(D1 == D"),
            ),
            ("width of a generated type", text.contains("[data_bits(D")),
        ] {
            forms.push((format!("generated {name}"), seen));
        }
        forms
    }

    /// Each form of the queries occurs in at least 10% of 256 programs, and
    /// each root and each kind in 1 program in 32.
    #[test]
    fn programs_cover_the_queries() {
        const TAPES: usize = 256;
        let mut with = BTreeMap::<String, usize>::new();
        let mut any = 0;
        for tape in tapes(TAPES) {
            let mut b = Builder::new(tape);
            let p = b.program();
            assert!(p.is_ok(), "a program faults: {p:?}");
            let Ok(p) = p else { continue };
            assert!(b.queries <= MAX_GROUPS, "{} groups", b.queries);
            let text = p.text();
            any += usize::from(text.contains("@TypeOf") || text.contains("@typeInfo"));
            for (form, seen) in forms(&text, &b.stats) {
                *with.entry(form).or_default() += usize::from(seen);
            }
        }
        assert!(
            any * 10 >= TAPES * 3 && any * 10 <= TAPES * 7,
            "{any} programs"
        );
        for (form, n) in &with {
            let detail = ["root ", "kind ", "generated ", "ports ", "wrapper"];
            // The budget mode reads the cost of a program with a wide result:
            // a type with 3 fields or more, or a child with 3 ports or more.
            let floor = if form == "wide result" {
                TAPES * 3 / 10
            } else if detail.iter().any(|d| form.starts_with(d)) {
                TAPES / 32
            } else {
                TAPES / 10
            };
            assert!(*n >= floor, "{form} occurs in {n} of {TAPES}: {with:?}");
        }
    }
}
