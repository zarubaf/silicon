// SPDX-License-Identifier: Apache-2.0
//! The records of `diagnostic` (Lean `Source.Eval.diagnose`, sections 5.4, 6.2, and 8.2). A
//! call runs in this order, and each error is at the call:
//!
//! 1. The node, the callee name, and the copies of the arguments charge first. The caller
//!    paid them.
//! 2. An enclosing guard has an effect that it cannot take (`S016`).
//! 3. The message takes a data context: a register, a wire, and an output are hardware
//!    (`S011`), a child input is `S017`, a memory, an instance, and a domain are `S010`. Then
//!    a hardware value is `S011`, and a static value other than a `String` is `S010`.
//! 4. A value that waits for its type is `S010`.
//! 5. The measure charge of the value, then the length of the record in bytes. The text of
//!    the record does not exist before the second charge.
//! 6. The record goes into the list. The result is `()`.
//!
//! The text is pure: one walk with its own stack writes it, into a counter of bytes for the
//! charge and into a string after it. It never calls the charging `normalize`: a reference
//! renders from the metadata of its type, and a part without a hardware leaf is its static
//! zero.

use super::{Evaluator, Opnd, Out, Res, at, fail};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Handle, Kind, Seen};
use crate::limit;
use crate::names::{Name, PathId, write_encoded};
use crate::serial::{self, Item, Len, Sink};
use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use parse::ast::Pos;
use resolve::DeclId;

/// A piece of the text that waits on the stack of the walk, in the order it is written.
enum Piece<'a> {
    Text(&'static str),
    Owned(String),
    /// The head `(record <line> <col> <emitted> (`, written from the borrowed name.
    Head(Pos, &'a str),
    /// An instance `(instance <module> `, written from the borrowed module name.
    Instance(Option<&'a Name>),
    /// The name of a path, encoded into the sink.
    Path(PathId),
    /// A port name and the closing bracket, ` <name>)`.
    Port(&'a str),
    /// A frame `(call <name> <line> <col>)`, written from the borrowed name.
    Frame(&'a str, Pos),
    /// A domain `(domain <name>)`, written from the shared name.
    Domain(&'a str),
    Quoted(&'a str),
    Value(&'a Value),
    Type(TyId),
    Node(&'a Ty),
    Agg(&'a Agg),
    /// The part of a reference of the type: the value that it stands for.
    Part(TyId),
    /// The remaining copies of the element type of a reference array, each after a space.
    Rest(TyId, u64),
    Handle(&'a Handle),
    Hw(crate::hw::HwId),
}

impl Evaluator<'_> {
    /// The emitted name of the current instantiation, else `-`. An index that `emitted` does not
    /// hold is a bug of the evaluator, never an input of the user.
    fn emitted_name(&self) -> &str {
        let Some(i) = self.inst else {
            return "-";
        };
        let Some(name) = self.emitted.get(i) else {
            panic!("the emitted name {i} is not in the table of emitted names");
        };
        name
    }

    /// The text of the name of the domain `id`. A handle makes the text before it exists, so a
    /// missing text is a bug of the evaluator, never an input of the user.
    fn domain_name(&self, id: DeclId) -> &str {
        let Some(name) = self.domains.get(&id) else {
            panic!("the domain handle has no name in the table of domains");
        };
        name
    }
}

impl Piece<'_> {
    /// Whether the piece writes a scalar form and expands to no other piece.
    #[cfg(test)]
    fn is_leaf(&self) -> bool {
        matches!(
            self,
            Piece::Value(_) | Piece::Type(_) | Piece::Node(_) | Piece::Hw(_)
        )
    }
}

/// Pushes `pieces` so that they come off the stack in their order.
fn push_all<'a>(work: &mut Vec<Piece<'a>>, pieces: Vec<Piece<'a>>) {
    work.extend(pieces.into_iter().rev());
}

/// The pieces of the items `items` with a space between.
fn spaced<'a>(items: impl Iterator<Item = Piece<'a>>) -> Vec<Piece<'a>> {
    let mut pieces = Vec::new();
    for (k, item) in items.enumerate() {
        if k > 0 {
            pieces.push(Piece::Text(" "));
        }
        pieces.push(item);
    }
    pieces
}

/// The measure charge of the rendering of a reference of the type `t` (section 5.4): 1 for
/// each container part with a hardware leaf. A part without one renders as its static zero,
/// which the copy of the reference paid for. An array multiplies the charge of its element, so
/// the walk reads each type once.
fn part_charge(tys: &Types, t: TyId) -> u128 {
    let mut total = 0u128;
    let mut work = vec![(t, 1u128)];
    while let Some((t, times)) = work.pop() {
        if tys.meta(t).leaves.is_zero() {
            continue;
        }
        match tys.get(t) {
            Ty::Array(elem, n) => {
                total = total.saturating_add(times);
                let n = u128::from(n.to_u64().unwrap_or(u64::MAX));
                work.push((*elem, times.saturating_mul(n)));
            }
            Ty::Tuple(parts) => {
                total = total.saturating_add(times);
                work.extend(parts.iter().map(|p| (*p, times)));
            }
            Ty::Struct(_) => {
                total = total.saturating_add(times);
                if let Some(parts) = tys.parts(t) {
                    work.extend(parts.types.iter().map(|f| (*f, times)));
                }
            }
            _ => {}
        }
    }
    total
}

impl Evaluator<'_> {
    /// The call at `pos` of `diagnostic` named `g`, with the arguments `vs` in the order of
    /// the parameters. The caller charged the node, the name, and the copies.
    pub(super) fn diagnose(&mut self, pos: Pos, g: &str, mut vs: Vec<Out>) -> Res<Option<Out>> {
        if let Some(guard) = self.guard {
            return fail(Code::S016, pos, guard.effect(g));
        }
        let (Some(value), Some(message)) = (vs.pop(), vs.pop()) else {
            return fail(Code::S010, pos, format!("`{g}` needs two arguments"));
        };
        let message = self.message(pos, g, message)?;
        if matches!(self.store.seen(&value), Seen::Pending(..)) {
            return fail(
                Code::S010,
                pos,
                format!(
                    "the value of `{g}` needs a type; {}",
                    self.text(self.store.seen(&value))
                ),
            );
        }
        limit::record(self.seen_size(self.store.seen(&value))).map_err(at(pos))?;
        let measure = self.measure_charge(self.store.seen(&value));
        self.charge(pos, measure)?;
        let mut len = Len::with(std::mem::take(&mut self.lens));
        self.line(pos, &message, self.store.seen(&value), &mut len);
        self.lens = len.1;
        self.charge(pos, u128::from(len.0))?;
        let mut text = String::with_capacity(usize::try_from(len.0).unwrap_or(0));
        self.line(pos, &message, self.store.seen(&value), &mut text);
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Recorded, 1);
        self.records.push(text);
        Ok(Some(Out::Made(crate::hw::Val::Static(Value::Unit))))
    }

    /// The message of `diagnostic` at the call `pos`, in the data context (section 9.2).
    fn message(&mut self, pos: Pos, g: &str, m: Out) -> Res<String> {
        match self.store.seen(&m) {
            Seen::Pending(..) => {
                return fail(
                    Code::S010,
                    pos,
                    format!("the message of `{g}` is a String, not `[]` without a type"),
                );
            }
            // A resource is hardware even if its type is empty, so no read comes first.
            s @ Seen::Handle(Handle::Res { .. }) => {
                return fail(
                    Code::S011,
                    pos,
                    format!(
                        "the message of `{g}` is a static String, not {}",
                        self.text(s)
                    ),
                );
            }
            _ => {}
        }
        match self.data(pos, m)? {
            Opnd::Static(o) => match self.store.seen(&o) {
                Seen::Static(Value::Str(s)) => Ok(s.clone()),
                Seen::Static(v) => fail(
                    Code::S010,
                    pos,
                    format!(
                        "the message of `{g}` is a String, not {}",
                        v.text(&self.tys)
                    ),
                ),
                s => fail(
                    Code::S011,
                    pos,
                    format!(
                        "the message of `{g}` is a static String, not {}",
                        self.text(s)
                    ),
                ),
            },
            Opnd::Hw(h) => fail(
                Code::S011,
                pos,
                format!(
                    "the message of `{g}` is a static String, not hardware {}",
                    self.tys.text_of(&self.graph.ty(h))
                ),
            ),
        }
    }

    /// The measure charge of the value in a record (section 5.4): `Value::measure_charge` of
    /// a static part, and 1 for each rendered container with a hardware leaf. A hardware leaf
    /// and a handle have no container.
    fn measure_charge(&self, root: Seen<'_>) -> u128 {
        let mut total = 0u128;
        let mut work = vec![root];
        while let Some(seen) = work.pop() {
            total = total.saturating_add(match seen {
                Seen::Static(v) | Seen::Agg(Agg::Static(v)) => v.measure_charge(),
                Seen::Agg(Agg::Ref(_, t)) => part_charge(&self.tys, *t),
                Seen::Agg(Agg::Array(_, ps) | Agg::Tuple(_, ps) | Agg::Record(_, ps)) => {
                    work.extend(ps.0.iter().map(Agg::seen));
                    1
                }
                _ => 0,
            });
        }
        total
    }

    /// The record line `(record <line> <col> <emitted> (<frames>) <message> <value>)` into
    /// `out`. The walk is pure and keeps its own stack.
    fn line<S: Sink>(&self, pos: Pos, message: &str, root: Seen<'_>, out: &mut S) {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Framed, self.calls.len() as u64);
        let frames = spaced(self.calls.iter().map(|&(i, q)| {
            let name = self.file.ast().get(i).map_or("", |item| &item.name().name);
            Piece::Frame(name, q)
        }));
        let mut work = Vec::new();
        let value = match root {
            Seen::Static(v) => Piece::Value(v),
            Seen::Agg(a) => Piece::Agg(a),
            Seen::Handle(h) => Piece::Handle(h),
            Seen::Hw(h) => Piece::Hw(h),
            Seen::Pending(..) => Piece::Text("-"),
        };
        let mut pieces = vec![Piece::Head(pos, self.emitted_name())];
        pieces.extend(frames);
        pieces.extend([
            Piece::Text(") (string "),
            Piece::Quoted(message),
            Piece::Text(") "),
            value,
            Piece::Text(")"),
        ]);
        push_all(&mut work, pieces);
        while let Some(piece) = work.pop() {
            #[cfg(test)]
            {
                crate::counters::add(crate::counters::Count::Rendered, 1);
                if piece.is_leaf() {
                    crate::counters::add(crate::counters::Count::RenderedLeaves, 1);
                }
            }
            match piece {
                Piece::Text(s) => out.write_str(s).unwrap_or_default(),
                Piece::Owned(s) => out.write_str(&s).unwrap_or_default(),
                Piece::Head(pos, inst) => {
                    write!(out, "(record {} {} {inst} (", pos.line, pos.col).unwrap_or_default();
                }
                Piece::Frame(name, q) => {
                    write!(out, "(call {name} {} {})", q.line, q.col).unwrap_or_default();
                }
                Piece::Instance(module) => {
                    out.write_str("(instance ").unwrap_or_default();
                    if let Some(m) = module {
                        write_encoded(m, out).unwrap_or_default();
                    }
                    out.write_str(" ").unwrap_or_default();
                }
                Piece::Path(p) => self
                    .paths
                    .write_name(p, &self.syms.texts, out)
                    .unwrap_or_default(),
                Piece::Port(n) => write!(out, " {n})").unwrap_or_default(),
                Piece::Domain(d) => write!(out, "(domain {d})").unwrap_or_default(),
                Piece::Quoted(s) => out.quoted(s),
                Piece::Value(v) => serial::write(&self.tys, Item::Value(v), out),
                Piece::Type(t) => serial::write(&self.tys, Item::Ty(t), out),
                Piece::Node(t) => serial::write(&self.tys, Item::Node(t), out),
                Piece::Agg(a) => self.agg_pieces(a, &mut work),
                Piece::Part(t) => self.part_pieces(t, &mut work, out),
                Piece::Rest(t, k) => {
                    if k > 0 {
                        work.push(Piece::Rest(t, k - 1));
                        work.push(Piece::Part(t));
                        work.push(Piece::Text(" "));
                    }
                }
                Piece::Handle(h) => self.handle_pieces(h, &mut work),
                Piece::Hw(h) => self.hw_pieces(h, &mut work),
            }
        }
    }

    /// The pieces of `(hw <type>)` of the hardware value `h`.
    fn hw_pieces<'a>(&'a self, h: crate::hw::HwId, work: &mut Vec<Piece<'a>>) {
        let mut pieces = vec![Piece::Text("(hw ")];
        if let Some(node) = self.graph.node(h) {
            pieces.push(Piece::Node(&node.ty));
        }
        pieces.push(Piece::Text(")"));
        push_all(work, pieces);
    }

    /// The pieces of a part of an aggregate: a static part, a hardware leaf, a reference, or a
    /// container with its parts.
    fn agg_pieces<'a>(&self, a: &'a Agg, work: &mut Vec<Piece<'a>>) {
        match a {
            Agg::Static(v) => work.push(Piece::Value(v)),
            Agg::Hw(h) => work.push(Piece::Hw(*h)),
            Agg::Ref(_, t) => work.push(Piece::Part(*t)),
            Agg::Array(n, ps) => {
                let elem = match self.tys.get(n.ty) {
                    Ty::Array(elem, _) => *elem,
                    _ => n.ty,
                };
                let mut pieces = vec![Piece::Text("(array "), Piece::Type(elem), Piece::Text(" (")];
                pieces.extend(spaced(ps.0.iter().map(Piece::Agg)));
                pieces.push(Piece::Text("))"));
                push_all(work, pieces);
            }
            Agg::Tuple(_, ps) => {
                let mut pieces = vec![Piece::Text("(tuple (")];
                pieces.extend(spaced(ps.0.iter().map(Piece::Agg)));
                pieces.push(Piece::Text("))"));
                push_all(work, pieces);
            }
            Agg::Record(n, ps) => {
                let mut pieces = vec![
                    Piece::Text("(record "),
                    Piece::Type(n.ty),
                    Piece::Text(" ("),
                ];
                pieces.extend(spaced(ps.0.iter().map(Piece::Agg)));
                pieces.push(Piece::Text("))"));
                push_all(work, pieces);
            }
        }
    }

    /// The value that a part of the type `t` of a reference stands for. A part without a
    /// hardware leaf is its static zero, a part of a scalar type is a hardware leaf, and
    /// another part is its container form with each part rendered. The metadata and the done
    /// entries of the structs give it, so it reads no base and charges nothing.
    fn part_pieces<'a, S: Sink>(&'a self, t: TyId, work: &mut Vec<Piece<'a>>, out: &mut S) {
        if self.tys.meta(t).leaves.is_zero() {
            match self.tys.zero(t) {
                Some(zero) => serial::write(&self.tys, Item::Value(&zero), out),
                None => out.write_str("-").unwrap_or_default(),
            }
            return;
        }
        match self.tys.get(t) {
            Ty::Array(elem, n) => {
                let n = n.to_u64().unwrap_or(u64::MAX);
                work.push(Piece::Text("))"));
                work.push(Piece::Rest(*elem, n.saturating_sub(1)));
                work.push(Piece::Part(*elem));
                push_all(
                    work,
                    vec![
                        Piece::Text("(array "),
                        Piece::Type(*elem),
                        Piece::Text(" ("),
                    ],
                );
            }
            Ty::Tuple(parts) => {
                let mut pieces = vec![Piece::Text("(tuple (")];
                pieces.extend(spaced(parts.iter().map(|p| Piece::Part(*p))));
                pieces.push(Piece::Text("))"));
                push_all(work, pieces);
            }
            Ty::Struct(_) => {
                let mut pieces = vec![Piece::Text("(record "), Piece::Type(t), Piece::Text(" (")];
                if let Some(parts) = self.tys.parts(t) {
                    pieces.extend(spaced(parts.types.iter().map(|f| Piece::Part(*f))));
                }
                pieces.push(Piece::Text("))"));
                push_all(work, pieces);
            }
            ty => push_all(
                work,
                vec![Piece::Text("(hw "), Piece::Node(ty), Piece::Text(")")],
            ),
        }
    }

    /// The pieces of a handle by its kind (section 8.2): a resource and a memory name their
    /// type and their core name, an instance its emitted module name and its core name, a
    /// child input the core name of its instance and its port name, and a domain itself.
    fn handle_pieces<'a>(&'a self, h: &'a Handle, work: &mut Vec<Piece<'a>>) {
        let name = Piece::Path;
        let pieces = match h {
            Handle::Res { kind, ty, path, .. } => {
                let kind = match kind {
                    Kind::Reg => "(reg ",
                    Kind::Wire => "(wire ",
                    Kind::Output => "(output ",
                };
                vec![
                    Piece::Text(kind),
                    Piece::Node(ty),
                    Piece::Text(" "),
                    name(*path),
                    Piece::Text(")"),
                ]
            }
            Handle::Mem(id) => match self.mem(*id) {
                Some(m) => vec![
                    Piece::Text("(mem (array "),
                    Piece::Type(m.word),
                    Piece::Owned(format!(" {}) ", m.depth)),
                    name(m.path),
                    Piece::Text(")"),
                ],
                None => vec![Piece::Text("-")],
            },
            Handle::Inst { path, inst, .. } => {
                let module = self.elab.interface(*inst).map(|i| &i.name);
                vec![Piece::Instance(module), name(*path), Piece::Text(")")]
            }
            Handle::Input { path, port, .. } => {
                let port_name = self.syms.texts.get(port.sym).map_or("", String::as_str);
                vec![
                    Piece::Text("(input "),
                    Piece::Node(&port.ty),
                    Piece::Text(" "),
                    name(*path),
                    Piece::Port(port_name),
                ]
            }
            Handle::Domain(d) => vec![Piece::Domain(self.domain_name(*d))],
        };
        push_all(work, pieces);
    }
}
