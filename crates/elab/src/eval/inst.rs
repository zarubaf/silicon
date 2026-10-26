// SPDX-License-Identifier: Apache-2.0
//! The instantiations of slice 1 and the checks for each instantiation, as Lean
//! `Source.Elab` defines them (sections 5.3, 6.1, and 6.2 of the front-end spec). `elaborate`
//! runs the top selection and each instantiation that it reaches, in the evaluation order.
//! Each instantiation gives a hardware description: its ports, registers, wires, named
//! bindings, child instances, and `:=` bindings.
//!
//! The table of instantiations is normative. An `instance` statement works in these steps:
//!
//! 1. It evaluates the arguments from left to right. Each argument is static (`S011`).
//! 2. The typed use of the arguments nests one level (`S015`), in the scope of the module with
//!    a new frame. Each parameter type evaluates in order, with each earlier parameter bound
//!    to its converted argument. An error in it is at its own node. A literal with `[]` takes
//!    this type. The argument converts to it: `S010` or `S012` at the statement. Then the
//!    recursive size of the converted arguments charges, also for a done instantiation.
//! 3. A clocked child in a combinational module is `S017` at the statement.
//! 4. The serialization charges the square of the size of each integer, and its length in
//!    bytes. An instantiation in progress is `S019` at the statement. A done one gives its
//!    interface.
//! 5. A new one nests one level deeper (`S015`). Its emitted name charges its length in
//!    bytes, and it must be new (`S019`). Then it goes in progress, runs its body, checks its
//!    bindings, and is done.
//!
//! The `InstantiationId` holds the converted arguments, so `C(1)` and `C(UInt[8](1))` give one
//! instantiation when the parameter of `C` has the type `UInt[8]`. The parameters of a new
//! instantiation bind to the converted arguments with their types. The types do not evaluate
//! again, and the child charges nothing for them.
//!
//! The units of an instantiation are its charges from the start of its body to the end of its
//! binding check, without the units of its new children. The charges of an `instance`
//! statement, with the typed use of its arguments, belong to the parent. The arguments of the
//! top selection and their typed use belong to no instantiation.
//!
//! The child module `design` holds the description of an instantiation and the `Design`. The
//! child module `work` holds the work state of the current instantiation behind methods. The
//! child module `bind` holds the texts of `S018`. The child module `stmt` runs the statements of
//! a module body.

use super::{Evaluator, Out, ROOT, Res, Slot, fail};
use crate::hw::{Port, PortId, Val};
use crate::int::Int;
pub(super) use crate::names::entry_text;
use crate::names::{encode, module_name};
use crate::scan::Scan;
use crate::types::TyId;
use crate::value::{InstantiationId, Value, int_size};
use crate::{Budget, Code};
use parse::ast::{Expr, Item, Pos, UnOp};
use resolve::Resolved;
use std::collections::{BTreeMap, BTreeSet};

mod bind;
mod design;
mod family;
mod public;
mod stmt;
mod work;
pub use design::Design;
pub(crate) use design::{Bind, Inst, Mem, Sink};
use design::{Iface, PortDecl};
pub(super) use family::{child_key, family_value, no_port};
use work::Work;

/// The state of an `InstantiationId` in the table of instantiations.
enum Status {
    InProgress,
    Done(usize),
}

/// The state of the instantiations of an elaboration. `table` maps the serialization of each
/// `InstantiationId` to its state, and `names` holds the emitted name of each instantiation
/// that is in progress or done. `digest` makes the digest of an emitted name, so a test can
/// replace it.
pub(crate) struct Elab {
    digest: fn(&str) -> String,
    table: BTreeMap<String, Status>,
    names: BTreeSet<String>,
    done: Vec<Inst>,
    work: Work,
}

impl Elab {
    pub(crate) fn new(digest: fn(&str) -> String) -> Elab {
        Elab {
            digest,
            table: BTreeMap::new(),
            names: BTreeSet::new(),
            done: Vec::new(),
            work: Work::new(None, usize::MAX),
        }
    }

    /// The interface of the done instantiation `inst`.
    pub(crate) fn interface(&self, inst: usize) -> Option<&Iface> {
        self.done.get(inst).map(|i| &i.iface)
    }

    /// The ports of the done instantiation `inst` in the order of the port layout. A handle
    /// holds a done instantiation, so the empty answer for another number is never seen.
    pub(crate) fn schema(&self, inst: usize) -> &[Port] {
        self.interface(inst).map_or(&[], |i| &i.schema)
    }

    /// The port `sym` of the done instantiation `inst`.
    pub(crate) fn port(&self, inst: usize, id: PortId) -> Option<Port> {
        self.done
            .get(inst)
            .and_then(|i| i.iface.ports.get(&id))
            .cloned()
    }
}

/// A literal argument of a top selection: a number, a negative number, a Boolean, or a
/// string. A negative number has the position of its `-` and of its number.
pub(crate) enum Literal {
    Num(Pos, Int),
    Neg(Pos, Pos, Int),
    Bool(Pos, bool),
    Str(Pos, String),
}

impl Literal {
    /// The literal of an expression of the top selection, with its value.
    pub(crate) fn of(e: &Expr) -> Option<Literal> {
        let num = |v: &parse::ast::Nat| Int::from_decimal(v.as_str());
        match e {
            Expr::Num { pos, value, .. } => Some(Literal::Num(*pos, num(value)?)),
            Expr::Bool { pos, value } => Some(Literal::Bool(*pos, *value)),
            Expr::Str { pos, value } => Some(Literal::Str(*pos, value.clone())),
            Expr::Unary {
                pos,
                op: UnOp::Neg,
                arg,
            } => match &**arg {
                Expr::Num { pos: q, value, .. } => Some(Literal::Neg(*pos, *q, num(value)?)),
                _ => None,
            },
            _ => None,
        }
    }
}

/// The elaboration of the top selection at `pos`: the module item `top` with the literal
/// arguments `xs`. The arguments get their typed use and charge as those of an `instance`
/// statement.
pub(crate) fn elaborate(
    file: &Resolved,
    budget: Budget,
    scan: Scan,
    digest: fn(&str) -> String,
    pos: Pos,
    top: usize,
    xs: Vec<Literal>,
) -> (Vec<String>, Res<Design>) {
    let mut ev = Evaluator::new(file, None, budget, scan, Elab::new(digest));
    let outcome = ev.top_selection(pos, top, xs);
    let design = outcome.map(|top| Design {
        insts: std::mem::take(&mut ev.elab.done),
        top,
        pos,
        used: budget.fuel - ev.fuel.left(),
        left: ev.fuel.left(),
        graph: std::mem::take(&mut ev.graph),
        paths: std::mem::take(&mut ev.paths),
        tys: std::mem::take(&mut ev.tys),
        field_order: std::mem::take(&mut ev.syms.field_order),
        texts: std::mem::take(&mut ev.syms.texts),
    });
    (std::mem::take(&mut ev.records), design)
}

impl Evaluator<'_> {
    /// The instantiation of the top selection at `pos`: the module item `top` with the literal
    /// arguments `xs`. The result is the index of its done instantiation.
    fn top_selection(&mut self, pos: Pos, top: usize, xs: Vec<Literal>) -> Res<usize> {
        let mut outs = Vec::with_capacity(xs.len());
        for x in xs {
            outs.push(Out::Made(Val::Static(self.literal(x)?)));
        }
        let args = self.typed_arguments(pos, top, outs)?;
        self.instantiate(pos, top, args)
    }

    /// A literal of the top selection, as `eval` charges it.
    fn literal(&mut self, x: Literal) -> Res<Value> {
        Ok(match x {
            Literal::Num(p, n) => {
                self.charge(p, 1)?;
                self.charge(p, u128::from(int_size(&n)))?;
                Value::Int(n)
            }
            Literal::Neg(p, q, n) => {
                self.charge(p, 1)?;
                self.charge(q, 1)?;
                let size = u128::from(int_size(&n));
                self.charge(q, size)?;
                self.charge(p, size)?;
                Value::Int(n.neg())
            }
            Literal::Bool(p, b) => {
                self.charge(p, 1)?;
                self.charge(p, 1)?;
                Value::Bool(b)
            }
            Literal::Str(p, s) => {
                self.charge(p, 1)?;
                self.charge(p, 1 + s.chars().count() as u128)?;
                Value::Str(s)
            }
        })
    }

    /// The source name of the item `i`, for an error text.
    pub(super) fn item_name(&self, i: usize) -> &str {
        self.file
            .ast()
            .get(i)
            .map_or("", |item| item.name().name.as_str())
    }

    /// The memory number `id` of the current instantiation.
    pub(super) fn mem(&self, id: usize) -> Option<&Mem> {
        self.elab.work.mem(id)
    }

    /// The memory number `id` of the current instantiation, for a request.
    pub(super) fn mem_mut(&mut self, id: usize) -> Option<&mut Mem> {
        self.elab.work.mem_mut(id)
    }

    /// The serialization of an `InstantiationId` at the statement `pos`. It charges the walk
    /// that measures it, then its length in bytes, before it makes the text.
    fn serialize(&mut self, pos: Pos, module: &str, vs: &[Value]) -> Res<String> {
        let mut measure = 0u128;
        for v in vs {
            measure += v.measure_charge();
        }
        self.charge(pos, measure)?;
        let lens: Vec<u64> = vs.iter().map(|v| v.serialized_len(&self.tys)).collect();
        self.charge(pos, u128::from(InstantiationId::render_size(module, &lens)))?;
        let parts: Vec<String> = vs.iter().map(|v| v.serialize(&self.tys)).collect();
        Ok(InstantiationId::render(module, &parts))
    }

    /// The instantiation of the module item `i` with the converted arguments `args` and their
    /// parameter types, for the statement at `pos`. The parameters bind to them with no
    /// charge. The result is the index of the done instantiation.
    fn instantiate(&mut self, pos: Pos, i: usize, args: Vec<(TyId, Value)>) -> Res<usize> {
        let (types, vs): (Vec<TyId>, Vec<Value>) = args.into_iter().unzip();
        let file = self.file;
        let Some(Item::Module {
            pos: mp,
            name: m,
            params,
            domains,
            body,
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, pos, "an instance needs a module".to_owned());
        };
        let key = self.serialize(pos, &m.name, &vs)?;
        match self.elab.table.get(&key) {
            Some(Status::InProgress) => {
                return fail(
                    Code::S019,
                    pos,
                    format!(
                        "the instantiation of `{}` depends on itself, with the same arguments; \
                         change an argument at each level, and end the recursion with a \
                         `comptime if`",
                        m.name
                    ),
                );
            }
            Some(Status::Done(k)) => return Ok(*k),
            None => {}
        }
        let id = InstantiationId {
            module: m.name.clone(),
            args: vs,
        };
        let domain = match domains {
            None => Some(self.syms.clock),
            Some(ds) => match ds.first() {
                Some(d) => Some(self.sym(self.decl(d)?)),
                None => None,
            },
        };
        self.nested(pos, |ev| {
            let name = module_name(ev.elab.digest, &id, &key);
            ev.charge(pos, u128::from(name.byte_size()))?;
            let text = encode(&name);
            if ev.elab.names.contains(&text) {
                return fail(
                    Code::S019,
                    pos,
                    format!("two instantiations have the emitted name `{text}`"),
                );
            }
            ev.elab.table.insert(key.clone(), Status::InProgress);
            ev.emitted.push(text.clone());
            ev.elab.names.insert(text);
            let parent = std::mem::replace(&mut ev.elab.work, Work::new(domain, i));
            let naming = std::mem::take(&mut ev.naming);
            let start = ev.fuel.left();
            let args = id.args.clone();
            // The records of the body name this instantiation and start with no call frames.
            let outer_inst = ev.inst.replace(ev.emitted.len() - 1);
            let outer_calls = std::mem::take(&mut ev.calls);
            let outer_call = std::mem::take(&mut ev.call);
            let ran = ev.in_frame(None, |ev| {
                ev.in_item(i, ROOT, |ev| {
                    for ((q, t), v) in params.iter().zip(types).zip(args) {
                        let qid = ev.decl(&q.name)?;
                        ev.bind(
                            qid,
                            Slot {
                                ty: Some(t),
                                mutable: false,
                                value: Val::Static(v),
                            },
                        );
                    }
                    ev.block(*mp, body)
                })
            });
            ev.inst = outer_inst;
            ev.calls = outer_calls;
            ev.call = outer_call;
            ran?;
            ev.bindings()?;
            let lets = std::mem::take(&mut ev.naming.lets);
            ev.naming = naming;
            let used = start - ev.fuel.left();
            let w = std::mem::replace(&mut ev.elab.work, parent);
            let (mut body, publics, spent) = w.close();
            body.lets = lets;
            let iface = Iface::of(name, &body, i, &publics, &ev.syms.texts);
            let k = ev.elab.done.len();
            ev.elab.table.insert(key, Status::Done(k));
            ev.elab.done.push(Inst {
                iface,
                body,
                units: used - spent,
                pos: *mp,
            });
            ev.elab.work.charge_child(used);
            Ok(k)
        })
    }
}
