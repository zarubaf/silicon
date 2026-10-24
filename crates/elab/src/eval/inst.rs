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
//! The child module `design` holds the description of an instantiation and the `Design`. The child module `bind` holds the binding rule and the texts of `S018`.

use super::typed::Whole;
use super::{Evaluator, Mode, Out, ROOT, Res, Slot, fail, need};
use crate::agg::Agg;
use crate::hw::{Handle, Kind, Port, PortId, Seen, Val};
use crate::int::Int;
pub(super) use crate::names::entry_text;
use crate::names::{Sym, encode, module_name};
use crate::scan::Scan;
use crate::types::{Ty, TyId};
use crate::value::{InstantiationId, Value, int_size};
use crate::{Budget, Code};
use parse::ast::{Expr, Ident, Item, PortForm, Pos, Stmt, TypeExpr, UnOp};
use resolve::{Resolved, Target as Ref};
use std::collections::{BTreeMap, BTreeSet};

mod bind;
mod design;
mod family;
mod public;
use bind::{Breach, Need, Target};
pub use design::Design;
pub(crate) use design::{Bind, Inst, Mem, Sink};
use design::{Body, ChildDecl, Here, Iface, PortDecl, RegDecl};
pub(super) use family::{child_key, family_value};
use public::{PubKey, Public};

/// The work of the current instantiation. The resource number indexes `needs`, and the instance
/// number indexes `bound`. The memories are in the body, where `Handle::Mem` indexes them.
/// `inputs` counts the bindings of each child input, with the position and the call frame number of the first one. `dup`
/// holds the first `S018` of a second binding or a second port call by position. `spent` is the
/// fuel of the new children. `entries` holds the declared family entries by the symbol of the
/// public name and the key: the value of each entry and the position of its declaration. A family
/// binder has no frame slot. `publics` is the table of the public names of the owner. It holds the
/// form of each name by its symbol, with the position and the call frame number of its first
/// declaration. `owner` is the module item of the instantiation, whose static families the table
/// does not copy (`public_of`).
struct Work {
    body: Body,
    needs: Vec<Need>,
    bound: Vec<usize>,
    inputs: BTreeMap<(usize, PortId), (u64, Here)>,
    entries: BTreeMap<(Sym, u32), (Val, Pos)>,
    publics: BTreeMap<PubKey, (Public, Pos, usize)>,
    owner: usize,
    dup: Option<(Pos, Breach)>,
    spent: u64,
}

impl Work {
    fn new(domain: Option<Sym>, owner: usize) -> Work {
        Work {
            body: Body::new(domain),
            needs: Vec::new(),
            bound: Vec::new(),
            inputs: BTreeMap::new(),
            entries: BTreeMap::new(),
            publics: BTreeMap::new(),
            owner,
            dup: None,
            spent: 0,
        }
    }
}

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

    /// The two checks of a declaration or a `:=` statement before its module steps, with no
    /// charge (section 6.2). Under a guard it is `S016`, and the text names the function of the
    /// outermost call under the guard. In the static mode it is `S011`. A module body has
    /// neither.
    pub(super) fn hardware_checks(&self, pos: Pos, s: &Stmt) -> Res<()> {
        let here = self.item_name(self.item);
        if let Some(guard) = self.guard {
            let callee = self.item_name(guard.callee.unwrap_or(self.item));
            return fail(Code::S016, pos, guard.effect(callee));
        }
        let kind = match s {
            Stmt::Reg { .. } => "register",
            Stmt::Wire { .. } => "wire",
            Stmt::Mem { .. } => "memory",
            Stmt::Inst { .. } => "instance",
            Stmt::Input { .. } => "input",
            Stmt::Output { .. } => "output",
            _ => "`:=`",
        };
        match self.mode {
            Some(Mode::Static(m)) => fail(
                Code::S011,
                pos,
                format!(
                    "the `comptime fn` `{}` makes no hardware, but its call reaches this {kind} \
                     in `{here}`; call `{here}` from a `fn` or a module body",
                    self.item_name(m)
                ),
            ),
            Some(Mode::Eval) => fail(
                Code::S011,
                pos,
                format!(
                    "the `eval` command makes no hardware, but its expression reaches this \
                     {kind} in `{here}`; evaluate an expression that makes no hardware, or \
                     elaborate a module that calls `{here}`"
                ),
            ),
            None => Ok(()),
        }
    }

    /// A statement of a module body that makes hardware. Its statement charge is paid.
    pub(super) fn module_stmt(&mut self, s: &Stmt) -> Res<()> {
        match s {
            Stmt::Input {
                pos,
                name,
                form,
                ty,
            }
            | Stmt::Output {
                pos,
                name,
                form,
                ty,
            } => {
                let input = matches!(s, Stmt::Input { .. });
                if let PortForm::Indexed(k) = form {
                    return self.entry_decl(*pos, input, name, k, ty);
                }
                let tid = self.type_expr(ty)?;
                let t = self.data_type(*pos, tid)?;
                let id = self.decl(name)?;
                let v = match form {
                    PortForm::Keyed(k) => self.keyed_port(*pos, input, id, (t, tid), k)?,
                    _ => self.port(*pos, input, self.sym(id), (t, tid), None)?,
                };
                self.bind(
                    id,
                    Slot {
                        ty: Some(tid),
                        mutable: false,
                        value: v,
                    },
                );
            }
            Stmt::Reg {
                pos,
                name,
                ty,
                init,
            } => self.reg_stmt(*pos, name, ty, init)?,
            Stmt::Mem {
                pos,
                name,
                word,
                depth,
            } => self.mem_stmt(*pos, name, word, depth)?,
            Stmt::Wire { pos, name, ty } => {
                let tid = self.type_expr(ty)?;
                self.data_type(*pos, tid)?;
                let id = self.decl(name)?;
                let path = self.fresh(id);
                #[cfg(test)]
                self.elab.work.body.wires.push(path);
                let w = self.resource(Kind::Wire, path, tid, *pos, (self.sym(id), None), None);
                self.bind(
                    id,
                    Slot {
                        ty: Some(tid),
                        mutable: false,
                        value: w,
                    },
                );
            }
            Stmt::Connect { pos, target, value } => {
                let t = self.connect_target(target)?;
                let o = self.eval(value)?;
                let o = need(value, o)?;
                let ty = match &t {
                    Target::Own { ty, .. } => *ty,
                    Target::Child { port, .. } => port.ty,
                };
                let copies = o.is_ref();
                let v = self.typed_use(*pos, ty, copies, o, Whole)?;
                let v = self.sink_value(*pos, ty, v)?;
                self.bind_target(*pos, t, v);
            }
            Stmt::Inst {
                pos,
                name,
                module,
                args,
            } => self.inst_stmt(*pos, name, module, args)?,
            _ => {}
        }
        Ok(())
    }

    /// The value of a `:=` binding of the type `t` at `pos`, after its typed use. A static
    /// scalar becomes a hardware constant. A static value of another type is empty or has only
    /// static leaves, so it stays static. A hardware value and a hardware aggregate stay.
    fn sink_value(&mut self, pos: Pos, t: TyId, v: Val) -> Res<Agg> {
        match v {
            Val::Static(x) if matches!(self.tys.get(t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) => {
                Ok(Agg::Hw(self.lit(pos, x)?))
            }
            Val::Static(x) => Ok(Agg::Static(x)),
            Val::Hw(h) => Ok(Agg::Hw(h)),
            Val::Agg(a) => Ok(*a),
            v @ (Val::Handle(_) | Val::Pending(..)) => fail(
                Code::S010,
                pos,
                format!("{} is not data", self.text(v.seen())),
            ),
        }
    }

    /// A `reg` statement. A register in a combinational module is `S017` before its type.
    fn reg_stmt(&mut self, pos: Pos, name: &Ident, ty: &TypeExpr, init: &Expr) -> Res<()> {
        if self.elab.work.body.domain.is_none() {
            return fail(
                Code::S017,
                pos,
                "a combinational module has no register; remove `domains()` from the module, or \
                 move the register to a clocked module"
                    .to_owned(),
            );
        }
        let tid = self.type_expr(ty)?;
        let ty = self.data_type(pos, tid)?;
        let out = self.eval(init)?;
        let out = need(init, out)?;
        self.copy(pos, &out)?;
        let out = self.settle(pos, tid, out)?;
        let init = self.conform(pos, tid, out)?;
        let id = self.decl(name)?;
        let path = self.fresh(id);
        self.elab.work.body.regs.push(RegDecl {
            path,
            ty: ty.clone(),
            init,
            pos,
        });
        let reg = self.resource(Kind::Reg, path, tid, pos, (self.sym(id), None), None);
        self.bind(
            id,
            Slot {
                ty: Some(tid),
                mutable: false,
                value: reg,
            },
        );
        Ok(())
    }

    /// The memory number `id` of the current instantiation.
    pub(super) fn mem(&self, id: usize) -> Option<&Mem> {
        self.elab.work.body.mems.get(id)
    }

    /// The memory number `id` of the current instantiation, for a request.
    pub(super) fn mem_mut(&mut self, id: usize) -> Option<&mut Mem> {
        self.elab.work.body.mems.get_mut(id)
    }

    /// A `mem` statement. Each error is at the statement: a combinational module (`S017`), the
    /// word type, then the depth. No `[T; N]` type is made, so the depth adds no metadata
    /// charge. The name binds a memory handle, which is never data.
    fn mem_stmt(&mut self, pos: Pos, name: &Ident, word: &TypeExpr, depth: &Expr) -> Res<()> {
        if self.elab.work.body.domain.is_none() {
            return fail(
                Code::S017,
                pos,
                "a combinational module has no memory; remove `domains()` from the module, or \
                 move the memory to a clocked module"
                    .to_owned(),
            );
        }
        let tid = self.type_expr(word)?;
        self.mem_word(pos, tid)?;
        let out = self.structural(|ev| {
            let out = ev.eval(depth)?;
            need(depth, out)
        })?;
        let depth = self.mem_depth(pos, &out)?;
        let id = self.decl(name)?;
        let path = self.fresh(id);
        let sym = self.sym(id);
        let number = self.elab.work.body.mems.len();
        self.elab.work.body.mems.push(Mem {
            name: sym,
            path,
            word: tid,
            depth,
            pos,
            read: None,
            write: None,
            read_at: None,
            write_at: None,
        });
        self.bind(
            id,
            Slot {
                ty: None,
                mutable: false,
                value: Val::Handle(Handle::Mem(number)),
            },
        );
        Ok(())
    }

    /// An `instance` statement.
    fn inst_stmt(&mut self, pos: Pos, name: &Ident, module: &Ident, args: &[Expr]) -> Res<()> {
        let i = match self.file.target(module.id) {
            Some(Ref::Decl(id)) => self.items.get(&id).copied(),
            _ => None,
        }
        .unwrap_or(usize::MAX);
        let args = self.arguments(pos, i, args)?;
        let Some(Item::Module {
            name: m, domains, ..
        }) = self.file.ast().get(i)
        else {
            return fail(Code::S010, pos, "an instance needs a module".to_owned());
        };
        let clocked = domains.as_ref().is_none_or(|d| !d.is_empty());
        if self.elab.work.body.domain.is_none() && clocked {
            return fail(
                Code::S017,
                pos,
                format!(
                    "a combinational module has no clocked child `{}`; remove `domains()` from \
                     the module, or move the instance to a clocked module",
                    m.name
                ),
            );
        }
        // The converted arguments paid for their sizes, so the type adds no charge.
        let values: Vec<Value> = args.iter().map(|(_, v)| v.clone()).collect();
        let done = self.instantiate(pos, i, args)?;
        let ty = self.tys.instance(i, &m.name, values);
        let id = self.decl(name)?;
        let path = self.fresh(id);
        let k = self.elab.work.body.children.len();
        self.elab.work.body.children.push(ChildDecl {
            path,
            inst: done,
            pos,
            name: name.name.clone(),
        });
        self.elab.work.bound.push(0);
        self.bind(
            id,
            Slot {
                ty: None,
                mutable: false,
                value: Val::Handle(Handle::Inst {
                    id: k,
                    path,
                    inst: done,
                    ty,
                }),
            },
        );
        Ok(())
    }

    /// The target of a `:=` binding: a register, a wire, an own output, or a child input. A handle
    /// alias and the steps of `target_part` can select it. Each other part is `S017` at the start
    /// of the target. `S018` counts the target by its resource.
    fn connect_target(&mut self, e: &Expr) -> Res<Target> {
        let part = self.target_part(e)?;
        match self.store.seen(&part) {
            Seen::Handle(Handle::Res { kind, id, ty, path }) => Ok(Target::Own {
                kind: *kind,
                id: *id,
                ty: *ty,
                path: *path,
            }),
            Seen::Handle(Handle::Input { inst, path, port }) => Ok(Target::Child {
                inst: *inst,
                path: *path,
                port: port.clone(),
            }),
            seen => fail(Code::S017, e.pos(), Self::kind_text(&self.about(seen))),
        }
    }

    /// A port, a register, and a wire have a hardware data type (section 5.1), also an
    /// aggregate and an empty one. The metadata tells, so a function type at any depth is
    /// `S010` with no walk.
    fn data_type(&self, pos: Pos, t: TyId) -> Res<Ty> {
        self.not_handle(pos, t)?;
        if self.tys.meta(t).data {
            Ok(self.tys.get(t).clone())
        } else {
            fail(
                Code::S010,
                pos,
                format!(
                    "a port, a register, and a wire need a hardware data type, not `{}`; use a \
                     fixed-width type, for example `UInt[8]`",
                    self.tys.text(t)
                ),
            )
        }
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
            let mut body = w.body;
            body.lets = lets;
            let iface = Iface::of(name, &body, i, &w.publics);
            let k = ev.elab.done.len();
            ev.elab.table.insert(key, Status::Done(k));
            ev.elab.done.push(Inst {
                iface,
                body,
                units: used - w.spent,
                pos: *mp,
            });
            ev.elab.work.spent += used;
            Ok(k)
        })
    }
}
