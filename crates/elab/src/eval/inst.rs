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

use super::typed::Whole;
use super::{Evaluator, Let, Mode, Out, ROOT, Res, Slot, fail, need};
use crate::agg::{Agg, Base};
use crate::hw::{Graph, Handle, Kind, Port, PortId, Seen, Val};
use crate::int::Int;
pub(super) use crate::names::entry_text;
use crate::names::{Name, PathId, Paths, Sym, encode, module_name};
use crate::scan::Scan;
use crate::types::{Ty, TyId, Types};
use crate::value::{InstantiationId, Value, int_size};
use crate::{Budget, Code};
use parse::StackError;
use parse::ast::{Expr, Ident, Item, PortForm, Pos, Stmt, TypeExpr, UnOp};
use resolve::{DeclId, Resolved, Target as Ref};
use std::collections::{BTreeMap, BTreeSet};

mod family;
pub(super) use family::{child_key, family_value};

/// A port declaration. A port keeps its source name. A family entry has its key.
pub(crate) struct PortDecl {
    pub sym: Sym,
    pub key: Option<u32>,
    pub input: bool,
    pub ty: Ty,
    pub tid: TyId,
    pub pos: Pos,
}

pub(crate) struct RegDecl {
    pub path: PathId,
    pub ty: Ty,
    pub init: Value,
    pub pos: Pos,
}

/// A position with the number of the call frame that ran it (`Ev::call`).
pub(crate) type Here = (Pos, usize);

/// A memory of one instantiation (section 7.6): its name, its path, its word type, its depth,
/// and its `mem` statement. `read` holds the request of its first `read_port` call: the address
/// and the enable. `write` holds the request of its first `write_port` call: the address, the
/// data, and the enable. Each part of a request is after its typed use. `read_at` and `write_at`
/// hold the positions of the first calls, each with its call frame number (section 6.2).
pub(crate) struct Mem {
    pub name: Sym,
    pub path: PathId,
    pub word: TyId,
    pub depth: u64,
    pub pos: Pos,
    pub read: Option<(Agg, Agg)>,
    pub write: Option<(Agg, Agg, Agg)>,
    pub read_at: Option<Here>,
    pub write_at: Option<Here>,
}

/// A child instance: its path, the index of its done instantiation, its statement, and its name.
pub(crate) struct ChildDecl {
    pub path: PathId,
    pub inst: usize,
    pub pos: Pos,
    pub name: String,
}

/// The target of a `:=` binding: an own resource, or an input of the child number `index`. The
/// input names its port by symbol, so a binding copies no name; the lowering renders it.
pub(crate) enum Sink {
    Own {
        kind: Kind,
        ty: Ty,
        path: PathId,
    },
    Child {
        index: usize,
        inst: PathId,
        port: Sym,
        key: Option<u32>,
        ty: Ty,
    },
}

/// A `:=` binding. Its value has the type of the sink, and the lowering takes it leaf by leaf.
pub(crate) struct Bind {
    pub sink: Sink,
    pub value: Agg,
    pub pos: Pos,
}

/// The hardware description of one instantiation, in evaluation order. A combinational
/// module has no domain.
pub(crate) struct Body {
    pub domain: Option<Sym>,
    pub ports: Vec<PortDecl>,
    pub regs: Vec<RegDecl>,
    /// The paths of the wires. Only the tests read them: a wire lowers through its binding.
    #[cfg(test)]
    wires: Vec<PathId>,
    pub lets: Vec<Let>,
    pub mems: Vec<Mem>,
    pub children: Vec<ChildDecl>,
    pub binds: Vec<Bind>,
}

impl Body {
    fn new(domain: Option<Sym>) -> Body {
        Body {
            domain,
            ports: Vec::new(),
            regs: Vec::new(),
            #[cfg(test)]
            wires: Vec::new(),
            lets: Vec::new(),
            mems: Vec::new(),
            children: Vec::new(),
            binds: Vec::new(),
        }
    }
}

/// A resource that needs one binding: its name, its declaration, its bindings, and the position
/// of the first one with its call frame number.
struct Need {
    name: Sym,
    key: Option<u32>,
    pos: Pos,
    count: u64,
    first: Option<Here>,
}

/// A resource in an `S018` text (section 6.2): an own resource by its source name, or the input
/// `port` of the child number `child`, which renders as `u.p`. The key of a family entry renders
/// as `x[k]`.
#[derive(Clone, Copy)]
enum Subject {
    Own(Sym, Option<u32>),
    Input {
        child: usize,
        port: Sym,
        key: Option<u32>,
    },
}

/// The data of an `S018` text of section 6.2. A binding or a port call records it with no walk.
/// It holds symbols, indices, positions, and the item `h` of a helper. Its text renders once,
/// for the error that wins. `write` is true for `write_port`.
#[derive(Clone, Copy)]
enum Breach {
    Second {
        r: Subject,
        b: Pos,
        d: Pos,
    },
    SecondIn {
        r: Subject,
        h: usize,
    },
    Unbound(Sym, Option<u32>),
    /// The first child with a free input, by its number.
    Input(usize),
    NoPort {
        mem: usize,
        write: bool,
    },
    Port {
        mem: usize,
        write: bool,
        b: Pos,
    },
    PortIn {
        mem: usize,
        write: bool,
        h: usize,
    },
}

/// The work of the current instantiation. The resource number indexes `needs`, and the instance
/// number indexes `bound`. The memories are in the body, where `Handle::Mem` indexes them.
/// `inputs` counts the bindings of each child input, with the position and the call frame number of the first one. `dup`
/// holds the first `S018` of a second binding or a second port call by position. `spent` is the
/// fuel of the new children. `entries` holds the declared family entries by the family binder and
/// the key: the value of each entry and the position of its declaration. A family binder has no
/// frame slot.
struct Work {
    body: Body,
    needs: Vec<Need>,
    bound: Vec<usize>,
    inputs: BTreeMap<(usize, PortId), (u64, Here)>,
    entries: BTreeMap<(DeclId, u32), (Val, Pos)>,
    dup: Option<(Pos, Breach)>,
    spent: u64,
}

impl Work {
    fn new(domain: Option<Sym>) -> Work {
        Work {
            body: Body::new(domain),
            needs: Vec::new(),
            bound: Vec::new(),
            inputs: BTreeMap::new(),
            entries: BTreeMap::new(),
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

/// The interface of a done instantiation: its emitted name, its ports by their identity, its
/// number of inputs, and its domain. `item` is the module item. Its port families come from the
/// resolver (`Syms::families`), so they include a family without an entry.
pub(crate) struct Iface {
    pub name: Name,
    ports: BTreeMap<PortId, Port>,
    pub item: usize,
    inputs: usize,
    pub domain: Option<Sym>,
}

impl Iface {
    fn of(name: Name, b: &Body, item: usize) -> Iface {
        let mut ports = BTreeMap::new();
        let mut inputs = 0;
        for (order, q) in b.ports.iter().enumerate() {
            ports.insert(
                (q.sym, q.key),
                Port {
                    sym: q.sym,
                    key: q.key,
                    input: q.input,
                    ty: q.tid,
                    pos: q.pos,
                    order,
                },
            );
            inputs += usize::from(q.input);
        }
        Iface {
            name,
            ports,
            item,
            inputs,
            domain: b.domain,
        }
    }
}

/// A done instantiation: its interface, its description, its units, and the position of its
/// module item.
pub(crate) struct Inst {
    pub iface: Iface,
    pub body: Body,
    pub units: u64,
    pub pos: Pos,
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
            work: Work::new(None),
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

/// An elaborated design: the done instantiations in the order they finish, the top among
/// them, the position of the top selection, the used fuel, and the fuel that remains for the
/// lowering. It keeps the arenas of the hardware values and of the paths that its
/// descriptions refer to, the table of types and the field names of the struct items (the
/// lowering names the leaves of a record by them), and the text of each symbol. Dropping it is safe on any stack: it
/// holds no recursive value.
pub struct Design {
    pub(crate) insts: Vec<Inst>,
    pub(crate) top: usize,
    pub(crate) pos: Pos,
    used: u64,
    pub(crate) left: u64,
    pub(crate) graph: Graph,
    pub(crate) paths: Paths,
    pub(crate) tys: Types,
    pub(crate) field_order: Vec<Vec<Sym>>,
    pub(crate) texts: Vec<String>,
}

impl Design {
    /// The fuel that the elaboration used.
    #[must_use]
    pub fn used(&self) -> u64 {
        self.used
    }

    /// The output of `cost` (section 8) without the charges of the lowering: the total, then
    /// the units of each instantiation, sorted by its emitted name.
    #[cfg(test)]
    pub(crate) fn cost(&self) -> String {
        let lines = self
            .insts
            .iter()
            .map(|i| (encode(&i.iface.name), i.units))
            .collect();
        crate::flatten::cost_lines(self.used, lines)
    }

    /// The lowering of the design to core IR with the fuel that its elaboration leaves.
    /// The lowering recurses over the hardware values, so it runs on a thread with a stack
    /// for the highest of them.
    ///
    /// # Errors
    /// Returns an error if the machine cannot give the stack.
    pub fn lower(&self) -> Result<Result<crate::Lowered, crate::Failure>, StackError> {
        crate::flatten::lower(self)
    }

    /// The emitted names in the order in which the instantiations finish.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn order(&self) -> Vec<String> {
        self.insts.iter().map(|i| encode(&i.iface.name)).collect()
    }

    /// The core names of the named bindings, the registers, the wires, and the children of
    /// the instantiation with the emitted name `module`.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn core_names(&self, module: &str) -> Option<Vec<String>> {
        let i = self
            .insts
            .iter()
            .find(|i| encode(&i.iface.name) == module)?;
        let b = &i.body;
        let paths = b
            .lets
            .iter()
            .map(|l| l.path)
            .chain(b.regs.iter().map(|r| r.path))
            .chain(b.wires.iter().copied())
            .chain(b.children.iter().map(|c| c.path));
        Some(
            paths
                .map(|p| encode(&self.paths.name(p, &self.texts)))
                .collect(),
        )
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

fn before(a: Pos, b: Pos) -> bool {
    a < b
}

/// The target of a `:=` binding. It refers, so it charges nothing.
#[derive(Clone)]
enum Target {
    Own {
        kind: Kind,
        id: usize,
        ty: TyId,
        path: PathId,
    },
    Child {
        inst: usize,
        path: PathId,
        port: Port,
    },
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
                if let PortForm::Indexed(k) = form {
                    return self.entry_decl(*pos, matches!(s, Stmt::Input { .. }), name, k, ty);
                }
                let tid = self.type_expr(ty)?;
                let t = self.data_type(*pos, tid)?;
                let v = self.port(*pos, matches!(s, Stmt::Input { .. }), name, (t, tid))?;
                let id = self.decl(name)?;
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
                let w = self.resource(Kind::Wire, path, tid, *pos, (self.sym(id), None));
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
        let reg = self.resource(Kind::Reg, path, tid, pos, (self.sym(id), None));
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

    /// A resource that needs one binding. The result is its handle.
    fn resource(
        &mut self,
        kind: Kind,
        path: PathId,
        tid: TyId,
        pos: Pos,
        (name, key): (Sym, Option<u32>),
    ) -> Val {
        let id = self.elab.work.needs.len();
        self.elab.work.needs.push(Need {
            name,
            key,
            pos,
            count: 0,
            first: None,
        });
        Val::Handle(Handle::Res {
            kind,
            id,
            ty: tid,
            path,
        })
    }

    /// The port `name`. Its core name is its source name. The root frame counts it with the
    /// bindings of its name, so a name that is taken is `S019`.
    fn port(&mut self, pos: Pos, input: bool, name: &Ident, (ty, tid): (Ty, TyId)) -> Res<Val> {
        let id = self.decl(name)?;
        let sym = self.sym(id);
        let key = (ROOT.id, sym);
        let v = self.naming.versions.get(&key).copied().unwrap_or(0);
        self.naming.versions.insert(key, v + 1);
        if v != 0 {
            return fail(
                Code::S019,
                pos,
                format!("two declarations have the core name `{}`", name.name),
            );
        }
        self.elab.work.body.ports.push(PortDecl {
            sym,
            key: None,
            input,
            ty: ty.clone(),
            tid,
            pos,
        });
        let path = self.paths.child(None, sym);
        self.port_value(pos, input, path, tid, (sym, None))
    }

    /// The value of the port at `path`, scalar or family entry (`key`). An input refers to its
    /// name. An empty one stays a reference, so only a read of it pays its zero (`name`). An
    /// output is a resource that needs one binding.
    fn port_value(
        &mut self,
        pos: Pos,
        input: bool,
        path: PathId,
        tid: TyId,
        name: (Sym, Option<u32>),
    ) -> Res<Val> {
        if !input {
            return Ok(self.resource(Kind::Output, path, tid, pos, name));
        }
        let r = Agg::Ref(Base::Name(path), tid);
        if self.tys.meta(tid).leaves.is_zero() {
            Ok(Val::Agg(Box::new(r)))
        } else {
            self.normalize(pos, r)
        }
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

    /// The function whose body runs, the `{h}` of the `S018` texts of a helper (section 6.2). A
    /// module body gives none.
    fn helper(&self) -> Option<usize> {
        matches!(self.file.ast().get(self.item), Some(Item::Fn { .. })).then_some(self.item)
    }

    /// Records the `S018` data `x` at `pos`. The first by position wins, and a tie keeps the
    /// first recorded one (section 6.2).
    fn breach(&mut self, pos: Pos, x: Breach) {
        let w = &mut self.elab.work;
        w.dup = Some(match w.dup {
            Some((q, y)) if !before(pos, q) => (q, y),
            _ => (pos, x),
        });
    }

    /// The `S018` data of a second binding or a second port call at `pos`, whose first one is at
    /// `first.0` in the call frame `first.1`. When both are at `pos`, one `:=` or call runs
    /// again. When the first one ran in another call, the text names the function. A repeat in
    /// one call keeps the plain text (section 6.2).
    fn again(&self, pos: Pos, first: Here) -> Option<usize> {
        if first.0 == pos && first.1 != self.call {
            self.helper()
        } else {
            None
        }
    }

    /// Records the second port call of the memory number `id` at `pos`, if its first call of
    /// that kind exists. The result tells if the call is a second one.
    pub(super) fn second_call(&mut self, pos: Pos, id: usize, write: bool) -> bool {
        let Some(mem) = self.mem(id) else {
            return false;
        };
        let Some(b) = (if write { mem.write_at } else { mem.read_at }) else {
            return false;
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Seconds, 1);
        let x = match self.again(pos, b) {
            Some(h) => Breach::PortIn { mem: id, write, h },
            None => Breach::Port {
                mem: id,
                write,
                b: b.0,
            },
        };
        self.breach(pos, x);
        true
    }

    /// The `S018` data of the second binding at `pos` of the resource `subject`, whose first
    /// binding is at `first` and whose declaration is at `decl`.
    fn second_binding(&self, pos: Pos, subject: Subject, first: Here, decl: Pos) -> Breach {
        match self.again(pos, first) {
            Some(h) => Breach::SecondIn { r: subject, h },
            None => Breach::Second {
                r: subject,
                b: first.0,
                d: decl,
            },
        }
    }

    /// Records the binding of `t` to `value`. The second binding of one target is an `S018`,
    /// and the first binding keeps its position for its text.
    fn bind_target(&mut self, pos: Pos, t: Target, value: Agg) {
        let here = (pos, self.call);
        let sink = match t {
            Target::Own { kind, id, ty, path } => {
                let need = self.elab.work.needs.get(id);
                let seen = need.map(|n| (n.count, n.first, (n.name, n.key), n.pos));
                if let Some((count, first, name, decl)) = seen {
                    if count == 1 {
                        let x = self.second_binding(
                            pos,
                            Subject::Own(name.0, name.1),
                            first.unwrap_or(here),
                            decl,
                        );
                        self.breach(pos, x);
                    }
                    if let Some(n) = self.elab.work.needs.get_mut(id) {
                        n.count += 1;
                        n.first = n.first.or(Some(here));
                    }
                }
                let ty = self.tys.get(ty).clone();
                Sink::Own { kind, ty, path }
            }
            Target::Child { inst, path, port } => {
                let key = (inst, port.id());
                let (count, first) = self
                    .elab
                    .work
                    .inputs
                    .get(&key)
                    .copied()
                    .unwrap_or((0, here));
                if count == 0
                    && let Some(n) = self.elab.work.bound.get_mut(inst)
                {
                    *n += 1;
                }
                self.elab.work.inputs.insert(key, (count + 1, first));
                if count == 1 {
                    let decl = self
                        .elab
                        .work
                        .body
                        .children
                        .get(inst)
                        .map_or(pos, |child| child.pos);
                    let subject = Subject::Input {
                        child: inst,
                        port: port.sym,
                        key: port.key,
                    };
                    let x = self.second_binding(pos, subject, first, decl);
                    self.breach(pos, x);
                }
                let ty = self.tys.get(port.ty).clone();
                Sink::Child {
                    index: inst,
                    inst: path,
                    port: port.sym,
                    key: port.key,
                    ty,
                }
            }
        };
        self.elab.work.body.binds.push(Bind { sink, value, pos });
    }

    /// The binding rule at the end of a body. A missing binding of an own resource is at its
    /// declaration, and one of a child input is at the `instance` statement. The counts
    /// select the first child with a free input, so only the interface of that child is
    /// searched. The records compete by position, and the text of the winner renders once
    /// (section 6.2).
    fn bindings(&self) -> Res<()> {
        let work = &self.elab.work;
        let first_of = |old: Option<(Pos, Breach)>, at: Pos, x: Breach| match old {
            Some(o) if !before(at, o.0) => Some(o),
            _ => Some((at, x)),
        };
        let mut first = work.dup;
        for need in &work.needs {
            if need.count == 0 {
                first = first_of(first, need.pos, Breach::Unbound(need.name, need.key));
            }
        }
        for (k, mem) in work.body.mems.iter().enumerate() {
            if mem.read.is_none() || mem.write.is_none() {
                let x = Breach::NoPort {
                    mem: k,
                    write: mem.read.is_some(),
                };
                first = first_of(first, mem.pos, x);
            }
        }
        let mut free: Option<(Pos, usize)> = None;
        for (k, child) in work.body.children.iter().enumerate() {
            let inputs = self.elab.done.get(child.inst).map_or(0, |i| i.iface.inputs);
            if work.bound.get(k).copied().unwrap_or(0) < inputs
                && free.is_none_or(|(at, _)| before(child.pos, at))
            {
                free = Some((child.pos, k));
            }
        }
        if let Some((at, k)) = free {
            first = first_of(first, at, Breach::Input(k));
        }
        let Some((pos, x)) = first else {
            return Ok(());
        };
        fail(Code::S018, pos, self.breach_text(x))
    }

    /// The text of the `S018` of the first child number `k` with a free input: the free input
    /// with the first source position.
    fn free_input_text(&self, k: usize) -> String {
        let work = &self.elab.work;
        let text = |sym: Sym| self.syms.texts.get(sym).map_or("", String::as_str);
        let iface = work
            .body
            .children
            .get(k)
            .and_then(|child| self.elab.done.get(child.inst))
            .map(|i| &i.iface);
        let port = iface.and_then(|i| {
            i.ports
                .values()
                .filter(|q| q.input && !work.inputs.contains_key(&(k, q.id())))
                .min_by_key(|q| (q.pos.line, q.pos.col, q.order))
        });
        let name = port.map_or_else(String::new, |q| entry_text(text(q.sym), q.key));
        let inst = work.body.children.get(k).map_or("", |c| c.name.as_str());
        format!(
            "the input `{name}` of the instance `{inst}` has no binding; \
             bind it with `{inst}.{name} := ...;`"
        )
    }

    /// The text of the `S018` data `x` (section 6.2).
    fn breach_text(&self, x: Breach) -> String {
        let work = &self.elab.work;
        let sym_text = |sym: Sym| self.syms.texts.get(sym).map_or("", String::as_str);
        let at = |p: Pos| format!("{}:{}", p.line, p.col);
        let subject = |r: Subject| match r {
            Subject::Own(sym, key) => entry_text(sym_text(sym), key),
            Subject::Input { child, port, key } => {
                let u = work
                    .body
                    .children
                    .get(child)
                    .map_or("", |c| c.name.as_str());
                format!("{u}.{}", entry_text(sym_text(port), key))
            }
        };
        let mem_name = |k: usize| work.body.mems.get(k).map_or("", |m| sym_text(m.name));
        let call = |write: bool| if write { "write_port" } else { "read_port" };
        let item = |h: usize| self.item_name(h);
        let text = match x {
            Breach::Second { r, b, d } => format!(
                "`{}` has a second binding; the first binding is at {}, and the declaration is \
                 at {}; remove one of the two bindings",
                subject(r),
                at(b),
                at(d)
            ),
            Breach::SecondIn { r, h } => format!(
                "`{}` has a second binding, because the `:=` in `{}` runs again for it; run \
                 the `:=` once for each resource, for example with one call of `{}` for each",
                subject(r),
                item(h),
                item(h)
            ),
            Breach::Unbound(sym, key) => {
                let r = entry_text(sym_text(sym), key);
                format!(
                    "`{r}` has no binding; bind it with `{r} := ...;`, or remove its declaration"
                )
            }
            Breach::Input(k) => self.free_input_text(k),
            Breach::NoPort { mem, write } => format!(
                "the memory `{}` has no `{}`; call `{}` on it once, or remove the memory",
                mem_name(mem),
                call(write),
                call(write)
            ),
            Breach::Port {
                mem,
                write: false,
                b,
            } => format!(
                "the memory `{}` has a second `read_port`; the first call is at {}; call \
                 `read_port` once and keep its response in a `let`",
                mem_name(mem),
                at(b)
            ),
            Breach::Port {
                mem,
                write: true,
                b,
            } => format!(
                "the memory `{}` has a second `write_port`; the first call is at {}; make one \
                 call, and select its address, data, and enable with a hardware `if`",
                mem_name(mem),
                at(b)
            ),
            Breach::PortIn {
                mem,
                write: false,
                h,
            } => format!(
                "the memory `{}` has a second `read_port`, because the call in `{}` runs again \
                 for it; run the call once for each memory, for example with one call of `{}` \
                 for each",
                mem_name(mem),
                item(h),
                item(h)
            ),
            Breach::PortIn {
                mem,
                write: true,
                h,
            } => format!(
                "the memory `{}` has a second `write_port`, because the call in `{}` runs again \
                 for it; run the call once for each memory, for example with one call of `{}` \
                 for each",
                mem_name(mem),
                item(h),
                item(h)
            ),
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::TextBytes, text.len() as u64);
        text
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
            let parent = std::mem::replace(&mut ev.elab.work, Work::new(domain));
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
            let iface = Iface::of(name, &body, i);
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
