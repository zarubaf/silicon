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
use crate::hw::{Graph, Handle, Kind, Port, Seen, Val, port_name};
use crate::int::Int;
use crate::names::{Name, PathId, Paths, Sym, encode, module_name};
use crate::scan::Scan;
use crate::types::{Ty, TyId, Types};
use crate::value::{InstantiationId, Value, int_size};
use crate::{Budget, Code};
use parse::StackError;
use parse::ast::{Expr, Ident, Item, Pos, Stmt, TypeExpr, UnOp};
use resolve::{Resolved, Target as Ref};
use std::collections::{BTreeMap, BTreeSet};

/// A port declaration. A port keeps its source name.
pub(crate) struct PortDecl {
    pub sym: Sym,
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

/// A memory of one instantiation (section 7.6): its name, its path, its word type, its depth,
/// and its `mem` statement. `read` holds the request of its first `read_port` call: the address
/// and the enable. `write` holds the request of its first `write_port` call: the address, the
/// data, and the enable. Each part of a request is after its typed use. `dup` holds the earliest
/// second call by position, with the callee, for its `S018` at the end of the body.
pub(crate) struct Mem {
    pub name: Sym,
    pub path: PathId,
    pub word: TyId,
    pub depth: u64,
    pub pos: Pos,
    pub read: Option<(Agg, Agg)>,
    pub write: Option<(Agg, Agg, Agg)>,
    pub dup: Option<(Pos, &'static str)>,
}

/// A child instance: its path, the index of its done instantiation, its statement, and its name.
pub(crate) struct ChildDecl {
    pub path: PathId,
    pub inst: usize,
    pub pos: Pos,
    pub name: String,
}

/// The target of a `:=` binding: an own resource, or an input of the child number `index`.
pub(crate) enum Sink {
    Own {
        kind: Kind,
        ty: Ty,
        path: PathId,
    },
    Child {
        index: usize,
        inst: PathId,
        port: Name,
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

/// A resource that needs one binding: its name, its declaration, and its bindings.
struct Need {
    name: Sym,
    pos: Pos,
    count: u64,
}

/// The work of the current instantiation. The resource number indexes `needs`, and the instance
/// number indexes `bound`. The memories are in the body, where `Handle::Mem` indexes them.
/// `inputs` counts the bindings of each child input. `dup` holds the first `S018` of a second
/// binding by position. `spent` is the fuel of the new children.
struct Work {
    body: Body,
    needs: Vec<Need>,
    bound: Vec<usize>,
    inputs: BTreeMap<(usize, Sym), u64>,
    dup: Option<Pos>,
    spent: u64,
}

impl Work {
    fn new(domain: Option<Sym>) -> Work {
        Work {
            body: Body::new(domain),
            needs: Vec::new(),
            bound: Vec::new(),
            inputs: BTreeMap::new(),
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

/// The interface of a done instantiation: its emitted name, its ports by the symbol of their
/// name, its number of inputs, and its domain.
pub(crate) struct Iface {
    pub name: Name,
    ports: BTreeMap<Sym, Port>,
    inputs: usize,
    pub domain: Option<Sym>,
}

impl Iface {
    fn of(name: Name, b: &Body) -> Iface {
        let mut ports = BTreeMap::new();
        let mut inputs = 0;
        for q in &b.ports {
            ports.insert(
                q.sym,
                Port {
                    sym: q.sym,
                    input: q.input,
                    ty: q.tid,
                    pos: q.pos,
                },
            );
            inputs += usize::from(q.input);
        }
        Iface {
            name,
            ports,
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
    pub(crate) fn port(&self, inst: usize, sym: Sym) -> Option<Port> {
        self.done
            .get(inst)
            .and_then(|i| i.iface.ports.get(&sym))
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

/// The kind of the first `S018` of a body.
#[derive(Clone, Copy)]
enum Missing {
    Second,
    Need(usize),
    /// The memory has no `read_port` or no `write_port`.
    Mem(usize),
    /// The second call of a port function of the memory.
    Port(usize),
    Input(usize),
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
    fn item_name(&self, i: usize) -> &str {
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
            Stmt::Input { pos, name, ty } | Stmt::Output { pos, name, ty } => {
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
                let w = self.resource(Kind::Wire, path, tid, *pos, self.sym(id));
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
        let reg = self.resource(Kind::Reg, path, tid, pos, self.sym(id));
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
            dup: None,
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
    fn resource(&mut self, kind: Kind, path: PathId, tid: TyId, pos: Pos, name: Sym) -> Val {
        let id = self.elab.work.needs.len();
        self.elab.work.needs.push(Need {
            name,
            pos,
            count: 0,
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
            input,
            ty: ty.clone(),
            tid,
            pos,
        });
        let path = self.paths.child(None, sym);
        if input {
            // An input refers to its name. An empty one stays a reference, so only a read of it
            // pays its zero (`name`).
            let r = Agg::Ref(Base::Name(path), tid);
            if self.tys.meta(tid).leaves.is_zero() {
                Ok(Val::Agg(Box::new(r)))
            } else {
                self.normalize(pos, r)
            }
        } else {
            Ok(self.resource(Kind::Output, path, tid, pos, sym))
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

    /// Records the binding of `t` to `h`. The second binding of one target is an `S018`.
    fn bind_target(&mut self, pos: Pos, t: Target, h: Agg) {
        let w = &mut self.elab.work;
        match t {
            Target::Own { kind, id, ty, path } => {
                if let Some(need) = w.needs.get_mut(id) {
                    if need.count == 1 {
                        w.dup = Some(earlier(w.dup, pos));
                    }
                    need.count += 1;
                }
                w.body.binds.push(Bind {
                    sink: Sink::Own {
                        kind,
                        ty: self.tys.get(ty).clone(),
                        path,
                    },
                    value: h,
                    pos,
                });
            }
            Target::Child { inst, path, port } => {
                let c = w.inputs.get(&(inst, port.sym)).copied().unwrap_or(0);
                if c == 0
                    && let Some(b) = w.bound.get_mut(inst)
                {
                    *b += 1;
                }
                if c == 1 {
                    w.dup = Some(earlier(w.dup, pos));
                }
                w.inputs.insert((inst, port.sym), c + 1);
                w.body.binds.push(Bind {
                    sink: Sink::Child {
                        index: inst,
                        inst: path,
                        port: port_name(self.syms.texts.get(port.sym).map_or("", String::as_str)),
                        ty: self.tys.get(port.ty).clone(),
                    },
                    value: h,
                    pos,
                });
            }
        }
    }

    /// The binding rule at the end of a body. A missing binding of an own resource is at its
    /// declaration, and one of a child input is at the `instance` statement. The counts
    /// select the first child with a free input, so only the interface of that child is
    /// searched. The error with the lowest position wins; only its message is made.
    fn bindings(&self) -> Res<()> {
        let work = &self.elab.work;
        let mut first = work.dup.map(|at| (at, Missing::Second));
        for (k, need) in work.needs.iter().enumerate() {
            if need.count == 0 {
                first = Some(first_of(first, need.pos, Missing::Need(k)));
            }
        }
        for (k, mem) in work.body.mems.iter().enumerate() {
            if let Some((at, _)) = mem.dup {
                first = Some(first_of(first, at, Missing::Port(k)));
            }
            if mem.read.is_none() || mem.write.is_none() {
                first = Some(first_of(first, mem.pos, Missing::Mem(k)));
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
            first = Some(first_of(first, at, Missing::Input(k)));
        }
        let Some((pos, missing)) = first else {
            return Ok(());
        };
        let text = |sym: Sym| self.syms.texts.get(sym).map_or("", String::as_str);
        let message = match missing {
            Missing::Second => "a second binding of one target".to_owned(),
            Missing::Need(k) => {
                let name = work.needs.get(k).map_or("", |need| text(need.name));
                format!("`{name}` has no binding")
            }
            Missing::Mem(k) => {
                let mem = work.body.mems.get(k);
                let name = mem.map_or("", |mem| text(mem.name));
                let port = if mem.is_some_and(|mem| mem.read.is_none()) {
                    "read_port"
                } else {
                    "write_port"
                };
                format!("the memory `{name}` has no `{port}`")
            }
            Missing::Port(k) => {
                let mem = work.body.mems.get(k);
                let name = mem.map_or("", |mem| text(mem.name));
                let port = mem.and_then(|mem| mem.dup).map_or("", |(_, port)| port);
                format!("a second `{port}` of the memory `{name}`")
            }
            Missing::Input(k) => {
                let iface = work
                    .body
                    .children
                    .get(k)
                    .and_then(|child| self.elab.done.get(child.inst))
                    .map(|i| &i.iface);
                let port = iface.and_then(|i| {
                    i.ports
                        .values()
                        .filter(|q| q.input && !work.inputs.contains_key(&(k, q.sym)))
                        .min_by_key(|q| (q.pos.line, q.pos.col))
                });
                let name = port.map_or("", |q| text(q.sym));
                let inst = work.body.children.get(k).map_or("", |c| c.name.as_str());
                format!(
                    "the input `{name}` of the instance `{inst}` has no binding; \
                     bind it with `{inst}.{name} := ...;`"
                )
            }
        };
        fail(Code::S018, pos, message)
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
                    "a port, a register, and a wire need a hardware data type, not {}",
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
                    format!("the instantiation of `{}` depends on itself", m.name),
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
            ran?;
            ev.bindings()?;
            let lets = std::mem::take(&mut ev.naming.lets);
            ev.naming = naming;
            let used = start - ev.fuel.left();
            let w = std::mem::replace(&mut ev.elab.work, parent);
            let mut body = w.body;
            body.lets = lets;
            let iface = Iface::of(name, &body);
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

/// The first of an `S018` and an earlier one. A tie keeps the earlier one.
fn first_of(old: Option<(Pos, Missing)>, at: Pos, missing: Missing) -> (Pos, Missing) {
    match old {
        Some((o, m)) if !before(at, o) => (o, m),
        _ => (at, missing),
    }
}

/// The earlier of two positions of an `S018`.
fn earlier(old: Option<Pos>, p: Pos) -> Pos {
    match old {
        Some(o) if !before(p, o) => o,
        _ => p,
    }
}
