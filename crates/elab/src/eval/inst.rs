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
//! 2. It charges the recursive size of the arguments, also for a done instantiation. Then the
//!    serialization charges the square of the size of each integer, and its length in bytes.
//! 3. A clocked child in a combinational module is `S017` at the statement.
//! 4. An instantiation in progress is `S019` at the statement. A done one gives its
//!    interface.
//! 5. A new one nests one level deeper (`S015`). Its emitted name charges its length in
//!    bytes, and it must be new (`S019`). Then it goes in progress, runs its body, checks its
//!    bindings, and is done.
//!
//! The units of an instantiation are its charges from the start of its parameters to the end
//! of its binding check, without the units of its new children. The charges of an `instance`
//! statement belong to the parent. The arguments of the top selection belong to no
//! instantiation.

use super::{Evaluator, Let, Out, ROOT, Res, Slot, Tag, fail, need};
use crate::hw::{Graph, Handle, HwId, Kind, Op, Port, Val};
use crate::int::Int;
use crate::names::{Name, PathId, Paths, Sym, encode, module_name};
use crate::scan::Scan;
use crate::value::{InstantiationId, Ty, Value, int_size};
use crate::{Budget, Code};
use parse::StackError;
use parse::ast::{Expr, Ident, Item, NodeId, Pos, Stmt, UnOp};
use resolve::{Kind as DeclKind, Resolved, Target as Ref};
use std::collections::{BTreeMap, BTreeSet};

/// A port declaration. A port keeps its source name.
pub(crate) struct PortDecl {
    pub sym: Sym,
    pub input: bool,
    pub ty: Ty,
    pub pos: Pos,
}

pub(crate) struct RegDecl {
    pub path: PathId,
    pub ty: Ty,
    pub init: Value,
    pub pos: Pos,
}

#[expect(
    dead_code,
    reason = "the lowering of #72 reads the types and positions"
)]
pub(crate) struct WireDecl {
    path: PathId,
    ty: Ty,
    pos: Pos,
}

/// A child instance: its path, the index of its done instantiation, and its statement.
pub(crate) struct ChildDecl {
    pub path: PathId,
    pub inst: usize,
    pub pos: Pos,
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
        port: Sym,
    },
}

pub(crate) struct Bind {
    pub sink: Sink,
    pub value: HwId,
    pub pos: Pos,
}

/// The hardware description of one instantiation, in evaluation order. A combinational
/// module has no domain.
pub(crate) struct Body {
    pub domain: Option<Sym>,
    pub ports: Vec<PortDecl>,
    pub regs: Vec<RegDecl>,
    wires: Vec<WireDecl>,
    pub lets: Vec<Let>,
    pub children: Vec<ChildDecl>,
    pub binds: Vec<Bind>,
}

impl Body {
    fn new(domain: Option<Sym>) -> Body {
        Body {
            domain,
            ports: Vec::new(),
            regs: Vec::new(),
            wires: Vec::new(),
            lets: Vec::new(),
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

/// The work of the current instantiation. The resource number indexes `needs`, and the
/// instance number indexes `bound`. `inputs` counts the bindings of each child input. `dup`
/// holds the first `S018` of a second binding by position. `spent` is the fuel of the new
/// children.
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
                    ty: q.ty,
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

    /// The port `sym` of the done instantiation `inst`.
    pub(crate) fn port(&self, inst: usize, sym: Sym) -> Option<Port> {
        self.done
            .get(inst)
            .and_then(|i| i.iface.ports.get(&sym))
            .copied()
    }
}

/// An elaborated design: the done instantiations in the order they finish, the top among
/// them, the position of the top selection, the used fuel, and the fuel that remains for the
/// lowering. It keeps the arenas of the hardware values and of the paths that its
/// descriptions refer to, and the text of each symbol. Dropping it is safe on any stack: it
/// holds no recursive value.
pub struct Design {
    pub(crate) insts: Vec<Inst>,
    pub(crate) top: usize,
    pub(crate) pos: Pos,
    used: u64,
    pub(crate) left: u64,
    pub(crate) graph: Graph,
    pub(crate) paths: Paths,
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
            .chain(b.wires.iter().map(|w| w.path))
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
/// arguments `xs`. The arguments charge as those of an `instance` statement.
pub(crate) fn elaborate(
    file: &Resolved,
    budget: Budget,
    scan: Scan,
    digest: fn(&str) -> String,
    pos: Pos,
    top: usize,
    xs: Vec<Literal>,
) -> Res<Design> {
    let mut ev = Evaluator::new(file, None, budget, scan, Elab::new(digest));
    let mut vs = Vec::with_capacity(xs.len());
    for x in xs {
        vs.push(ev.literal(x)?);
    }
    let mut sizes = 0u128;
    for v in &vs {
        sizes += u128::from(v.size());
    }
    ev.charge(pos, sizes)?;
    let top = ev.instantiate(pos, top, vs)?;
    Ok(Design {
        insts: ev.elab.done,
        top,
        pos,
        used: budget.fuel - ev.fuel.left(),
        left: ev.fuel.left(),
        graph: ev.graph,
        paths: ev.paths,
        texts: ev.syms.texts,
    })
}

fn before(a: Pos, b: Pos) -> bool {
    a < b
}

/// The target of a `:=` binding. It refers, so it charges nothing.
#[derive(Clone, Copy)]
enum Target {
    Own {
        kind: Kind,
        id: usize,
        ty: Ty,
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
    Input(usize),
}

impl Evaluator<'_> {
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

    /// The local slot that the name node `id` refers to.
    fn slot_of(&self, id: NodeId) -> Option<&Slot> {
        match self.file.target(id) {
            Some(Ref::Decl(id))
                if !matches!(
                    self.file.decl(id).kind,
                    DeclKind::Const | DeclKind::Fn | DeclKind::Module
                ) =>
            {
                self.store.frame().and_then(|f| f.get(&id))
            }
            _ => None,
        }
    }

    /// A statement of a module body that makes hardware. Its statement charge is paid.
    pub(super) fn module_stmt(&mut self, s: &Stmt) -> Res<()> {
        match s {
            Stmt::Input { pos, name, ty } | Stmt::Output { pos, name, ty } => {
                let t = self.type_expr(ty)?;
                let t = data_type(*pos, t)?;
                let v = self.port(*pos, matches!(s, Stmt::Input { .. }), name, t)?;
                let id = self.decl(name)?;
                self.bind(
                    id,
                    Slot {
                        ty: Some(t),
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
            } => {
                if self.elab.work.body.domain.is_none() {
                    return fail(
                        Code::S017,
                        *pos,
                        "a combinational module has no register".to_owned(),
                    );
                }
                let ty = self.type_expr(ty)?;
                let ty = data_type(*pos, ty)?;
                let out = self.eval(init)?;
                let out = need(init, out)?;
                self.copy(*pos, &out)?;
                let init = self.conform(*pos, ty, out)?;
                let id = self.decl(name)?;
                let path = self.fresh(id);
                self.elab.work.body.regs.push(RegDecl {
                    path,
                    ty,
                    init,
                    pos: *pos,
                });
                let reg = self.resource(Kind::Reg, path, ty, *pos, self.sym(id));
                self.bind(
                    id,
                    Slot {
                        ty: Some(ty),
                        mutable: false,
                        value: reg,
                    },
                );
            }
            Stmt::Wire { pos, name, ty } => {
                let t = self.type_expr(ty)?;
                let t = data_type(*pos, t)?;
                let id = self.decl(name)?;
                let path = self.fresh(id);
                self.elab.work.body.wires.push(WireDecl {
                    path,
                    ty: t,
                    pos: *pos,
                });
                let w = self.resource(Kind::Wire, path, t, *pos, self.sym(id));
                self.bind(
                    id,
                    Slot {
                        ty: Some(t),
                        mutable: false,
                        value: w,
                    },
                );
            }
            Stmt::Connect { pos, target, value } => {
                let t = self.connect_target(*pos, target)?;
                let o = self.eval(value)?;
                let o = need(value, o)?;
                self.copy(*pos, &o)?;
                let ty = match t {
                    Target::Own { ty, .. } => ty,
                    Target::Child { port, .. } => port.ty,
                };
                let h = match self.conform_val(*pos, ty, o)? {
                    Val::Static(v) => self.lit(*pos, v)?,
                    Val::Hw(h) => h,
                    v @ Val::Handle(_) => {
                        return fail(Code::S010, *pos, format!("{} is not data", self.text(&v)));
                    }
                };
                self.bind_target(*pos, t, h);
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

    /// An `instance` statement.
    fn inst_stmt(&mut self, pos: Pos, name: &Ident, module: &Ident, args: &[Expr]) -> Res<()> {
        let mut outs = Vec::with_capacity(args.len());
        for x in args {
            let o = self.eval(x)?;
            let o = need(x, o)?;
            self.check_static(pos, &o)?;
            outs.push(o);
        }
        let mut sizes = 0u128;
        for o in &outs {
            sizes += self.size(o);
        }
        self.charge(pos, sizes)?;
        let mut vs = Vec::with_capacity(outs.len());
        for o in outs {
            vs.push(self.static_value(pos, o)?);
        }
        let i = match self.file.target(module.id) {
            Some(Ref::Decl(id)) => self.items.get(&id).copied(),
            _ => None,
        }
        .unwrap_or(usize::MAX);
        if let Some(Item::Module {
            name: m, domains, ..
        }) = self.file.ast().get(i)
        {
            let clocked = domains.as_ref().is_none_or(|d| !d.is_empty());
            if self.elab.work.body.domain.is_none() && clocked {
                return fail(
                    Code::S017,
                    pos,
                    format!("a combinational module has no clocked child `{}`", m.name),
                );
            }
        }
        let done = self.instantiate(pos, i, vs)?;
        let id = self.decl(name)?;
        let path = self.fresh(id);
        let k = self.elab.work.body.children.len();
        self.elab.work.body.children.push(ChildDecl {
            path,
            inst: done,
            pos,
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
                }),
            },
        );
        Ok(())
    }

    /// A resource that needs one binding. The result is its handle.
    fn resource(&mut self, kind: Kind, path: PathId, ty: Ty, pos: Pos, name: Sym) -> Val {
        let id = self.elab.work.needs.len();
        self.elab.work.needs.push(Need {
            name,
            pos,
            count: 0,
        });
        Val::Handle(Handle::Res { kind, id, ty, path })
    }

    /// The port `name`. Its core name is its source name. The root frame counts it with the
    /// bindings of its name, so a name that is taken is `S019`.
    fn port(&mut self, pos: Pos, input: bool, name: &Ident, ty: Ty) -> Res<Val> {
        let id = self.decl(name)?;
        let sym = self.sym(id);
        let key = (ROOT.id, Tag::Sym(sym));
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
            ty,
            pos,
        });
        let path = self.paths.child(None, sym);
        if input {
            Ok(Val::Hw(self.graph.mk(pos, ty, Op::Ref(path), Vec::new())))
        } else {
            Ok(self.resource(Kind::Output, path, ty, pos, sym))
        }
    }

    /// The target of a `:=` binding: a register, a wire, an own output, or a child input,
    /// also through a handle alias.
    fn connect_target(&self, pos: Pos, e: &Expr) -> Res<Target> {
        let bad = || {
            fail(
                Code::S017,
                pos,
                "a `:=` target is a wire, a register, an own output, or a child input".to_owned(),
            )
        };
        match e {
            Expr::Name { id: nid, .. } => match self.slot_of(*nid).map(|s| &s.value) {
                Some(Val::Handle(Handle::Res { kind, id, ty, path })) => Ok(Target::Own {
                    kind: *kind,
                    id: *id,
                    ty: *ty,
                    path: *path,
                }),
                Some(Val::Handle(Handle::Input { inst, path, port })) => Ok(Target::Child {
                    inst: *inst,
                    path: *path,
                    port: *port,
                }),
                _ => bad(),
            },
            Expr::Field { base, field, .. } => {
                let Expr::Name { id: nid, .. } = &**base else {
                    return bad();
                };
                let Some(Val::Handle(Handle::Inst { id, path, inst })) =
                    self.slot_of(*nid).map(|s| &s.value)
                else {
                    return bad();
                };
                let port = self
                    .syms
                    .fields
                    .get(&field.pos)
                    .and_then(|s| self.elab.port(*inst, *s));
                match port {
                    Some(q) if q.input => Ok(Target::Child {
                        inst: *id,
                        path: *path,
                        port: q,
                    }),
                    Some(_) => fail(
                        Code::S017,
                        pos,
                        format!("`{}` is an output of the child, not a target", field.name),
                    ),
                    None => fail(
                        Code::S010,
                        pos,
                        format!("the instance has no port `{}`", field.name),
                    ),
                }
            }
            _ => bad(),
        }
    }

    /// Records the binding of `t` to `h`. The second binding of one target is an `S018`.
    fn bind_target(&mut self, pos: Pos, t: Target, h: HwId) {
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
                    sink: Sink::Own { kind, ty, path },
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
                        port: port.sym,
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
                        .find(|q| q.input && !work.inputs.contains_key(&(k, q.sym)))
                });
                let name = port.map_or("", |q| text(q.sym));
                format!("the input `{name}` of the child has no binding")
            }
        };
        fail(Code::S018, pos, message)
    }

    /// The serialization of an `InstantiationId` at the statement `pos`. It charges the
    /// decimal forms of its integers, then its length in bytes, before it makes the text.
    fn serialize(&mut self, pos: Pos, module: &str, vs: &[Value]) -> Res<String> {
        let mut decimal = 0u128;
        for v in vs {
            decimal += u128::from(v.decimal_charge());
        }
        self.charge(pos, decimal)?;
        let parts: Vec<String> = vs.iter().map(Value::serialize).collect();
        self.charge(
            pos,
            u128::from(InstantiationId::render_size(module, &parts)),
        )?;
        Ok(InstantiationId::render(module, &parts))
    }

    /// The instantiation of the module item `i` with the arguments `vs`, for the statement at
    /// `pos`. The result is the index of the done instantiation.
    fn instantiate(&mut self, pos: Pos, i: usize, vs: Vec<Value>) -> Res<usize> {
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
            ev.elab.names.insert(text);
            let parent = std::mem::replace(&mut ev.elab.work, Work::new(domain));
            let naming = std::mem::take(&mut ev.naming);
            let start = ev.fuel.left();
            let args = id.args.clone();
            ev.in_frame(None, |ev| {
                ev.in_item(i, ROOT, |ev| {
                    for (q, v) in params.iter().zip(args) {
                        let t = ev.type_expr(&q.ty)?;
                        let x = ev.conform(pos, t, Out::Made(Val::Static(v)))?;
                        let qid = ev.decl(&q.name)?;
                        ev.bind(
                            qid,
                            Slot {
                                ty: Some(t),
                                mutable: false,
                                value: Val::Static(x),
                            },
                        );
                    }
                    ev.block(*mp, body, true)
                })
            })?;
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

/// A port, a register, and a wire have a hardware type.
fn data_type(pos: Pos, t: Ty) -> Res<Ty> {
    if t.is_finite() || t == Ty::Bool {
        Ok(t)
    } else {
        fail(
            Code::S010,
            pos,
            format!(
                "a port, a register, and a wire have a hardware type, not {}",
                t.text()
            ),
        )
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
