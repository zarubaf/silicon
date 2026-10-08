//! The symbol tables that the passes share: the interface of each unit and
//! the names of each module body.

use crate::ast::{Conn, Design, Dir, Expr, Item, Module, Name, Port, Reset, Stmt, Ty};
use crate::diag::Span;
use crate::typed::{
    Callee, ExternIdx, InputIdx, InstIdx, LetIdx, MemIdx, ModIdx, OutputIdx, RegIdx,
};
use std::collections::HashMap;

/// What a port name denotes in its unit.
#[derive(Clone, Copy)]
pub(super) enum PortRef {
    Input(InputIdx),
    /// The one clock input.
    Clock,
    Output(OutputIdx),
    /// A clock output or a second clock input. Pass 5 rejects both.
    Stray,
}

/// A data port with its width.
pub(super) struct DataPort<'a> {
    pub port: &'a Port,
    pub width: u32,
}

/// The interface of a module or an extern.
pub(super) struct Sig<'a> {
    pub inputs: Vec<DataPort<'a>>,
    pub outputs: Vec<DataPort<'a>>,
    pub clock: Option<&'a Port>,
    ports: HashMap<&'a str, PortRef>,
}

impl<'a> Sig<'a> {
    fn new(ports: &'a [Port]) -> Sig<'a> {
        let mut sig = Sig {
            inputs: Vec::new(),
            outputs: Vec::new(),
            clock: None,
            ports: HashMap::new(),
        };
        for port in ports {
            let entry = match (port.dir, port.ty) {
                (Dir::Input, Ty::Bits(width)) => {
                    let idx = InputIdx::new(sig.inputs.len());
                    sig.inputs.push(DataPort { port, width });
                    PortRef::Input(idx)
                }
                (Dir::Output, Ty::Bits(width)) => {
                    let idx = OutputIdx::new(sig.outputs.len());
                    sig.outputs.push(DataPort { port, width });
                    PortRef::Output(idx)
                }
                (Dir::Input, Ty::Clock) if sig.clock.is_none() => {
                    sig.clock = Some(port);
                    PortRef::Clock
                }
                (_, Ty::Clock) => PortRef::Stray,
            };
            sig.ports.entry(&port.name.text).or_insert(entry);
        }
        sig
    }

    pub fn port(&self, name: &str) -> Option<PortRef> {
        self.ports.get(name).copied()
    }

    /// The names and the entries, in no particular order.
    fn entries(&self) -> impl Iterator<Item = (&'a str, PortRef)> + '_ {
        self.ports.iter().map(|(name, entry)| (*name, *entry))
    }
}

/// The interfaces of all units of a design.
pub(super) struct Env<'a> {
    modules: Vec<Sig<'a>>,
    externs: Vec<Sig<'a>>,
    items: HashMap<&'a str, Callee>,
}

impl<'a> Env<'a> {
    pub fn build(design: &'a Design) -> Env<'a> {
        let mut env = Env {
            modules: Vec::new(),
            externs: Vec::new(),
            items: HashMap::new(),
        };
        for item in &design.items {
            let (name, callee) = match item {
                Item::Module(m) => {
                    let callee = Callee::Module(ModIdx::new(env.modules.len()));
                    env.modules.push(Sig::new(&m.ports));
                    (&m.name, callee)
                }
                Item::Extern(e) => {
                    let callee = Callee::Extern(ExternIdx::new(env.externs.len()));
                    env.externs.push(Sig::new(&e.ports));
                    (&e.name, callee)
                }
            };
            env.items.entry(&name.text).or_insert(callee);
        }
        env
    }

    pub fn callee(&self, name: &str) -> Option<Callee> {
        self.items.get(name).copied()
    }

    pub fn module_sig(&self, module: ModIdx) -> Option<&Sig<'a>> {
        self.modules.get(module.index())
    }

    pub fn sig(&self, callee: Callee) -> Option<&Sig<'a>> {
        match callee {
            Callee::Module(m) => self.modules.get(m.index()),
            Callee::Extern(e) => self.externs.get(e.index()),
        }
    }

    pub fn extern_sig(&self, ext: ExternIdx) -> Option<&Sig<'a>> {
        self.externs.get(ext.index())
    }
}

/// What a name denotes in a module body.
#[derive(Clone, Copy)]
pub(super) enum Binding {
    Input(InputIdx),
    Clock,
    Output(OutputIdx),
    Stray,
    Let(LetIdx),
    Reg(RegIdx),
    Mem(MemIdx),
    Inst(InstIdx),
}

pub(super) struct LetDecl<'a> {
    pub name: &'a Name,
    pub width: u32,
    pub expr: &'a Expr,
    pub span: Span,
}

pub(super) struct RegDecl<'a> {
    pub name: &'a Name,
    pub width: u32,
    pub clk: &'a Name,
    pub reset: Option<&'a Reset>,
    pub span: Span,
}

pub(super) struct MemDecl<'a> {
    pub name: &'a Name,
    pub width: u32,
    pub depth: u32,
    pub clk: &'a Name,
    pub span: Span,
}

pub(super) struct InstDecl<'a> {
    pub name: &'a Name,
    pub module: &'a Name,
    pub conns: &'a [Conn],
    /// `None` when the module name does not resolve; pass 3 reports that.
    pub callee: Option<Callee>,
    pub span: Span,
}

/// The declarations and the names of one module body.
pub(super) struct Scope<'a> {
    pub module: &'a Module,
    pub index: ModIdx,
    pub lets: Vec<LetDecl<'a>>,
    pub regs: Vec<RegDecl<'a>>,
    pub mems: Vec<MemDecl<'a>>,
    pub insts: Vec<InstDecl<'a>>,
    names: HashMap<&'a str, Binding>,
}

impl<'a> Scope<'a> {
    /// Builds the scope of every module, in item order.
    pub fn build_all(design: &'a Design, env: &Env<'a>) -> Vec<Scope<'a>> {
        let modules = design.items.iter().filter_map(|item| match item {
            Item::Module(m) => Some(m),
            Item::Extern(_) => None,
        });
        (0usize..)
            .zip(modules)
            .map(|(i, module)| Scope::build(module, ModIdx::new(i), env))
            .collect()
    }

    fn build(module: &'a Module, index: ModIdx, env: &Env<'a>) -> Scope<'a> {
        let mut scope = Scope {
            module,
            index,
            lets: Vec::new(),
            regs: Vec::new(),
            mems: Vec::new(),
            insts: Vec::new(),
            names: HashMap::new(),
        };
        if let Some(sig) = env.module_sig(index) {
            for (name, entry) in sig.entries() {
                let binding = match entry {
                    PortRef::Input(i) => Binding::Input(i),
                    PortRef::Clock => Binding::Clock,
                    PortRef::Output(o) => Binding::Output(o),
                    PortRef::Stray => Binding::Stray,
                };
                scope.names.insert(name, binding);
            }
        }
        for stmt in &module.stmts {
            scope.declare(stmt, env);
        }
        scope
    }

    fn declare(&mut self, stmt: &'a Stmt, env: &Env<'a>) {
        match stmt {
            Stmt::Let {
                name,
                width,
                expr,
                span,
            } => {
                let idx = LetIdx::new(self.lets.len());
                self.lets.push(LetDecl {
                    name,
                    width: *width,
                    expr,
                    span: *span,
                });
                self.names.entry(&name.text).or_insert(Binding::Let(idx));
            }
            Stmt::Reg {
                name,
                width,
                clk,
                reset,
                span,
            } => {
                let idx = RegIdx::new(self.regs.len());
                self.regs.push(RegDecl {
                    name,
                    width: *width,
                    clk,
                    reset: reset.as_ref(),
                    span: *span,
                });
                self.names.entry(&name.text).or_insert(Binding::Reg(idx));
            }
            Stmt::Mem {
                name,
                width,
                depth,
                clk,
                span,
            } => {
                let idx = MemIdx::new(self.mems.len());
                self.mems.push(MemDecl {
                    name,
                    width: *width,
                    depth: *depth,
                    clk,
                    span: *span,
                });
                self.names.entry(&name.text).or_insert(Binding::Mem(idx));
            }
            Stmt::Inst {
                name,
                module,
                conns,
                span,
            } => {
                let idx = InstIdx::new(self.insts.len());
                self.insts.push(InstDecl {
                    name,
                    module,
                    conns,
                    callee: env.callee(&module.text),
                    span: *span,
                });
                self.names.entry(&name.text).or_insert(Binding::Inst(idx));
            }
            Stmt::Next { .. } | Stmt::Write { .. } | Stmt::Assign { .. } => {}
        }
    }

    pub fn lookup(&self, name: &str) -> Option<Binding> {
        self.names.get(name).copied()
    }

    /// The expressions of the body that compute values. The connections to
    /// clock inputs of instances are not among them.
    pub fn value_exprs(&self, env: &Env<'a>) -> Vec<&'a Expr> {
        let mut roots = Vec::new();
        for stmt in &self.module.stmts {
            match stmt {
                Stmt::Inst { .. } => {}
                other => roots.extend(stmt_exprs(other)),
            }
        }
        for inst in &self.insts {
            let sig = inst.callee.and_then(|c| env.sig(c));
            for conn in inst.conns {
                let is_clock = sig
                    .and_then(|s| s.port(&conn.port.text))
                    .is_some_and(|p| matches!(p, PortRef::Clock));
                if !is_clock {
                    roots.push(&conn.expr);
                }
            }
        }
        roots
    }
}

/// The expressions that a statement contains directly.
pub(super) fn stmt_exprs(stmt: &Stmt) -> Vec<&Expr> {
    match stmt {
        Stmt::Let { expr, .. } | Stmt::Next { expr, .. } | Stmt::Assign { expr, .. } => {
            vec![expr]
        }
        Stmt::Reg { reset, .. } => reset.iter().flat_map(|r| [&r.signal, &r.value]).collect(),
        Stmt::Mem { .. } => Vec::new(),
        Stmt::Write { addr, data, en, .. } => vec![addr, data, en],
        Stmt::Inst { conns, .. } => conns.iter().map(|c| &c.expr).collect(),
    }
}

/// Calls `f` on `expr` and on each expression inside it, outermost first.
pub(super) fn visit<'a>(expr: &'a Expr, f: &mut impl FnMut(&'a Expr)) {
    f(expr);
    match expr {
        Expr::Ref(_) | Expr::InstOut { .. } | Expr::Const { .. } => {}
        Expr::Unary { arg, .. } | Expr::Extract { arg, .. } | Expr::Replicate { arg, .. } => {
            visit(arg, f);
        }
        Expr::Read { addr, .. } => visit(addr, f),
        Expr::Binary { lhs, rhs, .. } | Expr::Icmp { lhs, rhs, .. } => {
            visit(lhs, f);
            visit(rhs, f);
        }
        Expr::Mux {
            cond, then, els, ..
        } => {
            visit(cond, f);
            visit(then, f);
            visit(els, f);
        }
    }
}
