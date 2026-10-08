//! The symbol tables that the passes share: the interface of each unit and
//! the names of each module body.

use crate::ast::{Conn, Design, Dir, Expr, Item, Module, Name, Num, Port, Stmt, Ty};
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
    /// A clock output. Pass 5 rejects it, and so it rejects every read of it.
    ClockOut,
}

/// A data port with its declared width. Pass 4 checks the width.
pub(super) struct DataPort<'a> {
    pub port: &'a Port,
    pub width: Num,
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
                (Dir::Input, Ty::Clock) => {
                    // Pass 5 rejects a second clock input.
                    sig.clock.get_or_insert(port);
                    PortRef::Clock
                }
                (Dir::Output, Ty::Clock) => PortRef::ClockOut,
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

    pub fn sig(&self, callee: Callee) -> Option<&Sig<'a>> {
        match callee {
            Callee::Module(m) => self.modules.get(m.index()),
            Callee::Extern(e) => self.externs.get(e.index()),
        }
    }

    pub fn externs(&self) -> &[Sig<'a>] {
        &self.externs
    }
}

/// What a name denotes in a module body.
#[derive(Clone, Copy)]
pub(super) enum Binding {
    Input(InputIdx),
    Clock,
    Output(OutputIdx),
    ClockOut,
    Let(LetIdx),
    Reg(RegIdx),
    Mem(MemIdx),
    Inst(InstIdx),
}

pub(super) struct LetDecl<'a> {
    pub name: &'a Name,
    pub width: Num,
}

pub(super) struct RegDecl<'a> {
    pub name: &'a Name,
    pub width: Num,
    pub span: Span,
}

pub(super) struct MemDecl<'a> {
    pub name: &'a Name,
    pub width: Num,
    pub depth: u32,
    pub span: Span,
}

pub(super) struct InstDecl<'a> {
    pub name: &'a Name,
    pub module: &'a Name,
    pub conns: &'a [Conn],
    /// `None` when the module name does not resolve; pass 3 reports that.
    pub callee: Option<Callee>,
    pub sig: Option<&'a Sig<'a>>,
    pub span: Span,
}

/// The declarations and the names of one module body.
pub(super) struct Scope<'a> {
    pub module: &'a Module,
    pub sig: &'a Sig<'a>,
    pub lets: Vec<LetDecl<'a>>,
    pub regs: Vec<RegDecl<'a>>,
    pub mems: Vec<MemDecl<'a>>,
    pub insts: Vec<InstDecl<'a>>,
    names: HashMap<&'a str, Binding>,
}

impl<'a> Scope<'a> {
    /// Builds the scope of every module, in item order.
    pub fn build_all(design: &'a Design, env: &'a Env<'a>) -> Vec<Scope<'a>> {
        let modules = design.items.iter().filter_map(|item| match item {
            Item::Module(m) => Some(m),
            Item::Extern(_) => None,
        });
        modules
            .zip(&env.modules)
            .map(|(module, sig)| Scope::build(module, sig, env))
            .collect()
    }

    fn build(module: &'a Module, sig: &'a Sig<'a>, env: &'a Env<'a>) -> Scope<'a> {
        let mut scope = Scope {
            module,
            sig,
            lets: Vec::new(),
            regs: Vec::new(),
            mems: Vec::new(),
            insts: Vec::new(),
            names: HashMap::new(),
        };
        for (name, entry) in sig.entries() {
            let binding = match entry {
                PortRef::Input(i) => Binding::Input(i),
                PortRef::Clock => Binding::Clock,
                PortRef::Output(o) => Binding::Output(o),
                PortRef::ClockOut => Binding::ClockOut,
            };
            scope.names.insert(name, binding);
        }
        for stmt in &module.stmts {
            scope.declare(stmt, env);
        }
        scope
    }

    fn declare(&mut self, stmt: &'a Stmt, env: &'a Env<'a>) {
        match stmt {
            Stmt::Let { name, width, .. } => {
                let idx = LetIdx::new(self.lets.len());
                self.lets.push(LetDecl {
                    name,
                    width: *width,
                });
                self.names.entry(&name.text).or_insert(Binding::Let(idx));
            }
            Stmt::Reg {
                name, width, span, ..
            } => {
                let idx = RegIdx::new(self.regs.len());
                self.regs.push(RegDecl {
                    name,
                    width: *width,
                    span: *span,
                });
                self.names.entry(&name.text).or_insert(Binding::Reg(idx));
            }
            Stmt::Mem {
                name,
                width,
                depth,
                span,
                ..
            } => {
                let idx = MemIdx::new(self.mems.len());
                self.mems.push(MemDecl {
                    name,
                    width: *width,
                    depth: depth.value,
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
                    sig: env.callee(&module.text).and_then(|c| env.sig(c)),
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

    /// Whether the expression is a single name of a clock input.
    pub fn is_clock_name(&self, expr: &Expr) -> bool {
        matches!(
            expr,
            Expr::Ref(name) if matches!(self.lookup(&name.text), Some(Binding::Clock))
        )
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
