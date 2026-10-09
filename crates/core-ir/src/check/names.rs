//! Pass 2 (`E002`, unique names) and pass 3 (`E003`, name resolution).

use super::rx::{
    ConnArg, RawConst, RawModule, RawRx, Rx, RxConn, RxInst, RxLet, RxReg, RxReset, RxWrite, Target,
};
use super::scope::{Binding, Env, InstDecl, PortRef, Scope};
use super::{error, first_error};
use crate::ast::{Design, Expr, Item, Name, Port, Stmt};
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed::{Callee, MemIdx, ModIdx};
use std::collections::HashSet;

/// The lowering generates names with this prefix.
const RESERVED_PREFIX: &str = "silicon_";

/// The lowering names an instance result `<inst>.<port>`. The parser never
/// produces this character in a name; a hand-built AST can.
const RESERVED_CHAR: char = '.';

/// The names defined in one scope.
#[derive(Default)]
struct Defs<'a> {
    seen: HashSet<&'a str>,
    errors: Vec<Diagnostic>,
}

impl<'a> Defs<'a> {
    fn define(&mut self, name: &'a Name) {
        if name.text.starts_with(RESERVED_PREFIX) {
            self.errors.push(error(
                ErrorCode::E002,
                name.span,
                format!(
                    "`{}` starts with the reserved prefix `{RESERVED_PREFIX}`",
                    name.text
                ),
            ));
        }
        if name.text.contains(RESERVED_CHAR) {
            self.errors.push(error(
                ErrorCode::E002,
                name.span,
                format!(
                    "`{}` contains the reserved character `{RESERVED_CHAR}`",
                    name.text
                ),
            ));
        }
        if !self.seen.insert(&name.text) {
            self.errors.push(error(
                ErrorCode::E002,
                name.span,
                format!("`{}` is already defined in this scope", name.text),
            ));
        }
    }

    fn ports(&mut self, ports: &'a [Port]) {
        for port in ports {
            self.define(&port.name);
        }
    }
}

/// Pass 2.
pub(super) fn duplicates(design: &Design) -> Vec<Diagnostic> {
    let mut items = Defs::default();
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => {
                items.define(&m.name);
                let mut body = Defs::default();
                body.ports(&m.ports);
                for stmt in &m.stmts {
                    match stmt {
                        Stmt::Let { name, .. }
                        | Stmt::Reg { name, .. }
                        | Stmt::Mem { name, .. }
                        | Stmt::Inst { name, .. } => body.define(name),
                        Stmt::Next { .. } | Stmt::Write { .. } | Stmt::Assign { .. } => {}
                    }
                }
                errors.extend(body.errors);
            }
            Item::Extern(e) => {
                items.define(&e.name);
                let mut body = Defs::default();
                body.ports(&e.ports);
                errors.extend(body.errors);
            }
        }
    }
    errors.extend(items.errors);
    errors
}

/// Pass 3. It also resolves every name of every module.
pub(super) fn resolve<'a>(
    design: &Design,
    env: &Env,
    scopes: &[Scope<'a>],
) -> Result<(Vec<RawModule<'a>>, ModIdx), Diagnostic> {
    let mut errors = Vec::new();
    let top = match env.callee(&design.top.text) {
        Some(Callee::Module(top)) => Ok(top),
        _ => Err(error(
            ErrorCode::E003,
            design.top.span,
            format!("`{}` is not a module", design.top.text),
        )),
    };
    errors.extend(top.clone().err());
    let modules: Vec<_> = scopes
        .iter()
        .map(|scope| {
            Resolver {
                scope,
                errors: &mut errors,
            }
            .module()
        })
        .collect();
    first_error(errors)?;
    Ok((modules, top?))
}

struct Resolver<'e, 'a> {
    scope: &'e Scope<'a>,
    errors: &'e mut Vec<Diagnostic>,
}

/// An `Option` here is `None` after an error was recorded. The caller drops
/// the result when it records any error.
impl<'a> Resolver<'_, 'a> {
    fn unknown(&mut self, name: &Name, what: &str) {
        self.errors.push(error(
            ErrorCode::E003,
            name.span,
            format!("`{}` is not {what}", name.text),
        ));
    }

    fn module(&mut self) -> RawModule<'a> {
        let scope = self.scope;
        let mut module = RawModule {
            lets: Vec::new(),
            regs: Vec::new(),
            nexts: Vec::new(),
            assigns: Vec::new(),
            writes: Vec::new(),
            insts: Vec::new(),
            clock_assigns: Vec::new(),
        };
        for stmt in &scope.module.stmts {
            self.stmt(stmt, &mut module);
        }
        for inst in &scope.insts {
            if let Some(resolved) = self.inst(inst) {
                module.insts.push(resolved);
            }
        }
        module
    }

    fn stmt(&mut self, stmt: &'a Stmt, module: &mut RawModule<'a>) {
        match stmt {
            Stmt::Let {
                width, expr, span, ..
            } => {
                if let Some(expr) = self.expr(expr) {
                    module.lets.push(RxLet {
                        width: width.value,
                        span: *span,
                        expr,
                    });
                }
            }
            Stmt::Reg {
                width, clk, reset, ..
            } => {
                self.clock(clk);
                let reset = reset.as_ref().and_then(|r| {
                    let (signal, value) = (self.expr(&r.signal), self.expr(&r.value));
                    Some(RxReset {
                        span: r.span,
                        signal: signal?,
                        value: value?,
                    })
                });
                module.regs.push(RxReg {
                    width: width.value,
                    reset,
                });
            }
            Stmt::Mem { clk, .. } => self.clock(clk),
            Stmt::Next { reg, expr, span } => {
                let expr = self.expr(expr);
                let Some(Binding::Reg(i)) = self.scope.lookup(&reg.text) else {
                    self.unknown(reg, "a register");
                    return;
                };
                let width = self.scope.regs.get(i.index()).map(|d| d.width.value);
                if let (Some(expr), Some(width)) = (expr, width) {
                    module.nexts.push(Target {
                        slot: i,
                        width,
                        span: *span,
                        expr,
                    });
                }
            }
            Stmt::Assign { out, expr, span } => {
                let expr = self.expr(expr);
                match self.scope.lookup(&out.text) {
                    Some(Binding::Output(o)) => {
                        let width = self.scope.sig.outputs.get(o.index()).map(|p| p.width.value);
                        if let (Some(expr), Some(width)) = (expr, width) {
                            module.assigns.push(Target {
                                slot: o,
                                width,
                                span: *span,
                                expr,
                            });
                        }
                    }
                    // Pass 5 rejects the clock output port itself, but pass 4
                    // checks the constants of the operand first.
                    Some(Binding::ClockOut) => module.clock_assigns.extend(expr),
                    _ => self.unknown(out, "an output"),
                }
            }
            Stmt::Write {
                mem,
                port,
                addr,
                data,
                en,
                span,
            } => {
                let (addr, data, en) = (self.expr(addr), self.expr(data), self.expr(en));
                let Some(m) = self.memory(mem) else {
                    return;
                };
                let decl = self.scope.mems.get(m.index());
                if let (Some(addr), Some(data), Some(en), Some(decl)) = (addr, data, en, decl) {
                    module.writes.push(RxWrite {
                        mem: m,
                        port: *port,
                        span: *span,
                        data_width: decl.width.value,
                        depth: decl.depth,
                        addr,
                        data,
                        en,
                    });
                }
            }
            Stmt::Inst { .. } => {}
        }
    }

    fn clock(&mut self, clk: &Name) {
        if !matches!(self.scope.lookup(&clk.text), Some(Binding::Clock)) {
            self.unknown(clk, "a clock input");
        }
    }

    fn memory(&mut self, name: &Name) -> Option<MemIdx> {
        if let Some(Binding::Mem(m)) = self.scope.lookup(&name.text) {
            Some(m)
        } else {
            self.unknown(name, "a memory");
            None
        }
    }

    fn inst(&mut self, inst: &InstDecl<'a>) -> Option<RxInst<'a, Span, RawConst<'a>>> {
        let (Some(callee), Some(sig)) = (inst.callee, inst.sig) else {
            self.unknown(inst.module, "a module or an extern");
            for conn in inst.conns {
                self.expr(&conn.expr);
            }
            return None;
        };
        let mut conns = Vec::new();
        for conn in inst.conns {
            let port = sig.port(&conn.port.text);
            let arg = match port {
                Some(PortRef::Clock) if self.scope.is_clock_name(&conn.expr) => {
                    Some(ConnArg::ClockName)
                }
                Some(PortRef::Clock) => self.expr(&conn.expr).map(|expr| ConnArg::ClockOther {
                    expr_span: conn.expr.span(),
                    expr,
                }),
                Some(PortRef::Input(i)) => {
                    let width = sig.inputs.get(i.index()).map(|p| p.width.value);
                    let expr = self.expr(&conn.expr);
                    width.zip(expr).map(|(width, expr)| ConnArg::Data {
                        input: i,
                        width,
                        expr,
                    })
                }
                _ => {
                    self.unknown(&conn.port, "an input of the instance");
                    self.expr(&conn.expr);
                    None
                }
            };
            if let Some(arg) = arg {
                conns.push(RxConn {
                    port: &conn.port,
                    span: conn.span,
                    arg,
                });
            }
        }
        Some(RxInst {
            callee,
            sig,
            span: inst.span,
            conns,
        })
    }

    fn expr(&mut self, expr: &'a Expr) -> Option<RawRx<'a>> {
        match expr {
            Expr::Ref(name) => self.reference(name),
            Expr::InstOut { inst, port, span } => self.inst_out(inst, port, *span),
            Expr::Const {
                width,
                value,
                value_span,
                ..
            } => Some(Rx::Const {
                width: *width,
                value: RawConst {
                    value,
                    value_span: *value_span,
                },
            }),
            Expr::Unary { op, arg, .. } => Some(Rx::Un(*op, Box::new(self.expr(arg)?))),
            Expr::Binary { op, lhs, rhs, span } => {
                let (lhs, rhs) = (self.expr(lhs), self.expr(rhs));
                Some(Rx::Bin {
                    op: *op,
                    lhs: Box::new(lhs?),
                    rhs: Box::new(rhs?),
                    span: *span,
                })
            }
            Expr::Icmp {
                pred,
                lhs,
                rhs,
                span,
            } => {
                let (lhs, rhs) = (self.expr(lhs), self.expr(rhs));
                Some(Rx::Icmp {
                    pred: *pred,
                    lhs: Box::new(lhs?),
                    rhs: Box::new(rhs?),
                    span: *span,
                })
            }
            Expr::Mux {
                cond,
                then,
                els,
                span,
            } => {
                let (cond, then, els) = (self.expr(cond), self.expr(then), self.expr(els));
                Some(Rx::Mux {
                    cond: Box::new(cond?),
                    then: Box::new(then?),
                    els: Box::new(els?),
                    span: *span,
                })
            }
            Expr::Extract {
                arg,
                lo,
                width,
                span,
            } => Some(Rx::Extract {
                arg: Box::new(self.expr(arg)?),
                lo: *lo,
                width: *width,
                span: *span,
            }),
            Expr::Replicate { arg, count, span } => Some(Rx::Replicate {
                arg: Box::new(self.expr(arg)?),
                count: *count,
                span: *span,
            }),
            Expr::Read { mem, addr, span } => {
                let addr = self.expr(addr);
                let m = self.memory(mem)?;
                let decl = self.scope.mems.get(m.index())?;
                Some(Rx::Read {
                    mem: m,
                    data_width: decl.width.value,
                    depth: decl.depth,
                    addr: Box::new(addr?),
                    span: *span,
                })
            }
        }
    }

    fn reference(&mut self, name: &Name) -> Option<RawRx<'a>> {
        let scope = self.scope;
        let found = match scope.lookup(&name.text) {
            Some(Binding::Input(i)) => scope
                .sig
                .inputs
                .get(i.index())
                .map(|p| Rx::Input(i, p.width.value)),
            Some(Binding::Let(i)) => scope.lets.get(i.index()).map(|d| Rx::Let(i, d.width.value)),
            Some(Binding::Reg(i)) => scope.regs.get(i.index()).map(|d| Rx::Reg(i, d.width.value)),
            Some(Binding::Output(o)) => scope
                .sig
                .outputs
                .get(o.index())
                .map(|p| Rx::Output(o, p.width.value)),
            Some(Binding::Clock | Binding::ClockOut) => Some(Rx::Clock(name.span)),
            _ => None,
        };
        if found.is_none() {
            self.unknown(name, "a value");
        }
        found
    }

    fn inst_out(&mut self, inst: &Name, port: &Name, span: Span) -> Option<RawRx<'a>> {
        let Some(Binding::Inst(i)) = self.scope.lookup(&inst.text) else {
            self.unknown(inst, "an instance");
            return None;
        };
        let decl = self.scope.insts.get(i.index())?;
        let Some(sig) = decl.sig else {
            // The `NAME.PORT` cannot resolve: the module of the instance does not.
            self.errors.push(error(
                ErrorCode::E003,
                span,
                format!(
                    "`{}.{}` has no module: `{}` is not a module or an extern",
                    inst.text, port.text, decl.module.text
                ),
            ));
            return None;
        };
        match sig.port(&port.text) {
            Some(PortRef::Output(o)) => sig
                .outputs
                .get(o.index())
                .map(|p| Rx::InstOut(i, o, p.width.value)),
            Some(PortRef::ClockOut) => Some(Rx::Clock(span)),
            _ => {
                self.errors.push(error(
                    ErrorCode::E003,
                    span,
                    format!("`{}` is not an output of `{}`", port.text, inst.text),
                ));
                None
            }
        }
    }
}
