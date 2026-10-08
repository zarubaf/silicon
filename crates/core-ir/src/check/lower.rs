//! Lowers a checked design to the typed core IR. The earlier passes resolved
//! the targets, the arguments, and the `deps`. The name lookups here repeat
//! pass 3 and report its code if one ever fails.

use super::error;
use super::instances::{Linked, LinkedInst};
use super::scope::{Binding, DataPort, Env, PortRef, Scope};
use super::structure::Structure;
use crate::Bits;
use crate::ast::{self, Design, Item};
use crate::diag::{Diagnostic, ErrorCode};
use crate::typed::{self, Callee, Deps, Inst, Let, Mem, Module, Port, Reg, Write};

pub(super) fn lower(
    design: &Design,
    env: &Env,
    scopes: &[Scope],
    structures: &[Structure],
    linked: &Linked,
) -> Result<typed::Design, Diagnostic> {
    let modules = scopes
        .iter()
        .zip(structures)
        .zip(&linked.insts)
        .map(|((scope, structure), insts)| Lowerer { scope }.module(structure, insts))
        .collect::<Result<Vec<_>, _>>()?;
    let externs = design
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Extern(e) => Some(e),
            Item::Module(_) => None,
        })
        .zip(env.externs())
        .zip(&linked.extern_deps)
        .map(|((ext, sig), deps)| typed::Extern {
            name: ext.name.text.clone(),
            inputs: ports(&sig.inputs),
            outputs: ports(&sig.outputs),
            deps: deps.clone(),
        })
        .collect();
    let Some(Callee::Module(top)) = env.callee(&design.top.text) else {
        return Err(error(
            ErrorCode::E003,
            design.top.span,
            "the top is not a module",
        ));
    };
    Ok(typed::Design {
        modules,
        externs,
        top,
    })
}

fn ports(ports: &[DataPort]) -> Vec<Port> {
    ports
        .iter()
        .map(|p| Port {
            name: p.port.name.text.clone(),
            width: p.width,
        })
        .collect()
}

struct Lowerer<'e, 'a> {
    scope: &'e Scope<'a>,
}

impl Lowerer<'_, '_> {
    fn module(&self, structure: &Structure, insts: &[LinkedInst]) -> Result<Module, Diagnostic> {
        let scope = self.scope;
        let lets = scope
            .lets
            .iter()
            .map(|d| {
                Ok(Let {
                    name: d.name.text.clone(),
                    width: d.width,
                    expr: self.expr(d.expr)?,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let regs = scope
            .regs
            .iter()
            .zip(&structure.nexts)
            .map(|(d, next)| {
                let reset = d
                    .reset
                    .map(|r| Ok((self.expr(&r.signal)?, self.expr(&r.value)?)))
                    .transpose()?;
                Ok(Reg {
                    name: d.name.text.clone(),
                    width: d.width,
                    next: self.expr(next)?,
                    reset,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let mems = scope
            .mems
            .iter()
            .zip(&structure.writes)
            .map(|(d, ports)| {
                let writes = ports
                    .iter()
                    .map(|w| {
                        Ok(Write {
                            addr: self.expr(w.addr)?,
                            data: self.expr(w.data)?,
                            en: self.expr(w.en)?,
                        })
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(Mem {
                    name: d.name.text.clone(),
                    width: d.width,
                    depth: d.depth,
                    writes,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let insts = scope
            .insts
            .iter()
            .zip(insts)
            .map(|(decl, linked)| {
                let inputs = linked
                    .inputs
                    .iter()
                    .map(|e| self.expr(e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Inst {
                    name: decl.name.text.clone(),
                    callee: linked.callee,
                    inputs,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let assigns = structure
            .assigns
            .iter()
            .map(|e| self.expr(e))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Module {
            name: scope.module.name.text.clone(),
            inputs: ports(&scope.sig.inputs),
            outputs: ports(&scope.sig.outputs),
            has_clock: scope.sig.clock.is_some(),
            lets,
            regs,
            mems,
            insts,
            assigns,
            schedule: Vec::new(),
            deps: Deps::default(),
        })
    }

    fn expr(&self, expr: &ast::Expr) -> Result<typed::Expr, Diagnostic> {
        use typed::Expr as T;
        let boxed = |e: &ast::Expr| self.expr(e).map(Box::new);
        Ok(match expr {
            ast::Expr::Ref(name) => match self.scope.lookup(&name.text) {
                Some(Binding::Input(i)) => T::Input(i),
                Some(Binding::Let(i)) => T::Let(i),
                Some(Binding::Reg(i)) => T::Reg(i),
                Some(Binding::Clock | Binding::ClockOut) => {
                    return Err(error(ErrorCode::E009, name.span, "a value reads a clock"));
                }
                _ => return Err(error(ErrorCode::E003, name.span, "the name is not a value")),
            },
            ast::Expr::InstOut { inst, port, span } => {
                let Some(Binding::Inst(i)) = self.scope.lookup(&inst.text) else {
                    return Err(error(
                        ErrorCode::E003,
                        inst.span,
                        "the name is not an instance",
                    ));
                };
                let sig = self.scope.insts.get(i.index()).and_then(|d| d.sig);
                match sig.and_then(|s| s.port(&port.text)) {
                    Some(PortRef::Output(o)) => T::InstOut(i, o),
                    _ => return Err(error(ErrorCode::E003, *span, "the port is not an output")),
                }
            }
            ast::Expr::Const {
                width, value, span, ..
            } => Bits::new(width.value, value.clone())
                .map(T::Const)
                .ok_or_else(|| error(ErrorCode::E005, *span, "the constant does not fit"))?,
            ast::Expr::Unary { op, arg, .. } => T::Un(*op, boxed(arg)?),
            ast::Expr::Binary { op, lhs, rhs, .. } => T::Bin(*op, boxed(lhs)?, boxed(rhs)?),
            ast::Expr::Icmp { pred, lhs, rhs, .. } => T::Icmp(*pred, boxed(lhs)?, boxed(rhs)?),
            ast::Expr::Mux {
                cond, then, els, ..
            } => T::Mux(boxed(cond)?, boxed(then)?, boxed(els)?),
            ast::Expr::Extract { arg, lo, width, .. } => T::Extract(boxed(arg)?, *lo, width.value),
            ast::Expr::Replicate { arg, count, .. } => T::Replicate(boxed(arg)?, count.value),
            ast::Expr::Read { mem, addr, span } => {
                let Some(Binding::Mem(m)) = self.scope.lookup(&mem.text) else {
                    return Err(error(ErrorCode::E003, *span, "the name is not a memory"));
                };
                T::Read(m, boxed(addr)?)
            }
        })
    }
}
