//! Lowers a checked design to the typed core IR. Every lookup here succeeded
//! in an earlier pass; a lookup that fails reports the error of that pass.

use super::error;
use super::scope::{Binding, Env, PortRef, Scope};
use super::structure::Structure;
use crate::Bits;
use crate::ast::{self, Design, Item};
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed::{self, Deps, ExternIdx, Inst, Let, Mem, Module, Port, Reg, Write};

pub(super) fn lower(
    design: &Design,
    env: &Env,
    scopes: &[Scope],
    structures: &[Structure],
) -> Result<typed::Design, Diagnostic> {
    let modules = scopes
        .iter()
        .zip(structures)
        .map(|(scope, structure)| Lowerer { env, scope }.module(structure))
        .collect::<Result<Vec<_>, _>>()?;
    let externs = design
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Extern(e) => Some(e),
            Item::Module(_) => None,
        })
        .zip(0usize..)
        .map(|(ext, i)| lower_extern(env, ExternIdx::new(i), ext))
        .collect::<Result<Vec<_>, _>>()?;
    let top = scopes
        .iter()
        .find(|s| s.module.name.text == design.top.text)
        .map(|s| s.index)
        .ok_or_else(|| error(ErrorCode::E003, design.top.span, "the top is not a module"))?;
    Ok(typed::Design {
        modules,
        externs,
        top,
    })
}

fn ports(ports: &[super::scope::DataPort]) -> Vec<Port> {
    ports
        .iter()
        .map(|p| Port {
            name: p.port.name.text.clone(),
            width: p.width,
        })
        .collect()
}

fn missing_sig(span: Span) -> Diagnostic {
    error(ErrorCode::E003, span, "the unit has no interface")
}

fn lower_extern(
    env: &Env,
    index: ExternIdx,
    ext: &ast::Extern,
) -> Result<typed::Extern, Diagnostic> {
    let sig = env.extern_sig(index).ok_or_else(|| missing_sig(ext.span))?;
    let deps = sig
        .outputs
        .iter()
        .map(|output| {
            let dep = ext
                .deps
                .iter()
                .find(|d| d.out.text == output.port.name.text)
                .ok_or_else(|| {
                    error(
                        ErrorCode::E013,
                        output.port.span,
                        "the output has no deps entry",
                    )
                })?;
            let mut ins = Vec::new();
            for input in &dep.ins {
                let Some(PortRef::Input(i)) = sig.port(&input.text) else {
                    return Err(error(
                        ErrorCode::E013,
                        dep.span,
                        "the dependency is not an input",
                    ));
                };
                if !ins.contains(&i) {
                    ins.push(i);
                }
            }
            Ok(ins)
        })
        .collect::<Result<Deps, Diagnostic>>()?;
    Ok(typed::Extern {
        name: ext.name.text.clone(),
        inputs: ports(&sig.inputs),
        outputs: ports(&sig.outputs),
        deps,
    })
}

struct Lowerer<'e, 'a> {
    env: &'e Env<'a>,
    scope: &'e Scope<'a>,
}

impl Lowerer<'_, '_> {
    fn module(&self, structure: &Structure) -> Result<Module, Diagnostic> {
        let scope = self.scope;
        let sig = self
            .env
            .module_sig(scope.index)
            .ok_or_else(|| missing_sig(scope.module.span))?;
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
            .map(|d| self.inst(d))
            .collect::<Result<Vec<_>, _>>()?;
        let assigns = structure
            .assigns
            .iter()
            .map(|e| self.expr(e))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Module {
            name: scope.module.name.text.clone(),
            inputs: ports(&sig.inputs),
            outputs: ports(&sig.outputs),
            has_clock: sig.clock.is_some(),
            lets,
            regs,
            mems,
            insts,
            assigns,
            schedule: Vec::new(),
            deps: Deps::default(),
        })
    }

    fn inst(&self, decl: &super::scope::InstDecl) -> Result<Inst, Diagnostic> {
        let callee = decl.callee.ok_or_else(|| {
            error(
                ErrorCode::E003,
                decl.module.span,
                "the module does not resolve",
            )
        })?;
        let sig = self.env.sig(callee).ok_or_else(|| missing_sig(decl.span))?;
        let inputs = (0usize..)
            .zip(&sig.inputs)
            .map(|(i, input)| {
                let conn = decl
                    .conns
                    .iter()
                    .find(|c| matches!(sig.port(&c.port.text), Some(PortRef::Input(j)) if j.index() == i))
                    .ok_or_else(|| {
                        error(
                            ErrorCode::E011,
                            decl.span,
                            format!("the input `{}` is not connected", input.port.name.text),
                        )
                    })?;
                self.expr(&conn.expr)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Inst {
            name: decl.name.text.clone(),
            callee,
            inputs,
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
                Some(Binding::Clock | Binding::Stray) => {
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
                let sig = self
                    .scope
                    .insts
                    .get(i.index())
                    .and_then(|d| d.callee)
                    .and_then(|c| self.env.sig(c));
                match sig.and_then(|s| s.port(&port.text)) {
                    Some(PortRef::Output(o)) => T::InstOut(i, o),
                    _ => return Err(error(ErrorCode::E003, *span, "the port is not an output")),
                }
            }
            ast::Expr::Const { width, value, span } => Bits::new(*width, value.clone())
                .map(T::Const)
                .ok_or_else(|| error(ErrorCode::E005, *span, "the constant does not fit"))?,
            ast::Expr::Unary { op, arg, .. } => T::Un(*op, boxed(arg)?),
            ast::Expr::Binary { op, lhs, rhs, .. } => T::Bin(*op, boxed(lhs)?, boxed(rhs)?),
            ast::Expr::Icmp { pred, lhs, rhs, .. } => T::Icmp(*pred, boxed(lhs)?, boxed(rhs)?),
            ast::Expr::Mux {
                cond, then, els, ..
            } => T::Mux(boxed(cond)?, boxed(then)?, boxed(els)?),
            ast::Expr::Extract { arg, lo, width, .. } => T::Extract(boxed(arg)?, *lo, *width),
            ast::Expr::Replicate { arg, count, .. } => T::Replicate(boxed(arg)?, *count),
            ast::Expr::Read { mem, addr, span } => {
                let Some(Binding::Mem(m)) = self.scope.lookup(&mem.text) else {
                    return Err(error(ErrorCode::E003, *span, "the name is not a memory"));
                };
                T::Read(m, boxed(addr)?)
            }
        })
    }
}
