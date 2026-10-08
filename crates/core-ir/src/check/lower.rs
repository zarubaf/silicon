//! Lowers a checked design to the typed core IR. The earlier passes resolved
//! the names, the targets, the arguments, and the `deps`.

use super::error;
use super::instances::{Linked, LinkedInst};
use super::rx::{Rx, RxModule};
use super::scope::{DataPort, Env, Scope};
use super::structure::Structure;
use crate::ast::{Design, Item};
use crate::diag::{Diagnostic, ErrorCode};
use crate::typed::{self, Callee, Deps, Inst, Let, Mem, Module, Port, Reg, Write};

pub(super) fn lower(
    design: &Design,
    env: &Env,
    scopes: &[Scope],
    resolved: &[RxModule],
    structures: &[Structure],
    linked: &Linked,
) -> Result<typed::Design, Diagnostic> {
    let modules = scopes
        .iter()
        .zip(resolved)
        .zip(structures)
        .zip(&linked.insts)
        .map(|(((scope, rx), structure), insts)| module(scope, rx, structure, insts))
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

fn all(exprs: &[&Rx]) -> Result<Vec<typed::Expr>, Diagnostic> {
    exprs.iter().map(|e| e.finish()).collect()
}

fn module(
    scope: &Scope,
    rx: &RxModule,
    structure: &Structure,
    insts: &[LinkedInst],
) -> Result<Module, Diagnostic> {
    let lets = scope
        .lets
        .iter()
        .zip(&rx.lets)
        .map(|(d, l)| {
            Ok(Let {
                name: d.name.text.clone(),
                width: d.width,
                expr: l.expr.finish()?,
            })
        })
        .collect::<Result<Vec<_>, Diagnostic>>()?;
    let nexts = all(&structure.nexts)?;
    let regs = scope
        .regs
        .iter()
        .zip(&rx.regs)
        .zip(nexts)
        .map(|((d, r), next)| {
            let reset = r
                .reset
                .as_ref()
                .map(|reset| Ok((reset.signal.finish()?, reset.value.finish()?)))
                .transpose()?;
            Ok(Reg {
                name: d.name.text.clone(),
                width: d.width,
                next,
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
                        addr: w.addr.finish()?,
                        data: w.data.finish()?,
                        en: w.en.finish()?,
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
            Ok(Inst {
                name: decl.name.text.clone(),
                callee: linked.callee,
                inputs: all(&linked.inputs)?,
            })
        })
        .collect::<Result<Vec<_>, Diagnostic>>()?;
    Ok(Module {
        name: scope.module.name.text.clone(),
        inputs: ports(&scope.sig.inputs),
        outputs: ports(&scope.sig.outputs),
        has_clock: scope.sig.clock.is_some(),
        lets,
        regs,
        mems,
        insts,
        assigns: all(&structure.assigns)?,
        schedule: Vec::new(),
        deps: Deps::default(),
    })
}
