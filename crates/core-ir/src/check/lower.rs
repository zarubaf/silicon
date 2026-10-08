//! Lowers a checked design to the typed core IR. The earlier passes resolved
//! the names, the targets, the arguments, the `deps`, the constants, and the
//! clocks, so no step here can fail.

use super::instances::{Linked, LinkedInst};
use super::rx::{Ex, ExModule};
use super::scope::{DataPort, Env, Scope};
use super::structure::Structure;
use crate::ast::{Design, Item};
use crate::typed::{self, Deps, Inst, Let, Mem, ModIdx, Module, Port, Reg, Write};

pub(super) fn lower(
    design: &Design,
    env: &Env,
    top: ModIdx,
    scopes: &[Scope],
    resolved: &[ExModule],
    structures: &[Structure],
    linked: &Linked,
) -> typed::Design {
    let modules = scopes
        .iter()
        .zip(resolved)
        .zip(structures)
        .zip(&linked.insts)
        .map(|(((scope, rx), structure), insts)| module(scope, rx, structure, insts))
        .collect();
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
    typed::Design {
        modules,
        externs,
        top,
    }
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

fn all(exprs: &[&Ex]) -> Vec<typed::Expr> {
    exprs.iter().map(|e| e.finish()).collect()
}

fn module(scope: &Scope, rx: &ExModule, structure: &Structure, insts: &[LinkedInst]) -> Module {
    let lets = scope
        .lets
        .iter()
        .zip(&rx.lets)
        .map(|(d, l)| Let {
            name: d.name.text.clone(),
            width: d.width,
            expr: l.expr.finish(),
        })
        .collect();
    let regs = scope
        .regs
        .iter()
        .zip(&rx.regs)
        .zip(all(&structure.nexts))
        .map(|((d, r), next)| Reg {
            name: d.name.text.clone(),
            width: d.width,
            next,
            reset: r
                .reset
                .as_ref()
                .map(|reset| (reset.signal.finish(), reset.value.finish())),
        })
        .collect();
    let mems = scope
        .mems
        .iter()
        .zip(&structure.writes)
        .map(|(d, ports)| Mem {
            name: d.name.text.clone(),
            width: d.width,
            depth: d.depth,
            writes: ports
                .iter()
                .map(|w| Write {
                    addr: w.addr.finish(),
                    data: w.data.finish(),
                    en: w.en.finish(),
                })
                .collect(),
        })
        .collect();
    let insts = scope
        .insts
        .iter()
        .zip(insts)
        .map(|(decl, linked)| Inst {
            name: decl.name.text.clone(),
            callee: linked.callee,
            inputs: all(&linked.inputs),
        })
        .collect();
    Module {
        name: scope.module.name.text.clone(),
        inputs: ports(&scope.sig.inputs),
        outputs: ports(&scope.sig.outputs),
        has_clock: scope.sig.clock.is_some(),
        lets,
        regs,
        mems,
        insts,
        assigns: all(&structure.assigns),
        schedule: Vec::new(),
        deps: Deps::default(),
    }
}
