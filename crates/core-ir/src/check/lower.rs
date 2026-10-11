// SPDX-License-Identifier: Apache-2.0
//! Lowers the modules and the externs of a checked design to the typed core
//! IR. The earlier passes resolved the names, the targets, the arguments, the
//! `deps`, the constants, the declared widths, and the clocks, so no step here
//! can fail.

use super::instances::{Linked, LinkedInst};
use super::rx::{Ex, ExModule};
use super::scope::{DataPort, Env, Scope, Sig};
use super::structure::Structure;
use super::types::{ModuleWidths, Widths};
use crate::ast::{Design, Item};
use std::num::NonZeroU32;

use crate::typed::{self, Deps, Inst, Let, Mem, Module, Port, Reg, Write};

pub(super) fn lower(
    design: &Design,
    env: &Env,
    widths: &Widths,
    scopes: &[Scope],
    resolved: &[ExModule],
    structures: &[Structure],
    linked: &Linked,
) -> (Vec<Module>, Vec<typed::Extern>) {
    let modules = scopes
        .iter()
        .zip(resolved)
        .zip(structures)
        .zip(&linked.insts)
        .zip(&widths.modules)
        .map(|((((scope, rx), structure), insts), widths)| {
            module(scope, widths, rx, structure, insts)
        })
        .collect();
    let externs = design
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Extern(e) => Some(e),
            Item::Module(_) => None,
        })
        .zip(env.externs().iter().zip(&widths.externs))
        .zip(&linked.extern_deps)
        .map(|((ext, (sig, widths)), deps)| typed::Extern {
            name: ext.name.text.clone(),
            inputs: ports(&sig.inputs, &widths.inputs),
            outputs: ports(&sig.outputs, &widths.outputs),
            clock: clock(sig),
            deps: deps.clone(),
            span: ext.span,
        })
        .collect();
    (modules, externs)
}

fn clock(sig: &Sig) -> Option<typed::ClockPort> {
    sig.clock.map(|(position, port)| typed::ClockPort {
        name: port.name.text.clone(),
        position,
    })
}

fn ports(ports: &[DataPort], widths: &[NonZeroU32]) -> Vec<Port> {
    ports
        .iter()
        .zip(widths)
        .map(|(p, &width)| Port {
            name: p.port.name.text.clone(),
            width,
            position: p.position,
        })
        .collect()
}

fn all(exprs: &[&Ex]) -> Vec<typed::Expr> {
    exprs.iter().map(|e| e.finish()).collect()
}

fn module(
    scope: &Scope,
    widths: &ModuleWidths,
    rx: &ExModule,
    structure: &Structure,
    insts: &[LinkedInst],
) -> Module {
    let lets = scope
        .lets
        .iter()
        .zip(&widths.lets)
        .zip(&rx.lets)
        .map(|((d, &width), l)| Let {
            name: d.name.text.clone(),
            width,
            expr: l.expr.finish(),
        })
        .collect();
    let regs = scope
        .regs
        .iter()
        .zip(&widths.regs)
        .zip(&rx.regs)
        .zip(all(&structure.nexts))
        .map(|(((d, &width), r), next)| Reg {
            name: d.name.text.clone(),
            width,
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
        .zip(&widths.mems)
        .zip(&structure.writes)
        .map(|((d, &width), ports)| Mem {
            name: d.name.text.clone(),
            width,
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
        inputs: ports(&scope.sig.inputs, &widths.ports.inputs),
        outputs: ports(&scope.sig.outputs, &widths.ports.outputs),
        clock: clock(scope.sig),
        lets,
        regs,
        mems,
        insts,
        assigns: structure.assigns.iter().map(|a| a.expr.finish()).collect(),
        schedule: Vec::new(),
        deps: Deps::default(),
    }
}
