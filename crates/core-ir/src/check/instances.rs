// SPDX-License-Identifier: Apache-2.0
//! Pass 6: `E011` (instance connections) and `E013` (extern `deps`). The pass
//! also returns what it resolved: the `deps` of each extern and the arguments
//! of each instance.

use super::error;
use super::rx::{ConnArg, Ex, ExInst, ExModule};
use super::scope::{PortRef, Sig};
use crate::ast::{Design, Extern, Item};
use crate::diag::{Diagnostic, ErrorCode};
use crate::typed::{Callee, Deps, InputIdx};
use std::collections::{HashMap, HashSet};

/// The arguments of one instance.
pub(super) struct LinkedInst<'r> {
    pub callee: Callee,
    /// By input of the callee. The clock input is not among them.
    pub inputs: Vec<&'r Ex>,
}

pub(super) struct Linked<'r> {
    /// For each extern, its `deps` by output.
    pub extern_deps: Vec<Deps>,
    /// For each module, its instances.
    pub insts: Vec<Vec<LinkedInst<'r>>>,
}

pub(super) fn check<'r>(
    design: &Design,
    externs: &[Sig],
    modules: &'r [ExModule],
) -> Result<Linked<'r>, Diagnostic> {
    let mut errors = Vec::new();
    let units = design.items.iter().filter_map(|item| match item {
        Item::Extern(e) => Some(e),
        Item::Module(_) => None,
    });
    let mut extern_deps = Vec::new();
    for (ext, sig) in units.zip(externs) {
        match deps(sig, ext) {
            Ok(d) => extern_deps.push(d),
            Err(found) => errors.extend(found),
        }
    }
    let mut insts = Vec::new();
    for module in modules {
        let mut linked = Vec::new();
        for inst in &module.insts {
            match connections(inst) {
                Ok(l) => linked.push(l),
                Err(found) => errors.extend(found),
            }
        }
        insts.push(linked);
    }
    match errors.into_iter().min_by_key(|d| d.span) {
        Some(d) => Err(d),
        None => Ok(Linked { extern_deps, insts }),
    }
}

fn deps(sig: &Sig, ext: &Extern) -> Result<Deps, Vec<Diagnostic>> {
    let mut errors = Vec::new();
    let mut by_output: HashMap<usize, Vec<InputIdx>> = HashMap::new();
    for dep in &ext.deps {
        let mut inputs: Vec<InputIdx> = Vec::new();
        let mut listed: HashSet<InputIdx> = HashSet::new();
        for input in &dep.ins {
            match sig.port(&input.text) {
                Some(PortRef::Input(i)) if !listed.insert(i) => errors.push(error(
                    ErrorCode::E013,
                    input.span,
                    format!("`{}` is listed twice", input.text),
                )),
                Some(PortRef::Input(i)) => inputs.push(i),
                _ => errors.push(error(
                    ErrorCode::E013,
                    input.span,
                    format!(
                        "`{}` is not a data input of `{}`",
                        input.text, ext.name.text
                    ),
                )),
            }
        }
        let Some(PortRef::Output(o)) = sig.port(&dep.out.text) else {
            errors.push(error(
                ErrorCode::E013,
                dep.out.span,
                format!("`{}` is not an output of `{}`", dep.out.text, ext.name.text),
            ));
            continue;
        };
        // The typed IR lists the inputs in port order.
        inputs.sort_by_key(|i| i.index());
        if by_output.insert(o.index(), inputs).is_some() {
            errors.push(error(
                ErrorCode::E013,
                dep.out.span,
                format!("`{}` has more than one deps entry", dep.out.text),
            ));
        }
    }
    let mut deps = Vec::new();
    for (i, output) in sig.outputs.iter().enumerate() {
        match by_output.remove(&i) {
            Some(inputs) => deps.push(inputs),
            None => errors.push(error(
                ErrorCode::E013,
                output.port.name.span,
                format!("the output `{}` has no deps entry", output.port.name.text),
            )),
        }
    }
    if errors.is_empty() {
        Ok(deps)
    } else {
        Err(errors)
    }
}

fn connections<'r>(inst: &'r ExInst) -> Result<LinkedInst<'r>, Vec<Diagnostic>> {
    let mut errors = Vec::new();
    let mut data: HashMap<InputIdx, &'r Ex> = HashMap::new();
    let mut clocks = 0usize;
    for conn in &inst.conns {
        // The port name of the second connection is the atom that breaks the
        // rule, so the error is at that name.
        let repeated = || {
            error(
                ErrorCode::E011,
                conn.port.span,
                format!("the input `{}` is connected twice", conn.port.text),
            )
        };
        match &conn.arg {
            ConnArg::Data { input, expr, .. } => {
                if data.insert(*input, expr).is_some() {
                    errors.push(repeated());
                }
            }
            ConnArg::ClockName => {
                clocks += 1;
                if clocks > 1 {
                    errors.push(repeated());
                }
            }
            ConnArg::ClockOther { expr_span, .. } => {
                clocks += 1;
                if clocks > 1 {
                    errors.push(repeated());
                }
                errors.push(error(
                    ErrorCode::E011,
                    *expr_span,
                    format!("the clock input `{}` needs a clock input", conn.port.text),
                ));
            }
        }
    }
    let unconnected = |port: &str| {
        error(
            ErrorCode::E011,
            inst.span,
            format!("`{port}` is not connected"),
        )
    };
    if inst.sig.clock.is_some() && clocks == 0 {
        errors.push(unconnected("the clock"));
    }
    let mut inputs = Vec::new();
    for (i, input) in inst.sig.inputs.iter().enumerate() {
        match data.get(&InputIdx::new(i)) {
            Some(expr) => inputs.push(*expr),
            None => errors.push(unconnected(&input.port.name.text)),
        }
    }
    if errors.is_empty() {
        Ok(LinkedInst {
            callee: inst.callee,
            inputs,
        })
    } else {
        Err(errors)
    }
}
