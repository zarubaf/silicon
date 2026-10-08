//! Pass 6: `E011` (instance connections) and `E013` (extern `deps`). The pass
//! also returns what it resolved: the `deps` of each extern and the arguments
//! of each instance.

use super::error;
use super::scope::{InstDecl, PortRef, Scope, Sig};
use crate::ast::{Conn, Design, Expr, Extern, Item};
use crate::diag::{Diagnostic, ErrorCode};
use crate::typed::{Callee, Deps, InputIdx};

/// The arguments of one instance.
pub(super) struct LinkedInst<'a> {
    pub callee: Callee,
    /// By input of the callee. The clock input is not among them.
    pub inputs: Vec<&'a Expr>,
}

pub(super) struct Linked<'a> {
    /// For each extern, its `deps` by output.
    pub extern_deps: Vec<Deps>,
    /// For each module, its instances.
    pub insts: Vec<Vec<LinkedInst<'a>>>,
}

pub(super) fn check<'a>(
    design: &Design,
    externs: &[Sig],
    scopes: &[Scope<'a>],
) -> Result<Linked<'a>, Diagnostic> {
    let mut errors = Vec::new();
    let units = design.items.iter().filter_map(|item| match item {
        Item::Extern(e) => Some(e),
        Item::Module(_) => None,
    });
    let extern_deps = units
        .zip(externs)
        .map(|(ext, sig)| deps(sig, ext, &mut errors))
        .collect();
    let insts = scopes
        .iter()
        .map(|scope| connections(scope, &mut errors))
        .collect();
    match errors.into_iter().min_by_key(|d| d.span) {
        Some(d) => Err(d),
        None => Ok(Linked { extern_deps, insts }),
    }
}

fn deps(sig: &Sig, ext: &Extern, errors: &mut Vec<Diagnostic>) -> Deps {
    let mut by_output: Vec<Option<Vec<InputIdx>>> = sig.outputs.iter().map(|_| None).collect();
    for dep in &ext.deps {
        let mut inputs: Vec<InputIdx> = Vec::new();
        for input in &dep.ins {
            match sig.port(&input.text) {
                Some(PortRef::Input(i)) if inputs.contains(&i) => errors.push(error(
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
        match by_output.get_mut(o.index()) {
            Some(slot @ None) => *slot = Some(inputs),
            _ => errors.push(error(
                ErrorCode::E013,
                dep.span,
                format!("`{}` has more than one deps entry", dep.out.text),
            )),
        }
    }
    for (output, entry) in sig.outputs.iter().zip(&by_output) {
        if entry.is_none() {
            errors.push(error(
                ErrorCode::E013,
                output.port.span,
                format!("the output `{}` has no deps entry", output.port.name.text),
            ));
        }
    }
    // An output without an entry is an error above, so the result is unused.
    by_output
        .into_iter()
        .map(Option::unwrap_or_default)
        .collect()
}

fn connections<'a>(scope: &Scope<'a>, errors: &mut Vec<Diagnostic>) -> Vec<LinkedInst<'a>> {
    let mut linked = Vec::new();
    for inst in &scope.insts {
        // Pass 3 rejected an unresolved module.
        let (Some(callee), Some(sig)) = (inst.callee, inst.sig) else {
            continue;
        };
        let mut slots: Vec<Option<&'a Expr>> = sig.inputs.iter().map(|_| None).collect();
        let mut clock_connected = false;
        for conn in inst.conns {
            match sig.port(&conn.port.text) {
                Some(PortRef::Input(i)) => match slots.get_mut(i.index()) {
                    Some(slot @ None) => *slot = Some(&conn.expr),
                    _ => errors.push(repeated(conn)),
                },
                Some(PortRef::Clock) => {
                    if std::mem::replace(&mut clock_connected, true) {
                        errors.push(repeated(conn));
                    }
                    if !scope.is_clock_name(&conn.expr) {
                        errors.push(error(
                            ErrorCode::E011,
                            conn.expr.span(),
                            format!("the clock input `{}` needs a clock input", conn.port.text),
                        ));
                    }
                }
                // Pass 3 rejected a port that is not an input.
                _ => {}
            }
        }
        if sig.clock.is_some() && !clock_connected {
            errors.push(unconnected(inst, "the clock"));
        }
        let mut inputs = Vec::new();
        for (input, slot) in sig.inputs.iter().zip(slots) {
            match slot {
                Some(expr) => inputs.push(expr),
                None => errors.push(unconnected(inst, &input.port.name.text)),
            }
        }
        linked.push(LinkedInst { callee, inputs });
    }
    linked
}

fn repeated(conn: &Conn) -> Diagnostic {
    error(
        ErrorCode::E011,
        conn.span,
        format!("the input `{}` is connected twice", conn.port.text),
    )
}

fn unconnected(inst: &InstDecl, port: &str) -> Diagnostic {
    error(
        ErrorCode::E011,
        inst.span,
        format!("`{port}` is not connected"),
    )
}
