//! Pass 6: `E011` (instance connections) and `E013` (extern `deps`).

use super::error;
use super::scope::{Binding, Env, PortRef, Scope};
use crate::ast::{Design, Expr, Extern, Item};
use crate::diag::{Diagnostic, ErrorCode};
use std::collections::HashSet;

pub(super) fn check(design: &Design, env: &Env, scopes: &[Scope]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let externs = design.items.iter().filter_map(|item| match item {
        Item::Extern(e) => Some(e),
        Item::Module(_) => None,
    });
    for (i, ext) in (0u32..).zip(externs) {
        errors.extend(deps(env, i, ext));
    }
    for scope in scopes {
        errors.extend(connections(env, scope));
    }
    errors
}

fn deps(env: &Env, index: u32, ext: &Extern) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let Some(sig) = env.extern_sig(crate::typed::ExternIdx::new(index)) else {
        return errors;
    };
    let mut declared = HashSet::new();
    for dep in &ext.deps {
        let output = matches!(sig.port(&dep.out.text), Some(PortRef::Output(_)));
        if !output {
            errors.push(error(
                ErrorCode::E013,
                dep.span,
                format!("`{}` is not an output of `{}`", dep.out.text, ext.name.text),
            ));
        } else if !declared.insert(dep.out.text.as_str()) {
            errors.push(error(
                ErrorCode::E013,
                dep.span,
                format!("`{}` has more than one deps entry", dep.out.text),
            ));
        }
        for input in &dep.ins {
            if !matches!(sig.port(&input.text), Some(PortRef::Input(_))) {
                errors.push(error(
                    ErrorCode::E013,
                    dep.span,
                    format!(
                        "`{}` is not a data input of `{}`",
                        input.text, ext.name.text
                    ),
                ));
            }
        }
    }
    for output in &sig.outputs {
        if !declared.contains(output.port.name.text.as_str()) {
            errors.push(error(
                ErrorCode::E013,
                output.port.span,
                format!("the output `{}` has no deps entry", output.port.name.text),
            ));
        }
    }
    errors
}

fn connections(env: &Env, scope: &Scope) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for inst in &scope.insts {
        // Pass 3 rejected an unresolved module.
        let Some(sig) = inst.callee.and_then(|c| env.sig(c)) else {
            continue;
        };
        let mut connected = HashSet::new();
        for conn in inst.conns {
            let port = sig.port(&conn.port.text);
            if !matches!(port, Some(PortRef::Input(_) | PortRef::Clock)) {
                errors.push(error(
                    ErrorCode::E011,
                    conn.span,
                    format!(
                        "`{}` is not an input of `{}`",
                        conn.port.text, inst.module.text
                    ),
                ));
                continue;
            }
            if !connected.insert(conn.port.text.as_str()) {
                errors.push(error(
                    ErrorCode::E011,
                    conn.span,
                    format!("the input `{}` is connected twice", conn.port.text),
                ));
            }
            if matches!(port, Some(PortRef::Clock)) {
                let is_clock = matches!(
                    &conn.expr,
                    Expr::Ref(name) if matches!(scope.lookup(&name.text), Some(Binding::Clock))
                );
                if !is_clock {
                    errors.push(error(
                        ErrorCode::E011,
                        conn.span,
                        format!("the clock input `{}` needs a clock", conn.port.text),
                    ));
                }
            }
        }
        let inputs = sig.inputs.iter().map(|p| p.port).chain(sig.clock);
        for input in inputs {
            if !connected.contains(input.name.text.as_str()) {
                errors.push(error(
                    ErrorCode::E011,
                    inst.span,
                    format!("the input `{}` is not connected", input.name.text),
                ));
            }
        }
    }
    errors
}
