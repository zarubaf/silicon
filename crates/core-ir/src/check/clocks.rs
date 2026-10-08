//! Pass 5 (`E009`): one clock input, no clock output, and no value that reads
//! a clock.

use super::error;
use super::scope::{Binding, PortRef, Scope, visit};
use crate::ast::{Design, Dir, Expr, Item, Port, Ty};
use crate::diag::{Diagnostic, ErrorCode};

pub(super) fn check(design: &Design, scopes: &[Scope]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => errors.extend(ports(&m.ports)),
            Item::Extern(e) => errors.extend(ports(&e.ports)),
        }
    }
    for scope in scopes {
        errors.extend(reads(scope));
    }
    errors
}

fn ports(ports: &[Port]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let mut clocks = 0usize;
    for port in ports.iter().filter(|p| p.ty == Ty::Clock) {
        if port.dir == Dir::Output {
            errors.push(error(
                ErrorCode::E009,
                port.span,
                "a clock cannot be an output",
            ));
            continue;
        }
        clocks += 1;
        if clocks > 1 {
            errors.push(error(
                ErrorCode::E009,
                port.span,
                "a unit has at most one clock input",
            ));
        }
    }
    errors
}

/// The values that read a clock input, a clock output, or a clock output of
/// an instance.
fn reads(scope: &Scope) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for root in scope.value_exprs() {
        visit(root, &mut |e| match e {
            Expr::Ref(name)
                if matches!(
                    scope.lookup(&name.text),
                    Some(Binding::Clock | Binding::ClockOut)
                ) =>
            {
                errors.push(error(
                    ErrorCode::E009,
                    name.span,
                    format!("`{}` is a clock, and a value cannot read it", name.text),
                ));
            }
            Expr::InstOut { inst, port, span }
                if reads_clock_output(scope, &inst.text, &port.text) =>
            {
                errors.push(error(
                    ErrorCode::E009,
                    *span,
                    format!("`{}.{}` is a clock", inst.text, port.text),
                ));
            }
            _ => {}
        });
    }
    errors
}

fn reads_clock_output(scope: &Scope, inst: &str, port: &str) -> bool {
    let Some(Binding::Inst(i)) = scope.lookup(inst) else {
        return false;
    };
    scope
        .insts
        .get(i.index())
        .and_then(|d| d.sig)
        .and_then(|sig| sig.port(port))
        .is_some_and(|p| matches!(p, PortRef::ClockOut))
}
