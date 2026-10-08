//! Pass 5 (`E009`): one clock input, no clock output, registers and memories
//! on the clock, and no value that reads a clock.

use super::error;
use super::scope::{Binding, Env, Scope, visit};
use crate::ast::{Design, Dir, Expr, Item, Port, Ty};
use crate::diag::{Diagnostic, ErrorCode};

pub(super) fn check(design: &Design, env: &Env, scopes: &[Scope]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => errors.extend(ports(&m.ports)),
            Item::Extern(e) => errors.extend(ports(&e.ports)),
        }
    }
    for scope in scopes {
        errors.extend(module(env, scope));
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

fn module(env: &Env, scope: &Scope) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let on_clock = |clk: &str| matches!(scope.lookup(clk), Some(Binding::Clock));
    for reg in &scope.regs {
        if !on_clock(&reg.clk.text) {
            errors.push(error(
                ErrorCode::E009,
                reg.span,
                format!(
                    "the register `{}` does not name the clock input",
                    reg.name.text
                ),
            ));
        }
    }
    for mem in &scope.mems {
        if !on_clock(&mem.clk.text) {
            errors.push(error(
                ErrorCode::E009,
                mem.span,
                format!(
                    "the memory `{}` does not name the clock input",
                    mem.name.text
                ),
            ));
        }
    }
    for root in scope.value_exprs(env) {
        visit(root, &mut |e| {
            if let Expr::Ref(name) = e
                && matches!(
                    scope.lookup(&name.text),
                    Some(Binding::Clock | Binding::Stray)
                )
            {
                errors.push(error(
                    ErrorCode::E009,
                    name.span,
                    format!("`{}` is a clock, and a value cannot read it", name.text),
                ));
            }
        });
    }
    errors
}
