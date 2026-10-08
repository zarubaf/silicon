//! Pass 5 (`E009`): one clock input, no clock output, and no value that reads
//! a clock.

use super::error;
use super::rx::RxModule;
use crate::ast::{Design, Dir, Item, Port, Ty};
use crate::diag::{Diagnostic, ErrorCode};

pub(super) fn check(design: &Design, modules: &[RxModule]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => errors.extend(ports(&m.ports)),
            Item::Extern(e) => errors.extend(ports(&e.ports)),
        }
    }
    for module in modules {
        let mut reads = Vec::new();
        for obligation in module.obligations() {
            obligation.expr.clock_reads(&mut reads);
        }
        errors.extend(reads.into_iter().map(|span| {
            error(
                ErrorCode::E009,
                span,
                "a clock is not a value, and a value cannot read it",
            )
        }));
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
