//! Pass 5 (`E009`): one clock input, no clock output, and no value that reads
//! a clock.

use super::rx::{ExModule, Never, SizedModule};
use super::{error, first_error};
use crate::ast::{Design, Dir, Item, Port, Ty};
use crate::diag::{Diagnostic, ErrorCode};

/// Pass 5. The resolved modules lose their clock reads.
pub(super) fn check<'a>(
    design: &Design,
    modules: Vec<SizedModule<'a>>,
) -> Result<Vec<ExModule<'a>>, Diagnostic> {
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => errors.extend(ports(&m.ports)),
            Item::Extern(e) => errors.extend(ports(&e.ports)),
        }
    }
    let mut checked = Vec::new();
    for module in modules {
        let mut clock = |span| {
            errors.push(error(
                ErrorCode::E009,
                span,
                "a clock is not a value, and a value cannot read it",
            ));
            None::<Never>
        };
        let converted = module.map_exprs(&mut |e| e.map(&mut clock, &mut |_, bits| Some(bits)));
        checked.extend(converted);
    }
    first_error(errors)?;
    Ok(checked)
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
