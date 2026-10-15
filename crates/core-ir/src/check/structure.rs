// SPDX-License-Identifier: Apache-2.0
//! Pass 8: each register has one `next`, each output has one `assign`, and the
//! write ports of each memory are numbered `0` to `k-1`.

use super::error;
use super::rx::{Ex, ExAssign, ExModule, ExWrite};
use super::scope::Scope;
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed::{MemIdx, OutputIdx, RegIdx};
use std::collections::{HashMap, HashSet};

/// The unique definitions of a module, by table position.
pub(super) struct Structure<'r> {
    pub nexts: Vec<&'r Ex>,
    pub assigns: Vec<&'r ExAssign>,
    /// For each memory, its write ports ordered by port index.
    pub writes: Vec<Vec<&'r ExWrite>>,
}

pub(super) fn check<'r>(
    scopes: &[Scope],
    modules: &'r [ExModule],
) -> Result<Vec<Structure<'r>>, Diagnostic> {
    let mut errors = Vec::new();
    let structures = scopes
        .iter()
        .zip(modules)
        .map(|(scope, module)| structure(scope, module, &mut errors))
        .collect();
    match errors.into_iter().min_by_key(|d| d.span) {
        Some(d) => Err(d),
        None => Ok(structures),
    }
}

/// Groups the definitions by target, in source order.
fn group<K: std::hash::Hash + Eq, T>(items: impl Iterator<Item = (K, T)>) -> HashMap<K, Vec<T>> {
    let mut groups: HashMap<K, Vec<T>> = HashMap::new();
    for (key, item) in items {
        groups.entry(key).or_default().push(item);
    }
    groups
}

/// The one definition of a target. A missing one is an error at `missing`, a
/// second one at its own span.
fn only<'x, T>(
    found: Option<&'x Vec<(Span, T)>>,
    code: ErrorCode,
    missing: (Span, String),
    errors: &mut Vec<Diagnostic>,
) -> Option<&'x T> {
    let Some((first, rest)) = found.and_then(|v| v.split_first()) else {
        errors.push(error(code, missing.0, missing.1));
        return None;
    };
    for (span, _) in rest {
        errors.push(error(code, *span, "the target has a second definition"));
    }
    Some(&first.1)
}

fn structure<'r>(
    scope: &Scope,
    module: &'r ExModule,
    errors: &mut Vec<Diagnostic>,
) -> Structure<'r> {
    let nexts = group(module.nexts.iter().map(|n| (n.slot, (n.span, &n.expr))));
    let assigns = group(module.assigns.iter().map(|a| (a.slot, (a.span, a))));
    let mut next_exprs = Vec::new();
    for (i, reg) in scope.regs.iter().enumerate() {
        let missing = (
            reg.span,
            format!("the register `{}` has no `next`", reg.name.text),
        );
        let found = nexts.get(&RegIdx::new(i));
        next_exprs.extend(only(found, ErrorCode::E006, missing, errors).copied());
    }
    let mut assign_exprs = Vec::new();
    for (i, output) in scope.sig.outputs.iter().enumerate() {
        let name = &output.port.name;
        let missing = (
            output.port.span,
            format!("the output `{}` has no `assign`", name.text),
        );
        let found = assigns.get(&OutputIdx::new(i));
        assign_exprs.extend(only(found, ErrorCode::E007, missing, errors).copied());
    }
    let mut writes = group(module.writes.iter().map(|w| (w.mem, w)));
    let mut ordered = Vec::new();
    for (i, mem) in scope.mems.iter().enumerate() {
        let mut ports = writes.remove(&MemIdx::new(i)).unwrap_or_default();
        let mut repeated = false;
        let mut seen = HashSet::new();
        for w in &ports {
            if !seen.insert(w.port) {
                repeated = true;
                errors.push(error(
                    ErrorCode::E012,
                    w.span,
                    format!("the memory has a second write port {}", w.port),
                ));
            }
        }
        ports.sort_by_key(|w| w.port);
        let dense = (0u32..).zip(&ports).all(|(want, w)| want == w.port);
        if !dense && !repeated {
            errors.push(error(
                ErrorCode::E012,
                mem.span,
                format!("the write ports of `{}` are not 0 to k-1", mem.name.text),
            ));
        }
        ordered.push(ports);
    }
    Structure {
        nexts: next_exprs,
        assigns: assign_exprs,
        writes: ordered,
    }
}
