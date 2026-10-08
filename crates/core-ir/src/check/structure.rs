//! Pass 8: each register has one `next`, each output has one `assign`, and the
//! write ports of each memory are numbered `0` to `k-1`.

use super::error;
use super::scope::{Binding, DataPort, Scope};
use crate::ast::{Expr, Stmt};
use crate::diag::{Diagnostic, ErrorCode, Span};

/// The operands of one write port.
pub(super) struct WritePort<'a> {
    pub addr: &'a Expr,
    pub data: &'a Expr,
    pub en: &'a Expr,
}

/// The unique definitions of a module, by table position.
pub(super) struct Structure<'a> {
    pub nexts: Vec<&'a Expr>,
    pub assigns: Vec<&'a Expr>,
    /// For each memory, its write ports ordered by port index.
    pub writes: Vec<Vec<WritePort<'a>>>,
}

pub(super) fn check<'a>(scopes: &[Scope<'a>]) -> Result<Vec<Structure<'a>>, Diagnostic> {
    let mut errors = Vec::new();
    let mut structures = Vec::new();
    for scope in scopes {
        structures.push(module(scope, &mut errors));
    }
    match errors.into_iter().min_by_key(|d| d.span) {
        Some(d) => Err(d),
        None => Ok(structures),
    }
}

/// Adds `item` to the slot at `index` and reports a slot that already held an
/// item. Pass 3 rejected a target of the wrong kind, so `index` is `None` only
/// for a design that already failed.
fn define<T>(
    slots: &mut [Vec<T>],
    index: Option<usize>,
    item: T,
    repeated: (ErrorCode, Span, &str),
    errors: &mut Vec<Diagnostic>,
) {
    let (code, span, message) = repeated;
    if let Some(slot) = index.and_then(|i| slots.get_mut(i)) {
        if !slot.is_empty() {
            errors.push(error(code, span, message));
        }
        slot.push(item);
    }
}

fn module<'a>(scope: &Scope<'a>, errors: &mut Vec<Diagnostic>) -> Structure<'a> {
    let mut nexts: Vec<Vec<&'a Expr>> = scope.regs.iter().map(|_| Vec::new()).collect();
    let outputs = &scope.sig.outputs;
    let mut assigns: Vec<Vec<&'a Expr>> = outputs.iter().map(|_| Vec::new()).collect();
    let mut writes: Vec<Vec<(u32, WritePort<'a>)>> =
        scope.mems.iter().map(|_| Vec::new()).collect();
    for stmt in &scope.module.stmts {
        match stmt {
            Stmt::Next { reg, expr, span } => {
                let target = match scope.lookup(&reg.text) {
                    Some(Binding::Reg(i)) => Some(i.index()),
                    _ => None,
                };
                let repeated = (ErrorCode::E006, *span, "the register has a second `next`");
                define(&mut nexts, target, expr, repeated, errors);
            }
            Stmt::Assign { out, expr, span } => {
                let target = match scope.lookup(&out.text) {
                    Some(Binding::Output(o)) => Some(o.index()),
                    _ => None,
                };
                let repeated = (ErrorCode::E007, *span, "the output has a second `assign`");
                define(&mut assigns, target, expr, repeated, errors);
            }
            Stmt::Write {
                mem,
                port,
                addr,
                data,
                en,
                span,
            } => {
                if let Some(Binding::Mem(i)) = scope.lookup(&mem.text)
                    && let Some(slot) = writes.get_mut(i.index())
                {
                    if slot.iter().any(|(p, _)| p == port) {
                        errors.push(error(
                            ErrorCode::E012,
                            *span,
                            format!("the memory has a second write port {port}"),
                        ));
                    }
                    slot.push((*port, WritePort { addr, data, en }));
                }
            }
            _ => {}
        }
    }
    missing(scope, outputs, (&nexts, &assigns), errors);
    let writes = order_writes(scope, writes, errors);
    Structure {
        nexts: nexts
            .into_iter()
            .filter_map(|s| s.into_iter().next())
            .collect(),
        assigns: assigns
            .into_iter()
            .filter_map(|s| s.into_iter().next())
            .collect(),
        writes,
    }
}

/// Reports each register without `next` and each output without `assign`.
fn missing(
    scope: &Scope,
    outputs: &[DataPort],
    (nexts, assigns): (&[Vec<&Expr>], &[Vec<&Expr>]),
    errors: &mut Vec<Diagnostic>,
) {
    for (decl, slot) in scope.regs.iter().zip(nexts) {
        if slot.is_empty() {
            errors.push(error(
                ErrorCode::E006,
                decl.span,
                format!("the register `{}` has no `next`", decl.name.text),
            ));
        }
    }
    for (port, slot) in outputs.iter().zip(assigns) {
        if slot.is_empty() {
            errors.push(error(
                ErrorCode::E007,
                port.port.span,
                format!("the output `{}` has no `assign`", port.port.name.text),
            ));
        }
    }
}

/// Orders the write ports of each memory by index. A repeated index was
/// reported at the second write; otherwise a gap is reported at the memory.
fn order_writes<'a>(
    scope: &Scope,
    writes: Vec<Vec<(u32, WritePort<'a>)>>,
    errors: &mut Vec<Diagnostic>,
) -> Vec<Vec<WritePort<'a>>> {
    let mut ordered = Vec::new();
    for (decl, mut slot) in scope.mems.iter().zip(writes) {
        slot.sort_by_key(|(port, _)| *port);
        let dense = (0u32..).zip(&slot).all(|(want, (port, _))| want == *port);
        let repeated = slot
            .windows(2)
            .any(|w| matches!(w, [(a, _), (b, _)] if a == b));
        if !dense && !repeated {
            errors.push(error(
                ErrorCode::E012,
                decl.span,
                format!("the write ports of `{}` are not 0 to k-1", decl.name.text),
            ));
        }
        ordered.push(slot.into_iter().map(|(_, w)| w).collect());
    }
    ordered
}
