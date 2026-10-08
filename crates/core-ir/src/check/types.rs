//! Pass 4 (`E005`, declared sizes) and pass 7 (`E004`, operation widths).

use super::rx::{Ex, ExModule, RawConst, RawModule, Rx, SizedModule};
use super::scope::{Scope, Sig, stmt_exprs, visit};
use super::{error, first_error};
use crate::Bits;
use crate::ast::{BinOp, Design, Expr, Item, Num, Stmt};
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed::address_width;
use std::num::NonZeroU32;

/// The largest width of a declared or computed value.
const MAX_WIDTH: u32 = 65536;
/// The largest memory depth.
const MAX_DEPTH: u32 = 16_777_216;

// Pass 4.

/// The checked declared widths of a unit, by table position.
pub(super) struct PortWidths {
    pub inputs: Vec<NonZeroU32>,
    pub outputs: Vec<NonZeroU32>,
}

/// The checked declared widths of a module, by table position.
pub(super) struct ModuleWidths {
    pub ports: PortWidths,
    pub lets: Vec<NonZeroU32>,
    pub regs: Vec<NonZeroU32>,
    pub mems: Vec<NonZeroU32>,
}

/// The checked declared widths of a design.
pub(super) struct Widths {
    /// By module, in item order.
    pub modules: Vec<ModuleWidths>,
    /// By extern, in item order.
    pub externs: Vec<PortWidths>,
}

/// Pass 4. The declared widths become non-zero widths, and the constants of
/// the resolved modules become values.
pub(super) fn declared<'a>(
    design: &Design,
    scopes: &[Scope],
    externs: &[Sig],
    modules: Vec<RawModule<'a>>,
) -> Result<(Vec<SizedModule<'a>>, Widths), Diagnostic> {
    let mut errors = sizes(design);
    let externs = externs
        .iter()
        .map(|sig| port_widths(sig, &mut errors))
        .collect();
    let modules_widths = scopes
        .iter()
        .map(|scope| ModuleWidths {
            ports: port_widths(scope.sig, &mut errors),
            lets: widths(scope.lets.iter().map(|d| d.width), "the width", &mut errors),
            regs: widths(scope.regs.iter().map(|d| d.width), "the width", &mut errors),
            mems: widths(
                scope.mems.iter().map(|d| d.width),
                "the memory width",
                &mut errors,
            ),
        })
        .collect();
    let mut sized = Vec::new();
    for module in modules {
        let mut constant = |width, raw: RawConst| match const_bits(width, &raw) {
            Ok(bits) => Some(bits),
            Err(d) => {
                errors.push(d);
                None
            }
        };
        let converted = module.map_exprs(&mut |e| e.map(&mut Some, &mut constant));
        sized.extend(converted);
    }
    first_error(errors)?;
    let widths = Widths {
        modules: modules_widths,
        externs,
    };
    Ok((sized, widths))
}

fn port_widths(sig: &Sig, errors: &mut Vec<Diagnostic>) -> PortWidths {
    let what = "the port width";
    PortWidths {
        inputs: widths(sig.inputs.iter().map(|p| p.width), what, errors),
        outputs: widths(sig.outputs.iter().map(|p| p.width), what, errors),
    }
}

/// The checked widths. Each width that fails adds its error and has no
/// entry: pass 4 then fails, and nobody reads the widths.
fn widths(
    nums: impl Iterator<Item = Num>,
    what: &str,
    errors: &mut Vec<Diagnostic>,
) -> Vec<NonZeroU32> {
    nums.filter_map(|n| checked_width(n, what).map_err(|d| errors.push(d)).ok())
        .collect()
}

/// The memory depths and the numbers inside the expressions. The widths of
/// the declarations are checked from the scopes.
fn sizes(design: &Design) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for item in &design.items {
        if let Item::Module(m) = item {
            for stmt in &m.stmts {
                stmt_sizes(stmt, &mut errors);
            }
        }
    }
    errors
}

/// A declared width is 1 to 65536.
fn checked_width(n: Num, what: &str) -> Result<NonZeroU32, Diagnostic> {
    NonZeroU32::new(n.value)
        .filter(|w| w.get() <= MAX_WIDTH)
        .ok_or_else(|| {
            error(
                ErrorCode::E005,
                n.span,
                format!("{what} is {}, and a width is 1 to {MAX_WIDTH}", n.value),
            )
        })
}

/// The value of a `const` form. Pass 4 checks each constant here only. `E005`
/// is the error for a width outside 1 to 65536, at the width, and for a value
/// that does not fit, at the value.
fn const_bits(width: Num, raw: &RawConst) -> Result<Bits, Diagnostic> {
    let w = checked_width(width, "the constant width")?;
    Bits::new(w.get(), raw.value.clone()).ok_or_else(|| {
        error(
            ErrorCode::E005,
            raw.value_span,
            format!(
                "the constant {} does not fit in {} bits",
                raw.value, width.value
            ),
        )
    })
}

fn stmt_sizes(stmt: &Stmt, errors: &mut Vec<Diagnostic>) {
    if let Stmt::Mem { depth, .. } = stmt
        && !(1..=MAX_DEPTH).contains(&depth.value)
    {
        errors.push(error(
            ErrorCode::E005,
            depth.span,
            format!("the memory depth {} is not 1 to {MAX_DEPTH}", depth.value),
        ));
    }
    for root in stmt_exprs(stmt) {
        visit(root, &mut |e| expr_sizes(e, errors));
    }
}

fn expr_sizes(expr: &Expr, errors: &mut Vec<Diagnostic>) {
    match expr {
        Expr::Replicate { count, .. } if count.value == 0 => {
            errors.push(error(
                ErrorCode::E005,
                count.span,
                "the replication count is 0",
            ));
        }
        Expr::Extract { width: w, .. } if w.value == 0 => {
            errors.push(error(ErrorCode::E005, w.span, "the extracted width is 0"));
        }
        _ => {}
    }
}

// Pass 7.

pub(super) fn operations(modules: &[ExModule]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for module in modules {
        for form in module.forms() {
            for o in &form.operands {
                let got = width(o.expr, &mut errors);
                if let (Some(got), Some(want)) = (got, o.want)
                    && got != want
                {
                    errors.push(error(
                        ErrorCode::E004,
                        form.span,
                        format!("{} has the width {want}, but its value has {got}", o.what),
                    ));
                }
            }
        }
    }
    errors
}

fn fail(errors: &mut Vec<Diagnostic>, span: Span, message: impl Into<String>) {
    errors.push(error(ErrorCode::E004, span, message));
}

fn equal(errors: &mut Vec<Diagnostic>, l: u32, r: u32, span: Span) -> bool {
    if l != r {
        fail(
            errors,
            span,
            format!("the operand widths {l} and {r} differ"),
        );
    }
    l == r
}

/// The width of an expression. An error in an operand gives `None`: the
/// operand is reported, and its parent has no width to check.
fn width(expr: &Ex, errors: &mut Vec<Diagnostic>) -> Option<u32> {
    match expr {
        Rx::Input(_, w) | Rx::Let(_, w) | Rx::Reg(_, w) | Rx::InstOut(_, _, w) => Some(*w),
        Rx::Clock(never) => match *never {},
        Rx::Const { width, .. } => Some(width.value),
        Rx::Un(_, arg) => width(arg, errors),
        Rx::Bin {
            op, lhs, rhs, span, ..
        } => {
            let (l, r) = (width(lhs, errors), width(rhs, errors));
            let (l, r) = (l?, r?);
            if *op == BinOp::Concat {
                let sum = l.saturating_add(r);
                if sum > MAX_WIDTH {
                    fail(
                        errors,
                        *span,
                        format!("the concatenation has the width {sum}"),
                    );
                    return None;
                }
                return Some(sum);
            }
            equal(errors, l, r, *span).then_some(l)
        }
        Rx::Icmp { lhs, rhs, span, .. } => {
            let (l, r) = (width(lhs, errors), width(rhs, errors));
            equal(errors, l?, r?, *span).then_some(1)
        }
        Rx::Mux {
            cond,
            then,
            els,
            span,
        } => {
            let (c, t, e) = (width(cond, errors), width(then, errors), width(els, errors));
            let (c, t, e) = (c?, t?, e?);
            if c != 1 {
                fail(
                    errors,
                    *span,
                    format!("the condition has the width {c}, not 1"),
                );
                return None;
            }
            equal(errors, t, e, *span).then_some(t)
        }
        Rx::Extract {
            arg,
            lo,
            width: n,
            span,
        } => {
            let w = width(arg, errors)?;
            let end = u64::from(*lo) + u64::from(n.value);
            if end > u64::from(w) {
                fail(
                    errors,
                    *span,
                    format!("the bits {lo} to {end} are outside {w} bits"),
                );
                return None;
            }
            Some(n.value)
        }
        Rx::Replicate { arg, count, span } => {
            let w = width(arg, errors)?;
            let total = u64::from(w) * u64::from(count.value);
            if total > u64::from(MAX_WIDTH) {
                fail(
                    errors,
                    *span,
                    format!("the replication has the width {total}"),
                );
                return None;
            }
            u32::try_from(total).ok()
        }
        Rx::Read {
            data_width,
            depth,
            addr,
            span,
            ..
        } => {
            let a = width(addr, errors)?;
            let want = address_width(*depth);
            if a != want {
                fail(
                    errors,
                    *span,
                    format!("the address has the width {a}, but the memory needs {want}"),
                );
                return None;
            }
            Some(*data_width)
        }
    }
}
