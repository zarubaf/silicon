// SPDX-License-Identifier: Apache-2.0
//! The source printer of Lean `Source.Print` (`Expr.print`), for the base of an `@field` in the
//! text "Family as a value" (design section 6.2). The text of an error prints the expression as
//! the source form writes it, not as a slice of the source. It runs once, at the winning error.
//! The evaluator runs on a stack that fits the height of the AST, and the walk recurses over that
//! height only.

use crate::ops::binop_text;
use parse::ast::{Arm, BinOp, Expr, FnParam, Pattern, TypeExpr, UnOp};

/// The level of a postfix form or a primary: the context of a base.
pub(super) const POSTFIX: u8 = 11;

/// The level of a prefix operator and of a function type.
const UNARY: u8 = 10;

/// The text of `e` in a context that needs at least the level `ctx`.
pub(super) fn print(e: &Expr, ctx: u8) -> String {
    let mut out = String::new();
    expr(e, ctx, &mut out);
    out
}

fn binary_level(op: BinOp) -> u8 {
    match op {
        BinOp::Lor => 1,
        BinOp::Land => 2,
        BinOp::Or => 3,
        BinOp::Xor => 4,
        BinOp::And => 5,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 6,
        BinOp::Shl | BinOp::Shr => 7,
        BinOp::Add | BinOp::Sub | BinOp::Addw | BinOp::Subw => 8,
        BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Mulw => 9,
    }
}

fn level(e: &Expr) -> u8 {
    match e {
        Expr::Cond { .. } | Expr::Match { .. } => 0,
        Expr::Binary { op, .. } => binary_level(*op),
        Expr::Unary { .. } | Expr::FnType { .. } => UNARY,
        _ => POSTFIX,
    }
}

/// The elements `xs` separated by a comma and a space.
fn args(xs: &[Expr], out: &mut String) {
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        expr(x, 0, out);
    }
}

#[allow(clippy::too_many_lines)]
fn expr(e: &Expr, ctx: u8, out: &mut String) {
    let paren = level(e) < ctx;
    if paren {
        out.push('(');
    }
    match e {
        Expr::Num { value, .. } => out.push_str(value.as_str()),
        Expr::Bool { value, .. } => out.push_str(if *value { "true" } else { "false" }),
        Expr::Str { value, .. } => parse::quote(value, out),
        Expr::Name { name, .. } => out.push_str(name),
        Expr::Unary { op, arg, .. } => {
            out.push_str(match op {
                UnOp::Not => "!",
                UnOp::Inv => "~",
                UnOp::Neg => "-",
            });
            expr(arg, UNARY, out);
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            let own = binary_level(*op);
            // A comparison is not associative, so neither of its operands is a comparison.
            expr(lhs, if own == 6 { own + 1 } else { own }, out);
            out.push(' ');
            out.push_str(binop_text(*op));
            out.push(' ');
            expr(rhs, own + 1, out);
        }
        Expr::Cond { cond, yes, no, .. } => {
            out.push_str("if (");
            expr(cond, 0, out);
            out.push_str(") { ");
            expr(yes, 0, out);
            out.push_str(" } else { ");
            expr(no, 0, out);
            out.push_str(" }");
        }
        Expr::Call {
            callee, args: xs, ..
        } => {
            // The parser reads `a.f(x)` as a receiver call, so a field callee needs parentheses.
            if matches!(**callee, Expr::Field { .. }) {
                out.push('(');
                expr(callee, 0, out);
                out.push(')');
            } else {
                expr(callee, POSTFIX, out);
            }
            out.push('(');
            args(xs, out);
            out.push(')');
        }
        Expr::Index { base, args: xs, .. } => {
            expr(base, POSTFIX, out);
            out.push('[');
            args(xs, out);
            out.push(']');
        }
        Expr::Method {
            recv,
            name,
            args: xs,
            ..
        } => {
            expr(recv, POSTFIX, out);
            out.push('.');
            out.push_str(&name.name);
            out.push('(');
            args(xs, out);
            out.push(')');
        }
        Expr::Field { base, field, .. } => {
            expr(base, POSTFIX, out);
            out.push('.');
            out.push_str(&field.name);
        }
        Expr::Unit { .. } => out.push_str("()"),
        Expr::Tuple { elems, .. } => {
            out.push('(');
            args(elems, out);
            out.push_str(if elems.len() == 1 { ",)" } else { ")" });
        }
        Expr::Array { elems, .. } => {
            out.push('[');
            args(elems, out);
            out.push(']');
        }
        Expr::Select { base, index, .. } => {
            expr(base, POSTFIX, out);
            out.push('.');
            out.push_str(index.as_str());
        }
        Expr::Path { ty, variant, .. } => {
            out.push_str(&ty.name);
            out.push_str("::");
            out.push_str(&variant.name);
        }
        Expr::Match { scrut, arms, .. } => {
            out.push_str("match (");
            expr(scrut, 0, out);
            out.push_str(") {");
            for a in arms {
                out.push(' ');
                arm(a, out);
                out.push(',');
            }
            out.push_str(" }");
        }
        Expr::Builtin {
            builtin, args: xs, ..
        } => {
            out.push('@');
            out.push_str(builtin.name());
            out.push('(');
            args(xs, out);
            out.push(')');
        }
        Expr::ArrayType { elem, len, .. } => {
            out.push('[');
            type_expr(elem, out);
            out.push_str("; ");
            expr(len, 0, out);
            out.push(']');
        }
        Expr::FnType { params, ret, .. } => fn_type(params, ret, out),
    }
    if paren {
        out.push(')');
    }
}

fn arm(a: &Arm, out: &mut String) {
    match &a.pat {
        Pattern::Wild { .. } => out.push('_'),
        Pattern::Int { neg, value, .. } => {
            if *neg {
                out.push('-');
            }
            out.push_str(value.as_str());
        }
        Pattern::Bool { value, .. } => out.push_str(if *value { "true" } else { "false" }),
        Pattern::Variant {
            ty,
            variant,
            binders,
            ..
        } => {
            out.push_str(&ty.name);
            out.push_str("::");
            out.push_str(&variant.name);
            if !binders.is_empty() {
                out.push('(');
                for (i, b) in binders.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(b.as_ref().map_or("_", |b| b.name.as_str()));
                }
                out.push(')');
            }
        }
    }
    out.push_str(" => ");
    expr(&a.value, 0, out);
}

fn fn_type(params: &[FnParam], ret: &TypeExpr, out: &mut String) {
    out.push_str("fn (");
    for (i, p) in params.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        if p.mutable {
            out.push_str("mut ");
        }
        type_expr(&p.ty, out);
    }
    out.push_str(") -> ");
    type_expr(ret, out);
}

fn type_expr(t: &TypeExpr, out: &mut String) {
    match t {
        TypeExpr::Name { name, .. } => out.push_str(name),
        TypeExpr::Index { base, args: xs, .. } => {
            if matches!(**base, TypeExpr::Fn { .. }) {
                out.push('(');
                type_expr(base, out);
                out.push(')');
            } else {
                type_expr(base, out);
            }
            out.push('[');
            args(xs, out);
            out.push(']');
        }
        TypeExpr::Unit { .. } => out.push_str("()"),
        TypeExpr::Tuple { elems, .. } => {
            out.push('(');
            for (i, x) in elems.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                type_expr(x, out);
            }
            out.push_str(if elems.len() == 1 { ",)" } else { ")" });
        }
        TypeExpr::Array { elem, len, .. } => {
            out.push('[');
            type_expr(elem, out);
            out.push_str("; ");
            expr(len, 0, out);
            out.push(']');
        }
        TypeExpr::Fn { params, ret, .. } => fn_type(params, ret, out),
    }
}
