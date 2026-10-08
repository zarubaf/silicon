//! Prints an AST as `.sil` text. The output keeps the order of the input.

use super::{BINOPS, PREDS, UNOPS, keyword_of};
use crate::ast::{Design, Dir, Expr, Extern, Item, Module, Port, Stmt, Ty};
use std::fmt::Write;

/// Prints with two-space indentation and one port or statement per line.
#[must_use]
pub fn print(design: &Design) -> String {
    let mut out = format!("(design {}", design.top.text);
    for item in &design.items {
        out.push_str("\n  ");
        match item {
            Item::Module(m) => module(&mut out, m),
            Item::Extern(e) => external(&mut out, e),
        }
    }
    out.push_str(")\n");
    out
}

fn module(out: &mut String, m: &Module) {
    let _ = write!(out, "(module {}", m.name.text);
    for p in &m.ports {
        out.push_str("\n    ");
        port(out, p);
    }
    for s in &m.stmts {
        out.push_str("\n    ");
        stmt(out, s);
    }
    out.push(')');
}

fn external(out: &mut String, e: &Extern) {
    let _ = write!(out, "(extern {}", e.name.text);
    for p in &e.ports {
        out.push_str("\n    ");
        port(out, p);
    }
    for d in &e.deps {
        let ins: Vec<&str> = d.ins.iter().map(|n| n.text.as_str()).collect();
        let _ = write!(out, "\n    (deps {} ({}))", d.out.text, ins.join(" "));
    }
    out.push(')');
}

fn port(out: &mut String, p: &Port) {
    let dir = match p.dir {
        Dir::Input => "input",
        Dir::Output => "output",
    };
    let _ = write!(out, "({dir} {} ", p.name.text);
    match p.ty {
        Ty::Clock => out.push_str("clock"),
        Ty::Bits(n) => {
            let _ = write!(out, "(bits {n})");
        }
    }
    out.push(')');
}

fn stmt(out: &mut String, s: &Stmt) {
    match s {
        Stmt::Let {
            name,
            width,
            expr: e,
            ..
        } => {
            let _ = write!(out, "(let {} (bits {width}) ", name.text);
            expr(out, e);
        }
        Stmt::Reg {
            name,
            width,
            clk,
            reset,
            ..
        } => {
            let _ = write!(out, "(reg {} (bits {width}) {}", name.text, clk.text);
            if let Some(r) = reset {
                out.push_str(" (reset sync ");
                expr(out, &r.signal);
                out.push(' ');
                expr(out, &r.value);
                out.push(')');
            }
        }
        Stmt::Next { reg, expr: e, .. } => {
            let _ = write!(out, "(next {} ", reg.text);
            expr(out, e);
        }
        Stmt::Mem {
            name,
            width,
            depth,
            clk,
            ..
        } => {
            let _ = write!(
                out,
                "(mem {} (bits {width}) {depth} {}",
                name.text, clk.text
            );
        }
        Stmt::Write {
            mem,
            port,
            addr,
            data,
            en,
            ..
        } => {
            let _ = write!(out, "(write {} {port} ", mem.text);
            expr(out, addr);
            out.push(' ');
            expr(out, data);
            out.push(' ');
            expr(out, en);
        }
        Stmt::Inst {
            name,
            module,
            conns,
            ..
        } => {
            let _ = write!(out, "(inst {} {}", name.text, module.text);
            for c in conns {
                let _ = write!(out, " ({} ", c.port.text);
                expr(out, &c.expr);
                out.push(')');
            }
        }
        Stmt::Assign {
            out: target,
            expr: e,
            ..
        } => {
            let _ = write!(out, "(assign {} ", target.text);
            expr(out, e);
        }
    }
    out.push(')');
}

fn expr(out: &mut String, e: &Expr) {
    match e {
        Expr::Ref(n) => out.push_str(&n.text),
        Expr::InstOut { inst, port, .. } => {
            let _ = write!(out, "{}.{}", inst.text, port.text);
            return;
        }
        Expr::Const { width, value, .. } => {
            let _ = write!(out, "(const {width} {value}");
        }
        Expr::Unary { op, arg, .. } => {
            let _ = write!(out, "({} ", keyword_of(&UNOPS, *op).unwrap_or_default());
            expr(out, arg);
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            let _ = write!(out, "({} ", keyword_of(&BINOPS, *op).unwrap_or_default());
            expr(out, lhs);
            out.push(' ');
            expr(out, rhs);
        }
        Expr::Icmp { pred, lhs, rhs, .. } => {
            let _ = write!(
                out,
                "(icmp {} ",
                keyword_of(&PREDS, *pred).unwrap_or_default()
            );
            expr(out, lhs);
            out.push(' ');
            expr(out, rhs);
        }
        Expr::Mux {
            cond, then, els, ..
        } => {
            out.push_str("(mux ");
            expr(out, cond);
            out.push(' ');
            expr(out, then);
            out.push(' ');
            expr(out, els);
        }
        Expr::Extract { arg, lo, width, .. } => {
            out.push_str("(extract ");
            expr(out, arg);
            let _ = write!(out, " {lo} {width}");
        }
        Expr::Replicate { arg, count, .. } => {
            out.push_str("(replicate ");
            expr(out, arg);
            let _ = write!(out, " {count}");
        }
        Expr::Read { mem, addr, .. } => {
            let _ = write!(out, "(read {} ", mem.text);
            expr(out, addr);
        }
    }
    if !matches!(e, Expr::Ref(_)) {
        out.push(')');
    }
}
