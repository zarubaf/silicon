//! The `.sil` text format: parser, printer, and canonical form.

mod lexer;
mod parser;
mod print;

use crate::Pred;
use crate::ast::{BinOp, Design, Item, Name, Stmt, UnOp};
use crate::diag::Diagnostic;

pub use parser::parse;
pub use print::print;

/// Keywords that structure the grammar. A name never equals one of them.
const STRUCTURE_KEYWORDS: [&str; 22] = [
    "design",
    "module",
    "extern",
    "input",
    "output",
    "deps",
    "let",
    "reg",
    "next",
    "mem",
    "write",
    "inst",
    "assign",
    "reset",
    "sync",
    "const",
    "icmp",
    "mux",
    "extract",
    "replicate",
    "read",
    "clock",
];

const UNOPS: [UnOp; 1] = [UnOp::Not];

const BINOPS: [BinOp; 10] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::Shru,
    BinOp::Shrs,
    BinOp::Concat,
];

const PREDS: [Pred; 10] = [
    Pred::Eq,
    Pred::Ne,
    Pred::Ult,
    Pred::Ule,
    Pred::Ugt,
    Pred::Uge,
    Pred::Slt,
    Pred::Sle,
    Pred::Sgt,
    Pred::Sge,
];

// The matches are exhaustive: a new operator without a keyword does not compile.
fn unop_keyword(op: UnOp) -> &'static str {
    match op {
        UnOp::Not => "not",
    }
}

fn binop_keyword(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::Shru => "shru",
        BinOp::Shrs => "shrs",
        BinOp::Concat => "concat",
    }
}

fn pred_keyword(pred: Pred) -> &'static str {
    match pred {
        Pred::Eq => "eq",
        Pred::Ne => "ne",
        Pred::Ult => "ult",
        Pred::Ule => "ule",
        Pred::Ugt => "ugt",
        Pred::Uge => "uge",
        Pred::Slt => "slt",
        Pred::Sle => "sle",
        Pred::Sgt => "sgt",
        Pred::Sge => "sge",
    }
}

/// `bits` is a keyword only inside a type, but a name never equals it either.
const TYPE_KEYWORD: &str = "bits";

fn is_keyword(text: &str) -> bool {
    STRUCTURE_KEYWORDS.contains(&text)
        || text == TYPE_KEYWORD
        || UNOPS.iter().any(|op| unop_keyword(*op) == text)
        || BINOPS.iter().any(|op| binop_keyword(*op) == text)
        || PREDS.iter().any(|p| pred_keyword(*p) == text)
}

/// The position of a statement in canonical order (spec section 3.3):
/// the kind, then the name, then the write port index.
fn stmt_key(stmt: &Stmt) -> (u8, &str, u32) {
    match stmt {
        Stmt::Reg { name, .. } => (0, &name.text, 0),
        Stmt::Mem { name, .. } => (1, &name.text, 0),
        Stmt::Inst { name, .. } => (2, &name.text, 0),
        Stmt::Let { name, .. } => (3, &name.text, 0),
        Stmt::Next { reg, .. } => (4, &reg.text, 0),
        Stmt::Write { mem, port, .. } => (5, &mem.text, *port),
        Stmt::Assign { out, .. } => (6, &out.text, 0),
    }
}

fn item_name(item: &Item) -> &Name {
    match item {
        Item::Module(m) => &m.name,
        Item::Extern(e) => &e.name,
    }
}

/// Sorts the items by name and the statements by kind, then name or port.
/// The sorts are stable, so equal keys keep their order.
#[must_use]
pub fn canonicalize(design: &Design) -> Design {
    let mut out = design.clone();
    out.items
        .sort_by(|a, b| item_name(a).text.cmp(&item_name(b).text));
    for item in &mut out.items {
        if let Item::Module(m) = item {
            m.stmts.sort_by(|a, b| stmt_key(a).cmp(&stmt_key(b)));
        }
    }
    out
}

fn syntax_error(span: crate::diag::Span, message: String) -> Diagnostic {
    Diagnostic {
        code: crate::diag::ErrorCode::E001,
        span,
        message,
    }
}
