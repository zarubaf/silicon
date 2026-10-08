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

const UNOPS: [(&str, UnOp); 1] = [("not", UnOp::Not)];

const BINOPS: [(&str, BinOp); 10] = [
    ("add", BinOp::Add),
    ("sub", BinOp::Sub),
    ("mul", BinOp::Mul),
    ("and", BinOp::And),
    ("or", BinOp::Or),
    ("xor", BinOp::Xor),
    ("shl", BinOp::Shl),
    ("shru", BinOp::Shru),
    ("shrs", BinOp::Shrs),
    ("concat", BinOp::Concat),
];

const PREDS: [(&str, Pred); 10] = [
    ("eq", Pred::Eq),
    ("ne", Pred::Ne),
    ("ult", Pred::Ult),
    ("ule", Pred::Ule),
    ("ugt", Pred::Ugt),
    ("uge", Pred::Uge),
    ("slt", Pred::Slt),
    ("sle", Pred::Sle),
    ("sgt", Pred::Sgt),
    ("sge", Pred::Sge),
];

/// `bits` is a keyword only inside a type, but a name never equals it either.
const TYPE_KEYWORD: &str = "bits";

fn is_keyword(text: &str) -> bool {
    STRUCTURE_KEYWORDS.contains(&text)
        || text == TYPE_KEYWORD
        || UNOPS.iter().any(|(k, _)| *k == text)
        || BINOPS.iter().any(|(k, _)| *k == text)
        || PREDS.iter().any(|(k, _)| *k == text)
}

fn keyword_of<T: Copy + PartialEq>(table: &[(&'static str, T)], value: T) -> Option<&'static str> {
    table.iter().find(|(_, v)| *v == value).map(|(k, _)| *k)
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
