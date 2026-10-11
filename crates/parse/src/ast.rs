// SPDX-License-Identifier: Apache-2.0
//! The source AST of slice 1. It mirrors `Silicon.Source.Syntax` in Lean: the same types,
//! the same constructors, and the same field order. The Lean name of a constructor is the
//! lowercase name of the variant here, so the AST dump can print both with one rule.

use std::fmt::Write;

/// A position is a line and a column. Both start at 1. A column counts characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

/// A natural number of any size, as its canonical decimal digits: no leading zero.
/// Lean has an unbounded `Nat`, and a source number has no size limit.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nat(String);

impl Nat {
    /// The value of digits in a radix of 2 to 16. The digits must be valid for the radix.
    pub(crate) fn from_digits(digits: &str, radix: u32) -> Nat {
        // Little-endian limbs of base 10^9.
        const BASE: u64 = 1_000_000_000;
        let mut limbs: Vec<u64> = Vec::new();
        for digit in digits.chars().filter_map(|c| c.to_digit(radix)) {
            let mut carry = u64::from(digit);
            for limb in &mut limbs {
                let value = *limb * u64::from(radix) + carry;
                *limb = value % BASE;
                carry = value / BASE;
            }
            if carry > 0 {
                limbs.push(carry);
            }
        }
        let Some((top, rest)) = limbs.split_last() else {
            return Nat("0".to_owned());
        };
        let mut out = top.to_string();
        for limb in rest.iter().rev() {
            write!(out, "{limb:09}").ok();
        }
        Nat(out)
    }

    /// The canonical decimal digits.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A name at a declaration or a selection keeps its own position for `S002` and `S003`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub pos: Pos,
    pub name: String,
}

/// The prefix operators `!`, `~`, and `-`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Inv,
    Neg,
}

/// The infix operators. A name ending in `w` is the wrapping form: `+%`, `-%`, `*%`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Lor,
    Land,
    Or,
    Xor,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Shl,
    Shr,
    Add,
    Sub,
    Addw,
    Subw,
    Mul,
    Div,
    Rem,
    Mulw,
}

/// An expression. A type in an expression position, such as `UInt[8]`, is an `Index`.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum Expr {
    Num {
        pos: Pos,
        value: Nat,
    },
    Bool {
        pos: Pos,
        value: bool,
    },
    Str {
        pos: Pos,
        value: String,
    },
    Name {
        pos: Pos,
        name: String,
    },
    Unary {
        pos: Pos,
        op: UnOp,
        arg: Box<Expr>,
    },
    Binary {
        pos: Pos,
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Cond {
        pos: Pos,
        cond: Box<Expr>,
        yes: Box<Expr>,
        no: Box<Expr>,
    },
    Call {
        pos: Pos,
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Index {
        pos: Pos,
        base: Box<Expr>,
        args: Vec<Expr>,
    },
    Field {
        pos: Pos,
        base: Box<Expr>,
        field: Ident,
    },
}

/// A type expression: a type name, or a type family with its static arguments.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum TypeExpr {
    Name {
        pos: Pos,
        name: String,
    },
    Index {
        pos: Pos,
        base: Box<TypeExpr>,
        args: Vec<Expr>,
    },
}

/// A statement. A target of `Assign` or `Connect` is a `Name`, a `Field`, or an `Index`
/// expression.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum Stmt {
    Local {
        pos: Pos,
        mutable: bool,
        name: Ident,
        ty: Option<TypeExpr>,
        value: Expr,
    },
    Assign {
        pos: Pos,
        target: Expr,
        value: Expr,
    },
    Connect {
        pos: Pos,
        target: Expr,
        value: Expr,
    },
    Reg {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
        init: Expr,
    },
    Wire {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
    },
    Input {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
    },
    Output {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
    },
    Inst {
        pos: Pos,
        name: Ident,
        module: Ident,
        args: Vec<Expr>,
    },
    Ret {
        pos: Pos,
        value: Option<Expr>,
    },
    CtIf {
        pos: Pos,
        cond: Expr,
        yes: Vec<Stmt>,
        no: Option<Vec<Stmt>>,
    },
    CtFor {
        pos: Pos,
        var: Ident,
        lo: Expr,
        hi: Expr,
        body: Vec<Stmt>,
    },
    Block {
        pos: Pos,
        body: Vec<Stmt>,
    },
    Expr {
        pos: Pos,
        value: Expr,
    },
}

/// A parameter of a function or a module. A module parameter always has `comptime`.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct Param {
    pub pos: Pos,
    pub comptime: bool,
    pub name: Ident,
    pub ty: TypeExpr,
}

/// A top-level item. The `domains` of a module are `None` without a clause and `Some` with
/// one. The list holds at most one name in slice 1.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum Item {
    Const {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
        value: Expr,
    },
    Fn {
        pos: Pos,
        comptime: bool,
        name: Ident,
        params: Vec<Param>,
        ret: TypeExpr,
        body: Vec<Stmt>,
    },
    Module {
        pos: Pos,
        name: Ident,
        params: Vec<Param>,
        domains: Option<Vec<Ident>>,
        body: Vec<Stmt>,
    },
}

// The recursive types free their children from a work list, so that a drop uses no recursion
// and is safe on any stack. Each `Drop` moves the children out and leaves a leaf behind.

impl Expr {
    fn leaf() -> Expr {
        Expr::Bool {
            pos: Pos { line: 0, col: 0 },
            value: false,
        }
    }

    fn take_children(&mut self, work: &mut Vec<Expr>) {
        let mut take = |e: &mut Expr| work.push(std::mem::replace(e, Expr::leaf()));
        match self {
            Expr::Unary { arg, .. } => take(arg),
            Expr::Binary { lhs, rhs, .. } => {
                take(lhs);
                take(rhs);
            }
            Expr::Cond { cond, yes, no, .. } => {
                take(cond);
                take(yes);
                take(no);
            }
            Expr::Call { callee, args, .. } => {
                take(callee);
                work.append(args);
            }
            Expr::Index { base, args, .. } => {
                take(base);
                work.append(args);
            }
            Expr::Field { base, .. } => take(base),
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } | Expr::Name { .. } => {}
        }
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.take_children(&mut work);
        while let Some(mut e) = work.pop() {
            e.take_children(&mut work);
        }
    }
}

impl Drop for TypeExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        let next = |t: &mut TypeExpr, work: &mut Vec<TypeExpr>| {
            if let TypeExpr::Index { base, .. } = t {
                let leaf = TypeExpr::Name {
                    pos: Pos { line: 0, col: 0 },
                    name: String::new(),
                };
                work.push(std::mem::replace(&mut **base, leaf));
            }
        };
        next(self, &mut work);
        while let Some(mut t) = work.pop() {
            next(&mut t, &mut work);
        }
    }
}

impl Stmt {
    fn take_children(&mut self, work: &mut Vec<Stmt>) {
        match self {
            Stmt::CtIf { yes, no, .. } => {
                work.append(yes);
                if let Some(no) = no {
                    work.append(no);
                }
            }
            Stmt::CtFor { body, .. } | Stmt::Block { body, .. } => work.append(body),
            _ => {}
        }
    }
}

impl Drop for Stmt {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.take_children(&mut work);
        while let Some(mut s) = work.pop() {
            s.take_children(&mut work);
        }
    }
}
