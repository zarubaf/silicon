// SPDX-License-Identifier: Apache-2.0
//! The source AST of slices 1 and 2. It mirrors `Silicon.Source.Syntax` in Lean: the same types,
//! the same constructors, and the same field order. Only the `NodeId` of a node is not in
//! Lean. The Lean name of a constructor is the lowercase name of the variant here, so the
//! AST dump can print both with one rule.

use std::fmt::Write;

/// A position is a line and a column. Both start at 1. A column counts characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

/// The id of a node: an `Ident`, an `Expr::Name`, a `TypeExpr::Name`, an `Expr::Num`, an
/// `Expr::Call`, or an `Expr::Method`. The lowering gives each such node of one parse its own id, in source order. A
/// later pass keys its facts about a node by the id and not by the position, because two nodes
/// can share a position or have none. The id is not in the Lean AST, and the dump does not print it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(usize);

impl NodeId {
    /// The first id of a parse.
    pub(crate) const FIRST: NodeId = NodeId(0);

    /// The id of a node that a `Drop` makes and frees at once. No pass sees it.
    const DROPPED: NodeId = NodeId(usize::MAX);

    /// The id after this one.
    pub(crate) fn next(self) -> NodeId {
        NodeId(self.0 + 1)
    }
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
    pub id: NodeId,
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

/// An expression. A type in an expression position, such as `UInt[8]`, is an `Index`. An array
/// type `[T; N]` is an `ArrayType`. Its element is a type expression, so `Expr` and
/// `TypeExpr` are mutually recursive, as in Lean.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum Expr {
    Num {
        pos: Pos,
        id: NodeId,
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
        id: NodeId,
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
        id: NodeId,
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Index {
        pos: Pos,
        base: Box<Expr>,
        args: Vec<Expr>,
    },
    /// The receiver call `recv.name(args)`. Its position is the position of the receiver.
    Method {
        pos: Pos,
        id: NodeId,
        recv: Box<Expr>,
        name: Ident,
        args: Vec<Expr>,
    },
    Field {
        pos: Pos,
        base: Box<Expr>,
        field: Ident,
    },
    Unit {
        pos: Pos,
    },
    /// At least one element: `()` is `Unit`.
    Tuple {
        pos: Pos,
        elems: Vec<Expr>,
    },
    Array {
        pos: Pos,
        elems: Vec<Expr>,
    },
    /// The selector `.N` of a tuple. `lit_pos` is the position of the number literal, for `S013`.
    Select {
        pos: Pos,
        base: Box<Expr>,
        lit_pos: Pos,
        index: Nat,
    },
    /// The array type `[T; N]` in an expression.
    ArrayType {
        pos: Pos,
        elem: Box<TypeExpr>,
        len: Box<Expr>,
    },
    /// The function type `fn (T, mut U) -> V` in an expression: a unary operand.
    FnType {
        pos: Pos,
        params: Vec<FnParam>,
        ret: Box<TypeExpr>,
    },
}

/// A type expression: a type name, a type family with its static arguments, the unit type,
/// a tuple type, an array type `[T; N]`, or a function type `fn (T, mut U) -> V`.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum TypeExpr {
    Name {
        pos: Pos,
        id: NodeId,
        name: String,
    },
    Index {
        pos: Pos,
        base: Box<TypeExpr>,
        args: Vec<Expr>,
    },
    Unit {
        pos: Pos,
    },
    /// At least one element type: `()` is `Unit`.
    Tuple {
        pos: Pos,
        elems: Vec<TypeExpr>,
    },
    Array {
        pos: Pos,
        elem: Box<TypeExpr>,
        len: Box<Expr>,
    },
    Fn {
        pos: Pos,
        params: Vec<FnParam>,
        ret: Box<TypeExpr>,
    },
}

/// A parameter type of a function type, with its `mut` mark. It has no `comptime` mark,
/// because that mark is `S001`.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct FnParam {
    pub mutable: bool,
    pub ty: TypeExpr,
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
    /// The statement `type N = T;`.
    Alias {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
    },
}

/// The mode of a parameter: no mark, `comptime`, or `mut`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamMode {
    None,
    Comptime,
    Mut,
}

/// A parameter of a function, a module, or a struct. A module parameter and a struct parameter
/// always have the mode `Comptime`.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct Param {
    pub pos: Pos,
    pub mode: ParamMode,
    pub name: Ident,
    pub ty: TypeExpr,
}

/// A field of a struct: `name: ty`.
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct StructField {
    pub name: Ident,
    pub ty: TypeExpr,
}

/// A top-level item. A `Struct` without parameters has an empty list of parameters. An `Alias`
/// is the item `type N = T;`. The `domains` of a module are `None` without a clause and `Some` with
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
    Struct {
        pos: Pos,
        name: Ident,
        params: Vec<Param>,
        fields: Vec<StructField>,
    },
    Alias {
        pos: Pos,
        name: Ident,
        ty: TypeExpr,
    },
}

impl Item {
    /// The name of the item.
    #[must_use]
    pub fn name(&self) -> &Ident {
        let (Item::Const { name, .. }
        | Item::Fn { name, .. }
        | Item::Module { name, .. }
        | Item::Struct { name, .. }
        | Item::Alias { name, .. }) = self;
        name
    }
}

// The recursive types free their children from a work list, so that a drop uses no recursion
// and is safe on any stack. `Expr` and `TypeExpr` contain each other, so they share one work
// list. Each `Drop` moves the children out and leaves a leaf behind.

/// A child that waits to be freed.
enum Pending {
    Expr(Expr),
    Type(TypeExpr),
}

impl Pending {
    fn take_children(&mut self, work: &mut Vec<Pending>) {
        match self {
            Pending::Expr(e) => e.take_children(work),
            Pending::Type(t) => t.take_children(work),
        }
    }
}

/// Frees what the children of a node hold, from a work list.
fn free(mut work: Vec<Pending>) {
    while let Some(mut pending) = work.pop() {
        pending.take_children(&mut work);
    }
}

fn take_expr(e: &mut Expr, work: &mut Vec<Pending>) {
    work.push(Pending::Expr(std::mem::replace(e, Expr::leaf())));
}

fn take_type(t: &mut TypeExpr, work: &mut Vec<Pending>) {
    work.push(Pending::Type(std::mem::replace(t, TypeExpr::leaf())));
}

fn take_exprs(es: &mut Vec<Expr>, work: &mut Vec<Pending>) {
    work.extend(es.drain(..).map(Pending::Expr));
}

fn take_params(params: &mut Vec<FnParam>, work: &mut Vec<Pending>) {
    work.extend(params.drain(..).map(|p| Pending::Type(p.ty)));
}

impl Expr {
    fn leaf() -> Expr {
        Expr::Bool {
            pos: Pos { line: 0, col: 0 },
            value: false,
        }
    }

    fn take_children(&mut self, work: &mut Vec<Pending>) {
        match self {
            Expr::Unary { arg, .. } => take_expr(arg, work),
            Expr::Binary { lhs, rhs, .. } => {
                take_expr(lhs, work);
                take_expr(rhs, work);
            }
            Expr::Cond { cond, yes, no, .. } => {
                take_expr(cond, work);
                take_expr(yes, work);
                take_expr(no, work);
            }
            Expr::Call { callee, args, .. } => {
                take_expr(callee, work);
                take_exprs(args, work);
            }
            Expr::Index { base, args, .. } => {
                take_expr(base, work);
                take_exprs(args, work);
            }
            Expr::Method { recv, args, .. } => {
                take_expr(recv, work);
                take_exprs(args, work);
            }
            Expr::Field { base, .. } | Expr::Select { base, .. } => take_expr(base, work),
            Expr::Tuple { elems, .. } | Expr::Array { elems, .. } => take_exprs(elems, work),
            Expr::ArrayType { elem, len, .. } => {
                take_type(elem, work);
                take_expr(len, work);
            }
            Expr::FnType { params, ret, .. } => {
                take_params(params, work);
                take_type(ret, work);
            }
            Expr::Num { .. }
            | Expr::Bool { .. }
            | Expr::Str { .. }
            | Expr::Name { .. }
            | Expr::Unit { .. } => {}
        }
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.take_children(&mut work);
        free(work);
    }
}

impl TypeExpr {
    fn leaf() -> TypeExpr {
        TypeExpr::Name {
            pos: Pos { line: 0, col: 0 },
            id: NodeId::DROPPED,
            name: String::new(),
        }
    }

    fn take_children(&mut self, work: &mut Vec<Pending>) {
        match self {
            TypeExpr::Index { base, args, .. } => {
                take_type(base, work);
                take_exprs(args, work);
            }
            TypeExpr::Array { elem, len, .. } => {
                take_type(elem, work);
                take_expr(len, work);
            }
            TypeExpr::Tuple { elems, .. } => work.extend(elems.drain(..).map(Pending::Type)),
            TypeExpr::Fn { params, ret, .. } => {
                take_params(params, work);
                take_type(ret, work);
            }
            TypeExpr::Name { .. } | TypeExpr::Unit { .. } => {}
        }
    }
}

impl Drop for TypeExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.take_children(&mut work);
        free(work);
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
