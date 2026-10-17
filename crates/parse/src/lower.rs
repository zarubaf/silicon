// SPDX-License-Identifier: Apache-2.0
//! Lowers an error-free syntax tree into the AST. Every function returns `None` for a
//! tree that does not have the shape that the parser builds.

use crate::ast::{
    BinOp, Expr, FnParam, Ident, Item, Nat, NodeId, Param, ParamMode, Pos, Stmt, StructField,
    TypeExpr, UnOp, Variant,
};
use crate::error::LineIndex;
use rowan::NodeOrToken;
use std::cell::Cell;
use syntax::{SyntaxKind, SyntaxNode, SyntaxToken};

pub(crate) struct Lower<'a> {
    index: LineIndex<'a>,
    /// The id of the next node that has one.
    next: Cell<NodeId>,
}

fn tokens(node: &SyntaxNode) -> impl Iterator<Item = SyntaxToken> {
    node.children_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .filter(|t| !t.kind().is_trivia())
}

fn token(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    tokens(node).find(|t| t.kind() == kind)
}

fn has(node: &SyntaxNode, kind: SyntaxKind) -> bool {
    token(node, kind).is_some()
}

fn param_mode(param: &SyntaxNode) -> ParamMode {
    if has(param, SyntaxKind::ComptimeKw) {
        ParamMode::Comptime
    } else if has(param, SyntaxKind::MutKw) {
        ParamMode::Mut
    } else {
        ParamMode::None
    }
}

fn unescape(literal: &str) -> String {
    let body = literal
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or(literal);
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

fn number(text: &str) -> Nat {
    if let Some(digits) = text.strip_prefix("0x") {
        Nat::from_digits(digits, 16)
    } else if let Some(digits) = text.strip_prefix("0b") {
        Nat::from_digits(digits, 2)
    } else {
        Nat::from_digits(text, 10)
    }
}

fn binop(kind: SyntaxKind) -> Option<BinOp> {
    #[allow(clippy::enum_glob_use)]
    use SyntaxKind::*;
    Some(match kind {
        PipePipe => BinOp::Lor,
        AmpAmp => BinOp::Land,
        Pipe => BinOp::Or,
        Caret => BinOp::Xor,
        Amp => BinOp::And,
        EqEq => BinOp::Eq,
        BangEq => BinOp::Ne,
        Lt => BinOp::Lt,
        LtEq => BinOp::Le,
        Gt => BinOp::Gt,
        GtEq => BinOp::Ge,
        Shl => BinOp::Shl,
        Shr => BinOp::Shr,
        Plus => BinOp::Add,
        Minus => BinOp::Sub,
        PlusPercent => BinOp::Addw,
        MinusPercent => BinOp::Subw,
        Star => BinOp::Mul,
        Slash => BinOp::Div,
        Percent => BinOp::Rem,
        StarPercent => BinOp::Mulw,
        _ => return None,
    })
}

impl<'a> Lower<'a> {
    pub(crate) fn new(index: LineIndex<'a>) -> Lower<'a> {
        Lower {
            index,
            next: Cell::new(NodeId::FIRST),
        }
    }

    /// A new id for a node. The lowering builds the nodes in source order, and a node takes
    /// its id before its children.
    fn id(&self) -> NodeId {
        let id = self.next.get();
        self.next.set(id.next());
        id
    }

    /// The position of the first token of the node. The parser opens each node after the
    /// trivia, so the node starts at its first token, and this costs no walk of the node.
    fn pos_of(&self, node: &SyntaxNode) -> Pos {
        self.index.pos(usize::from(node.text_range().start()))
    }

    fn pos_at(&self, token: &SyntaxToken) -> Pos {
        self.index.pos(usize::from(token.text_range().start()))
    }

    /// The first name token of the node.
    fn ident(&self, node: &SyntaxNode) -> Option<Ident> {
        self.ident_at(node, 0)
    }

    fn ident_at(&self, node: &SyntaxNode, n: usize) -> Option<Ident> {
        let token = tokens(node)
            .filter(|t| t.kind() == SyntaxKind::Ident)
            .nth(n)?;
        Some(Ident {
            pos: self.pos_at(&token),
            id: self.id(),
            name: token.text().to_owned(),
        })
    }

    pub(crate) fn source(&self, root: &SyntaxNode) -> Option<Vec<Item>> {
        root.children().map(|n| self.item(&n)).collect()
    }

    /// The expression of a tree from `Parser::finish_expr` without an error.
    pub(crate) fn source_expr(&self, root: &SyntaxNode) -> Option<Expr> {
        self.expr(&root.children().find(is_expr)?)
    }

    fn item(&self, node: &SyntaxNode) -> Option<Item> {
        let pos = self.pos_of(node);
        let name = self.ident(node)?;
        match node.kind() {
            SyntaxKind::ConstItem => Some(Item::Const {
                pos,
                name,
                ty: self.type_expr(&node.children().find(is_type)?)?,
                value: self.expr(&node.children().find(is_expr)?)?,
            }),
            SyntaxKind::FnItem => Some(Item::Fn {
                pos,
                comptime: has(node, SyntaxKind::ComptimeKw),
                name,
                params: self.params(node)?,
                ret: self.type_expr(&node.children().find(is_type)?)?,
                body: self.block(&node.children().find(|n| n.kind() == SyntaxKind::Block)?)?,
            }),
            SyntaxKind::ModuleItem => Some(Item::Module {
                pos,
                name,
                params: self.params(node)?,
                domains: node
                    .children()
                    .find(|n| n.kind() == SyntaxKind::DomainsClause)
                    .map(|clause| {
                        tokens(&clause)
                            .filter(|t| t.kind() == SyntaxKind::Ident)
                            .map(|t| Ident {
                                pos: self.pos_at(&t),
                                id: self.id(),
                                name: t.text().to_owned(),
                            })
                            .collect()
                    }),
                body: self.block(&node.children().find(|n| n.kind() == SyntaxKind::Block)?)?,
            }),
            SyntaxKind::StructItem => Some(Item::Struct {
                pos,
                name,
                params: self.optional_params(node)?,
                fields: node
                    .children()
                    .filter(|n| n.kind() == SyntaxKind::StructField)
                    .map(|field| {
                        Some(StructField {
                            name: self.ident(&field)?,
                            ty: self.type_expr(&field.children().find(is_type)?)?,
                        })
                    })
                    .collect::<Option<_>>()?,
            }),
            SyntaxKind::AliasItem => Some(Item::Alias {
                pos,
                name,
                ty: self.type_expr(&node.children().find(is_type)?)?,
            }),
            SyntaxKind::EnumItem => Some(Item::Enum {
                pos,
                name,
                tag: self.type_expr(&node.children().find(is_type)?)?,
                variants: node
                    .children()
                    .filter(|n| n.kind() == SyntaxKind::EnumVariant)
                    .map(|variant| self.variant(&variant))
                    .collect::<Option<_>>()?,
            }),
            _ => None,
        }
    }

    fn variant(&self, node: &SyntaxNode) -> Option<Variant> {
        Some(Variant {
            name: self.ident(node)?,
            payload: node
                .children()
                .filter(is_type)
                .map(|t| self.type_expr(&t))
                .collect::<Option<_>>()?,
            tag: self.expr(&node.children().find(is_expr)?)?,
        })
    }

    /// The parameters of a struct: none without parentheses.
    fn optional_params(&self, node: &SyntaxNode) -> Option<Vec<Param>> {
        if node.children().any(|n| n.kind() == SyntaxKind::ParamList) {
            self.params(node)
        } else {
            Some(Vec::new())
        }
    }

    fn params(&self, node: &SyntaxNode) -> Option<Vec<Param>> {
        let list = node
            .children()
            .find(|n| n.kind() == SyntaxKind::ParamList)?;
        list.children()
            .map(|param| {
                Some(Param {
                    pos: self.pos_of(&param),
                    mode: param_mode(&param),
                    name: self.ident(&param)?,
                    ty: self.type_expr(&param.children().find(is_type)?)?,
                })
            })
            .collect()
    }

    fn block(&self, node: &SyntaxNode) -> Option<Vec<Stmt>> {
        node.children().map(|n| self.stmt(&n)).collect()
    }

    fn stmt(&self, node: &SyntaxNode) -> Option<Stmt> {
        #[allow(clippy::enum_glob_use)]
        use SyntaxKind::*;
        if node.kind() == Block {
            return Some(Stmt::Block {
                pos: self.pos_of(node),
                body: self.block(node)?,
            });
        }
        let pos = self.pos_of(node);
        let exprs: Vec<SyntaxNode> = node.children().filter(is_expr).collect();
        let types: Vec<SyntaxNode> = node.children().filter(is_type).collect();
        let nth_expr = |n: usize| self.expr(exprs.get(n)?);
        let ty = || self.type_expr(types.first()?);
        match node.kind() {
            LetStmt => Some(Stmt::Local {
                pos,
                mutable: has(node, MutKw),
                name: self.ident(node)?,
                ty: types
                    .first()
                    .map_or(Some(None), |t| self.type_expr(t).map(Some))?,
                value: nth_expr(0)?,
            }),
            AssignStmt => Some(Stmt::Assign {
                pos,
                target: nth_expr(0)?,
                value: nth_expr(1)?,
            }),
            ConnectStmt => Some(Stmt::Connect {
                pos,
                target: nth_expr(0)?,
                value: nth_expr(1)?,
            }),
            RegStmt | WireStmt | MemStmt | InputStmt | OutputStmt => self.resource_stmt(node, pos),
            InstStmt => Some(Stmt::Inst {
                pos,
                name: self.ident(node)?,
                module: self.ident_at(node, 1)?,
                args: self.args(node)?,
            }),
            ReturnStmt => Some(Stmt::Ret {
                pos,
                value: exprs
                    .first()
                    .map_or(Some(None), |e| self.expr(e).map(Some))?,
            }),
            CtIfStmt => {
                let blocks: Vec<SyntaxNode> =
                    node.children().filter(|n| n.kind() == Block).collect();
                Some(Stmt::CtIf {
                    pos,
                    cond: nth_expr(0)?,
                    yes: self.block(blocks.first()?)?,
                    no: blocks
                        .get(1)
                        .map_or(Some(None), |b| self.block(b).map(Some))?,
                })
            }
            CtForStmt => Some(Stmt::CtFor {
                pos,
                var: self.ident(node)?,
                lo: nth_expr(0)?,
                hi: nth_expr(1)?,
                body: self.block(&node.children().find(|n| n.kind() == Block)?)?,
            }),
            ExprStmt => Some(Stmt::Expr {
                pos,
                value: nth_expr(0)?,
            }),
            AliasStmt => Some(Stmt::Alias {
                pos,
                name: self.ident(node)?,
                ty: ty()?,
            }),
            _ => None,
        }
    }

    /// A statement that declares a register, a wire, a memory, or a port.
    fn resource_stmt(&self, node: &SyntaxNode, pos: Pos) -> Option<Stmt> {
        #[allow(clippy::enum_glob_use)]
        use SyntaxKind::*;
        let exprs: Vec<SyntaxNode> = node.children().filter(is_expr).collect();
        let types: Vec<SyntaxNode> = node.children().filter(is_type).collect();
        let nth_expr = |n: usize| self.expr(exprs.get(n)?);
        let ty = || self.type_expr(types.first()?);
        match node.kind() {
            RegStmt => Some(Stmt::Reg {
                pos,
                name: self.ident(node)?,
                ty: ty()?,
                init: nth_expr(0)?,
            }),
            WireStmt => Some(Stmt::Wire {
                pos,
                name: self.ident(node)?,
                ty: ty()?,
            }),
            MemStmt => Some(Stmt::Mem {
                pos,
                name: self.ident(node)?,
                word: ty()?,
                depth: nth_expr(0)?,
            }),
            InputStmt => Some(Stmt::Input {
                pos,
                name: self.ident(node)?,
                ty: ty()?,
            }),
            OutputStmt => Some(Stmt::Output {
                pos,
                name: self.ident(node)?,
                ty: ty()?,
            }),
            _ => None,
        }
    }

    /// The expressions of the `ArgList` child.
    fn args(&self, node: &SyntaxNode) -> Option<Vec<Expr>> {
        let list = node.children().find(|n| n.kind() == SyntaxKind::ArgList)?;
        list.children().map(|e| self.expr(&e)).collect()
    }

    fn type_expr(&self, node: &SyntaxNode) -> Option<TypeExpr> {
        let pos = self.pos_of(node);
        match node.kind() {
            SyntaxKind::NameType => Some(TypeExpr::Name {
                pos,
                id: self.id(),
                name: token(node, SyntaxKind::Ident)?.text().to_owned(),
            }),
            SyntaxKind::IndexType => Some(TypeExpr::Index {
                pos,
                base: Box::new(self.type_expr(&node.children().find(is_type)?)?),
                args: self.args(node)?,
            }),
            SyntaxKind::UnitType => Some(TypeExpr::Unit { pos }),
            SyntaxKind::TupleType => Some(TypeExpr::Tuple {
                pos,
                elems: node
                    .children()
                    .map(|t| self.type_expr(&t))
                    .collect::<Option<_>>()?,
            }),
            SyntaxKind::ArrayType => Some(TypeExpr::Array {
                pos,
                elem: Box::new(self.type_expr(&node.children().find(is_type)?)?),
                len: Box::new(self.expr(&node.children().find(is_expr)?)?),
            }),
            SyntaxKind::ParenType => self.type_expr(&node.children().find(is_type)?),
            SyntaxKind::FnType => Some(TypeExpr::Fn {
                pos,
                params: self.fn_params(node)?,
                ret: Box::new(self.type_expr(&node.children().find(is_type)?)?),
            }),
            _ => None,
        }
    }

    /// The parameter types of a function type.
    fn fn_params(&self, node: &SyntaxNode) -> Option<Vec<FnParam>> {
        node.children()
            .filter(|n| n.kind() == SyntaxKind::FnTypeParam)
            .map(|param| {
                Some(FnParam {
                    mutable: has(&param, SyntaxKind::MutKw),
                    ty: self.type_expr(&param.children().find(is_type)?)?,
                })
            })
            .collect()
    }

    fn expr(&self, node: &SyntaxNode) -> Option<Expr> {
        #[allow(clippy::enum_glob_use)]
        use SyntaxKind::*;
        let pos = self.pos_of(node);
        let operands: Vec<SyntaxNode> = node.children().filter(is_expr).collect();
        let operand =
            |n: usize| -> Option<Box<Expr>> { Some(Box::new(self.expr(operands.get(n)?)?)) };
        match node.kind() {
            Literal => {
                let token = tokens(node).next()?;
                Some(match token.kind() {
                    Dec | Hex | Bin => Expr::Num {
                        pos,
                        id: self.id(),
                        value: number(token.text()),
                    },
                    Str => Expr::Str {
                        pos,
                        value: unescape(token.text()),
                    },
                    TrueKw | FalseKw => Expr::Bool {
                        pos,
                        value: token.kind() == TrueKw,
                    },
                    _ => return None,
                })
            }
            NameExpr => Some(Expr::Name {
                pos,
                id: self.id(),
                name: token(node, Ident)?.text().to_owned(),
            }),
            PathExpr => Some(Expr::Path {
                pos,
                ty: self.ident_at(node, 0)?,
                variant: self.ident_at(node, 1)?,
            }),
            ParenExpr => self.expr(operands.first()?),
            UnaryExpr => Some(Expr::Unary {
                pos,
                op: match tokens(node).next()?.kind() {
                    Bang => UnOp::Not,
                    Tilde => UnOp::Inv,
                    Minus => UnOp::Neg,
                    _ => return None,
                },
                arg: operand(0)?,
            }),
            BinExpr => Some(Expr::Binary {
                pos,
                op: binop(tokens(node).next()?.kind())?,
                lhs: operand(0)?,
                rhs: operand(1)?,
            }),
            CondExpr => Some(Expr::Cond {
                pos,
                cond: operand(0)?,
                yes: operand(1)?,
                no: operand(2)?,
            }),
            FnTypeExpr => Some(Expr::FnType {
                pos,
                params: self.fn_params(node)?,
                ret: Box::new(self.type_expr(&node.children().find(is_type)?)?),
            }),
            CallExpr | MethodExpr | IndexExpr | FieldExpr | SelectExpr => self.postfix(node, pos),
            UnitExpr => Some(Expr::Unit { pos }),
            TupleExpr => Some(Expr::Tuple {
                pos,
                elems: self.args(node)?,
            }),
            ArrayExpr => Some(Expr::Array {
                pos,
                elems: self.args(node)?,
            }),
            ArrayTypeExpr => Some(Expr::ArrayType {
                pos,
                elem: Box::new(self.type_expr(&node.children().find(is_type)?)?),
                len: operand(0)?,
            }),
            _ => None,
        }
    }

    /// A call, a receiver call, an index, a field, or a selector: the postfix forms, which
    /// have an operand first.
    fn postfix(&self, node: &SyntaxNode, pos: Pos) -> Option<Expr> {
        #[allow(clippy::enum_glob_use)]
        use SyntaxKind::*;
        let operand = || Some(Box::new(self.expr(&node.children().find(is_expr)?)?));
        match node.kind() {
            CallExpr => Some(Expr::Call {
                pos,
                id: self.id(),
                callee: operand()?,
                args: self.args(node)?,
            }),
            MethodExpr => Some(Expr::Method {
                pos,
                id: self.id(),
                recv: operand()?,
                name: self.ident(node)?,
                args: self.args(node)?,
            }),
            IndexExpr => Some(Expr::Index {
                pos,
                base: operand()?,
                args: self.args(node)?,
            }),
            FieldExpr => Some(Expr::Field {
                pos,
                base: operand()?,
                field: self.ident(node)?,
            }),
            SelectExpr => {
                let literal = tokens(node).find(|t| matches!(t.kind(), Dec | Hex | Bin))?;
                Some(Expr::Select {
                    pos,
                    base: operand()?,
                    lit_pos: self.pos_at(&literal),
                    index: number(literal.text()),
                })
            }
            _ => None,
        }
    }
}

fn is_type(node: &SyntaxNode) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::NameType
            | SyntaxKind::IndexType
            | SyntaxKind::UnitType
            | SyntaxKind::TupleType
            | SyntaxKind::ArrayType
            | SyntaxKind::ParenType
            | SyntaxKind::FnType
    )
}

fn is_expr(node: &SyntaxNode) -> bool {
    #[allow(clippy::enum_glob_use)]
    use SyntaxKind::*;
    matches!(
        node.kind(),
        Literal
            | NameExpr
            | PathExpr
            | ParenExpr
            | UnaryExpr
            | BinExpr
            | CondExpr
            | CallExpr
            | IndexExpr
            | FieldExpr
            | MethodExpr
            | SelectExpr
            | UnitExpr
            | TupleExpr
            | ArrayExpr
            | ArrayTypeExpr
            | FnTypeExpr
    )
}
