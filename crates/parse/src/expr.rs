// SPDX-License-Identifier: Apache-2.0
//! The grammar of types and expressions, with the precedence of the grammar file.
#![allow(clippy::enum_glob_use)] // The grammar names token kinds on almost every line.

use crate::parser::{Parser, Res};
use crate::tree::Checkpoint;
use syntax::SyntaxKind::{self, *};

/// The binding power of an infix operator. A higher number binds tighter.
fn binding_power(kind: SyntaxKind) -> Option<u8> {
    Some(match kind {
        PipePipe => 1,
        AmpAmp => 2,
        Pipe => 3,
        Caret => 4,
        Amp => 5,
        EqEq | BangEq | Lt | LtEq | Gt | GtEq => 6,
        Shl | Shr => 7,
        Plus | Minus | PlusPercent | MinusPercent => 8,
        Star | Slash | Percent | StarPercent => 9,
        _ => return None,
    })
}

const COMPARISON: u8 = 6;

/// The names after `@` that the grammar knows. They belong to slice 4.
const BUILTINS: [&str; 5] = ["TypeOf", "typeInfo", "field", "Struct", "ports"];

impl Parser<'_> {
    /// A type expression: a name, `()`, a tuple type, an array type, or a grouped type, then
    /// any number of `[arguments]`.
    pub(crate) fn type_expr(&mut self) -> Res {
        let start = self.offset();
        self.outermost(start, Self::type_form)
    }

    fn type_form(&mut self) -> Res {
        let checkpoint = self.checkpoint();
        match self.cur() {
            Some(Ident) => {
                self.node(NameType, |p| {
                    p.bump();
                    Some(())
                })?;
                if self.is(ColonColon) {
                    self.package_path(self.offset());
                    return None;
                }
                self.height = 1;
            }
            Some(LParen) => self.paren_type()?,
            Some(LBracket) => self.array_type()?,
            // The result type of a function type takes the suffixes, so the chain ends here.
            Some(FnKw) => return self.fn_chain(FnType),
            Some(At) => return self.builtin(),
            _ => {
                self.syntax_error("expected a type");
                return None;
            }
        }
        let mut height = self.height;
        loop {
            match self.cur() {
                Some(LBracket) => {
                    self.chain_at(checkpoint, IndexType, height, |p| {
                        p.arg_list(RBracket, false)
                    })?;
                    height = height.max(self.height) + 1;
                }
                Some(LParen) => {
                    self.later_slice(self.offset(), "a call in a type");
                    return None;
                }
                _ => break,
            }
        }
        self.height = height;
        Some(())
    }

    /// A chain of function types `fn (A) -> fn (B) -> T`, then the result type of the last. A
    /// loop opens one node for each arrow, so the recursion does not grow with the chain. The
    /// height of a function type is 1 plus the largest height of its parameter types and its
    /// result type: a `mut` mark adds none. `outer` is the kind of the first node.
    fn fn_chain(&mut self, outer: SyntaxKind) -> Res {
        let mut params = Vec::new();
        let mut opened = 0;
        let mut kind = outer;
        let res = loop {
            self.start(kind);
            opened += 1;
            let Some(height) = self.fn_head() else {
                break None;
            };
            params.push(height);
            if !self.is(FnKw) {
                break self.type_expr();
            }
            kind = FnType;
        };
        for _ in 0..opened {
            self.finish_node();
        }
        res?;
        for height in params.into_iter().rev() {
            self.height = height.max(self.height) + 1;
        }
        Some(())
    }

    /// `fn (P, mut Q,) ->`. The value is the largest height of the parameter types. A
    /// `comptime` mark is `S001` at the mark.
    fn fn_head(&mut self) -> Option<usize> {
        self.bump();
        self.expect(LParen, "`(`")?;
        let mut height = 0;
        while !self.is(RParen) {
            self.node(FnTypeParam, |p| {
                if p.is(ComptimeKw) {
                    p.syntax_error("a parameter of a function type has no `comptime` mark");
                    return None;
                }
                p.eat(MutKw);
                p.type_expr()?;
                height = height.max(p.height);
                Some(())
            })?;
            if !self.eat(Comma) {
                break;
            }
        }
        self.expect(RParen, "`,` or `)`")?;
        self.expect(Arrow, "`->`")?;
        Some(height)
    }

    /// `()`, a tuple type, or a grouped type. A group makes no node of the AST, so it adds
    /// nothing to the height.
    fn paren_type(&mut self) -> Res {
        if self.at_unit_or_tuple() {
            if self.next() == Some(RParen) {
                self.height = 1;
                return self.node(UnitType, |p| {
                    p.bump();
                    p.bump();
                    Some(())
                });
            }
            return self.node(TupleType, |p| {
                p.bump();
                let mut height = 0;
                loop {
                    p.type_expr()?;
                    height = height.max(p.height);
                    if !p.eat(Comma) || p.is(RParen) {
                        break;
                    }
                }
                p.expect(RParen, "`,` or `)`")?;
                p.height = height + 1;
                Some(())
            });
        }
        self.node(ParenType, |p| {
            p.bump();
            p.type_expr()?;
            p.expect(RParen, "`)`")
        })
    }

    /// `[T; N]`
    fn array_type(&mut self) -> Res {
        self.node(ArrayType, Self::array_type_parts)
    }

    /// The tokens and children of `[T; N]`, in a type and in an expression.
    fn array_type_parts(&mut self) -> Res {
        self.bump();
        self.type_expr()?;
        let elem = self.height;
        self.expect(Semi, "`;`")?;
        self.expr()?;
        self.expect(RBracket, "`]`")?;
        self.height = elem.max(self.height) + 1;
        Some(())
    }

    /// An expression: a conditional, or the operators by precedence. A `match` is at the
    /// level of the conditional, and it is a later phase of slice 3.
    pub(crate) fn expr(&mut self) -> Res {
        let start = self.offset();
        self.outermost(start, |p| {
            if p.is(MatchKw) {
                p.later_slice(p.offset(), "a `match`");
                None
            } else if p.is(IfKw) {
                p.cond_form()
            } else {
                p.binary(0)
            }
        })
    }

    fn cond_form(&mut self) -> Res {
        self.node(CondExpr, |p| {
            p.bump();
            p.expect(LParen, "`(`")?;
            p.expr()?;
            let mut height = p.height;
            p.expect(RParen, "`)`")?;
            for last in [false, true] {
                p.expect(LBrace, "`{`")?;
                p.expr()?;
                height = height.max(p.height);
                p.expect(RBrace, "`}`")?;
                if !last {
                    p.expect(ElseKw, "`else`")?;
                }
            }
            p.height = height + 1;
            Some(())
        })
    }

    /// Operators of at least `min` binding power. All are left-associative, except the
    /// comparisons, which do not chain.
    fn binary(&mut self, min: u8) -> Res {
        let checkpoint = self.checkpoint();
        self.unary()?;
        self.climb(checkpoint, min)
    }

    /// The operators of at least `min` binding power after an operand that is already parsed.
    /// The operand starts at the checkpoint.
    pub(crate) fn climb(&mut self, checkpoint: Checkpoint, min: u8) -> Res {
        let mut height = self.height;
        while let Some(power) = self.cur().and_then(binding_power).filter(|&b| b >= min) {
            self.chain_at(checkpoint, BinExpr, height, |p| {
                p.bump();
                p.binary(power + 1)
            })?;
            height = height.max(self.height) + 1;
            if power == COMPARISON && self.cur().and_then(binding_power) == Some(COMPARISON) {
                self.syntax_error("a comparison does not chain");
                return None;
            }
        }
        self.height = height;
        Some(())
    }

    /// A chain of unary operators. The loop opens one node for each operator, so the
    /// recursion does not grow with the length of the chain.
    fn unary(&mut self) -> Res {
        let mut ops = 0;
        while matches!(self.cur(), Some(Bang | Tilde | Minus)) {
            self.start(UnaryExpr);
            self.bump();
            ops += 1;
        }
        let res = if self.is(FnKw) {
            // A function type is a unary operand: its result type takes the suffixes.
            self.place = false;
            self.fn_chain(FnTypeExpr)
        } else {
            self.postfix_expr()
        };
        for _ in 0..ops {
            self.finish_node();
        }
        res?;
        self.height += ops;
        Some(())
    }

    /// A primary expression with its calls, indexes, field selections, and selectors `.N`.
    pub(crate) fn postfix_expr(&mut self) -> Res {
        let checkpoint = self.checkpoint();
        let mut place = self.is(Ident) && self.next() != Some(ColonColon);
        self.primary()?;
        let mut height = self.height;
        loop {
            match self.cur() {
                Some(LParen) => {
                    place = false;
                    self.chain_at(checkpoint, CallExpr, height, |p| p.arg_list(RParen, true))?;
                }
                Some(LBracket) => {
                    self.chain_at(checkpoint, IndexExpr, height, |p| {
                        p.arg_list(RBracket, false)
                    })?;
                }
                Some(Dot) if matches!(self.next(), Some(Dec | Hex | Bin)) => {
                    self.chain_at(checkpoint, SelectExpr, height, |p| {
                        p.bump();
                        p.bump();
                        Some(())
                    })?;
                    self.height = 0;
                }
                Some(Dot) if self.next() == Some(Ident) && self.after_next() == Some(LParen) => {
                    place = false;
                    self.chain_at(checkpoint, MethodExpr, height, |p| {
                        p.bump();
                        p.bump();
                        p.arg_list(RParen, true)
                    })?;
                }
                Some(Dot) => {
                    self.chain_at(checkpoint, FieldExpr, height, |p| {
                        p.bump();
                        if !p.eat(Ident) {
                            p.syntax_error("expected a field name");
                            return None;
                        }
                        Some(())
                    })?;
                    self.height = 0;
                }
                _ => break,
            }
            height = height.max(self.height) + 1;
        }
        self.height = height;
        self.place = place;
        Some(())
    }

    /// The arguments between a pair of delimiters, with an optional trailing comma. The
    /// opening delimiter is the one that pairs with `close`.
    pub(crate) fn arg_list(&mut self, close: SyntaxKind, may_be_empty: bool) -> Res {
        let (open, what, next) = if close == RParen {
            (LParen, "`(`", "`,` or `)`")
        } else {
            (LBracket, "`[`", "`,` or `]`")
        };
        self.node(ArgList, |p| {
            p.expect(open, what)?;
            let mut height = 0;
            if !(may_be_empty && p.is(close)) {
                loop {
                    p.expr()?;
                    height = height.max(p.height);
                    if !p.eat(Comma) || p.is(close) {
                        break;
                    }
                }
            }
            p.expect(close, next)?;
            p.height = height;
            Some(())
        })
    }

    fn primary(&mut self) -> Res {
        match self.cur() {
            Some(Dec | Hex | Bin | Str | TrueKw | FalseKw) => {
                self.node(Literal, |p| {
                    p.bump();
                    Some(())
                })?;
            }
            Some(Ident) if self.next() == Some(ColonColon) => {
                self.node(PathExpr, |p| {
                    p.bump();
                    p.bump();
                    p.expect(Ident, "a variant name")?;
                    if p.is(ColonColon) {
                        p.package_path(p.offset());
                        return None;
                    }
                    Some(())
                })?;
            }
            Some(Ident) => {
                self.node(NameExpr, |p| {
                    p.bump();
                    Some(())
                })?;
            }
            Some(LParen) => return self.paren(),
            Some(LBracket) => return self.array(),
            Some(At) => return self.builtin(),
            _ => {
                self.syntax_error("expected an expression");
                return None;
            }
        }
        self.height = 1;
        Some(())
    }

    /// `@` in an expression or a type: a builtin belongs to a later slice, and any other
    /// name after `@` is a syntax error at that name.
    fn builtin(&mut self) -> Res {
        if self.next() == Some(Ident) && BUILTINS.contains(&self.next_text()) {
            self.later_slice(self.offset(), "a builtin");
        } else {
            self.syntax_error_at(self.offset_of(1), "expected the name of a builtin");
        }
        None
    }

    /// A parenthesized expression, `()`, or a tuple. Parentheses make no node of the AST, so a
    /// group adds nothing to the height.
    fn paren(&mut self) -> Res {
        if !self.at_unit_or_tuple() {
            return self.node(ParenExpr, |p| {
                p.bump();
                p.expr()?;
                p.expect(RParen, "`)`")
            });
        }
        if self.next() == Some(RParen) {
            self.height = 1;
            return self.node(UnitExpr, |p| {
                p.bump();
                p.bump();
                Some(())
            });
        }
        self.node(TupleExpr, |p| p.arg_list(RParen, true))?;
        self.height += 1;
        Some(())
    }

    /// An array value, or an array type `[T; N]`. The `;` in the bracket decides, and the
    /// parser never reads a token again: the element of `[T; N]` is a type.
    fn array(&mut self) -> Res {
        if self.at_array_type() {
            return self.array_type_expr();
        }
        self.node(ArrayExpr, |p| p.arg_list(RBracket, true))?;
        self.height += 1;
        Some(())
    }

    /// `[T; N]` in an expression.
    fn array_type_expr(&mut self) -> Res {
        self.node(ArrayTypeExpr, Self::array_type_parts)
    }
}
