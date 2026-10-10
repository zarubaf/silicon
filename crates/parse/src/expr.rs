//! The grammar of types and expressions, with the precedence of the grammar file.
#![allow(clippy::enum_glob_use)] // The grammar names token kinds on almost every line.

use crate::ast::Nat;
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
    /// A type expression: a name, then any number of `[arguments]`.
    pub(crate) fn type_expr(&mut self) -> Res {
        let start = self.offset();
        self.outermost(start, Self::type_form)
    }

    fn type_form(&mut self) -> Res {
        let start = self.offset();
        let checkpoint = self.checkpoint();
        match self.cur() {
            Some(Ident) => {
                self.node(NameType, |p| {
                    p.bump();
                    Some(())
                })?;
                if self.is(ColonColon) {
                    self.later_slice(self.offset(), "a path");
                    return None;
                }
            }
            Some(LParen | LBracket | FnKw) => {
                self.later_slice(start, "this type");
                return None;
            }
            Some(At) => return self.builtin(),
            _ => {
                self.syntax_error("expected a type");
                return None;
            }
        }
        let mut height = 1;
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

    /// An expression: a conditional, or the operators by precedence.
    pub(crate) fn expr(&mut self) -> Res {
        let start = self.offset();
        self.outermost(start, |p| {
            if p.is(IfKw) {
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
        let res = self.postfix_expr();
        for _ in 0..ops {
            self.finish_node();
        }
        res?;
        self.height += ops;
        Some(())
    }

    /// A primary expression with its calls, indexes, and field selections.
    pub(crate) fn postfix_expr(&mut self) -> Res {
        let checkpoint = self.checkpoint();
        let mut place = self.is(Ident);
        let mut indexed = false;
        let mut called = false;
        self.primary()?;
        let mut height = self.height;
        loop {
            match self.cur() {
                Some(LParen) => {
                    place = false;
                    called = true;
                    self.chain_at(checkpoint, CallExpr, height, |p| p.arg_list(RParen, true))?;
                }
                Some(LBracket) => {
                    place = false;
                    indexed = true;
                    self.chain_at(checkpoint, IndexExpr, height, |p| {
                        p.arg_list(RBracket, false)
                    })?;
                }
                Some(Dot) => {
                    self.chain_at(checkpoint, FieldExpr, height, |p| {
                        p.bump();
                        match p.cur() {
                            Some(Ident) => {
                                p.bump();
                                if p.is(LParen) {
                                    p.later_slice(p.offset(), "a receiver call");
                                    return None;
                                }
                                Some(())
                            }
                            Some(Dec | Hex | Bin) => {
                                p.later_slice(p.offset(), "a tuple selector");
                                None
                            }
                            _ => {
                                p.syntax_error("expected a field name");
                                None
                            }
                        }
                    })?;
                    self.height = 0;
                }
                _ => break,
            }
            height = height.max(self.height) + 1;
        }
        self.height = height;
        self.place = place;
        self.indexed = indexed && !called;
        Some(())
    }

    /// The arguments between a pair of delimiters, with an optional trailing comma. The
    /// opening delimiter is the one that pairs with `close`.
    pub(crate) fn arg_list(&mut self, close: SyntaxKind, may_be_empty: bool) -> Res {
        let (open, what) = if close == RParen {
            (LParen, "`(`")
        } else {
            (LBracket, "`[`")
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
            p.expect(close, "a closing delimiter")?;
            p.height = height;
            Some(())
        })
    }

    fn primary(&mut self) -> Res {
        let start = self.offset();
        match self.cur() {
            Some(Dec | Hex | Bin | Str | TrueKw | FalseKw) => {
                if matches!(self.cur(), Some(Dec | Hex | Bin))
                    && !Nat::literal_in_bounds(self.text())
                {
                    self.syntax_error("the value of a number is not below 2^65536");
                    return None;
                }
                self.node(Literal, |p| {
                    p.bump();
                    Some(())
                })?;
            }
            Some(Ident) => {
                self.node(NameExpr, |p| {
                    p.bump();
                    Some(())
                })?;
                if self.is(ColonColon) {
                    self.later_slice(self.offset(), "a path");
                    return None;
                }
            }
            Some(LParen) => return self.paren(),
            Some(LBracket) => {
                self.later_slice(start, "an array");
                return None;
            }
            Some(FnKw) => {
                self.later_slice(start, "a function type");
                return None;
            }
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

    /// A parenthesized expression. The unit and the tuple belong to a later slice.
    /// Parentheses make no node of the AST, so they add nothing to the height.
    fn paren(&mut self) -> Res {
        let start = self.offset();
        if self.at_unit_or_tuple() {
            self.later_slice(start, "a unit or a tuple");
            return None;
        }
        self.node(ParenExpr, |p| {
            p.bump();
            p.expr()?;
            p.expect(RParen, "`)`")
        })
    }
}
