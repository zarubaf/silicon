// SPDX-License-Identifier: Apache-2.0
//! The grammar of types and expressions, with the precedence of the grammar file.
#![allow(clippy::enum_glob_use)] // The grammar names token kinds on almost every line.

use crate::ast::Builtin;
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
            Some(At) => self.builtin(BuiltinType)?,
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
                    self.later_slice(self.offset(), "a type function call");
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

    /// An expression: a conditional, a `match`, or the operators by precedence. A `match` is at
    /// the level of the conditional.
    pub(crate) fn expr(&mut self) -> Res {
        let start = self.offset();
        self.outermost(start, |p| {
            if p.is(MatchKw) {
                let res = p.match_form();
                p.ast_place = false;
                res
            } else if p.is(IfKw) {
                let res = p.cond_form();
                p.ast_place = false;
                res
            } else {
                p.binary(0)
            }
        })
    }

    /// `match (x) { p => e, }`. A `,` can end the arms. The height is 1 plus the largest height
    /// of the scrutinee and the arm expressions: a pattern adds none.
    fn match_form(&mut self) -> Res {
        self.node(MatchExpr, |p| {
            p.bump();
            p.expect(LParen, "`(`")?;
            p.expr()?;
            let mut height = p.height;
            p.expect(RParen, "`)`")?;
            p.expect(LBrace, "`{`")?;
            while !p.eat(RBrace) {
                p.node(MatchArm, |p| {
                    p.pattern()?;
                    p.expr()
                })?;
                height = height.max(p.height);
                if p.eat(RBrace) {
                    break;
                }
                p.expect(Comma, "`,` or `}`")?;
            }
            p.height = height + 1;
            Some(())
        })
    }

    /// `S001` with the pattern text at the current token.
    fn bad_pattern(&mut self) -> Res {
        self.syntax_error(
            "expected a pattern: an integer, `true`, `false`, `E::V(..)`, or `_`; compare with \
             a constant in an `if`",
        );
        None
    }

    /// A pattern and the `=>` after it. A `=>` is in the arm, not in the pattern.
    fn pattern(&mut self) -> Res {
        self.node(Pattern, |p| match p.cur() {
            Some(Dec | Hex | Bin | TrueKw | FalseKw) => {
                p.bump();
                Some(())
            }
            Some(Minus) => {
                p.bump();
                if !matches!(p.cur(), Some(Dec | Hex | Bin)) {
                    return p.bad_pattern();
                }
                p.bump();
                Some(())
            }
            Some(Ident) if p.cur_text() == "_" => {
                p.bump();
                Some(())
            }
            Some(Ident) => p.variant_pattern(),
            _ => p.bad_pattern(),
        })?;
        if self.eat(FatArrow) {
            Some(())
        } else {
            self.bad_pattern()
        }
    }

    /// `E::V` and its binders: a name or `_` for each payload value.
    fn variant_pattern(&mut self) -> Res {
        self.bump();
        if !self.eat(ColonColon) {
            return self.bad_pattern();
        }
        if self.is(Ident) && self.cur_text() == "_" {
            self.syntax_error(
                "a variant pattern names a variant, not `_`; write `_` alone to match each \
                 other value",
            );
            return None;
        }
        if !self.eat(Ident) {
            return self.bad_pattern();
        }
        if self.is(ColonColon) {
            self.package_path(self.offset());
            return None;
        }
        if !self.eat(LParen) {
            return Some(());
        }
        loop {
            if self.eat(RParen) {
                return Some(());
            }
            if !self.eat(Ident) {
                return self.bad_pattern();
            }
            if self.eat(RParen) {
                return Some(());
            }
            if !self.eat(Comma) {
                return self.bad_pattern();
            }
        }
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
            self.ast_place = false;
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
            let res = self.fn_chain(FnTypeExpr);
            self.ast_place = false;
            res
        } else {
            self.postfix_expr()
        };
        if ops > 0 {
            self.ast_place = false;
        }
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
        let at_builtin = self.is(At);
        let mut place = self.is(Ident) && self.next() != Some(ColonColon);
        self.primary()?;
        if at_builtin {
            place = self.ast_place;
        }
        let mut ast_place = self.ast_place;
        let mut height = self.height;
        loop {
            match self.cur() {
                Some(LParen) => {
                    place = false;
                    ast_place = false;
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
                    ast_place = false;
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
        self.ast_place = ast_place;
        Some(())
    }

    /// The arguments between a pair of delimiters, with an optional trailing comma. The
    /// opening delimiter is the one that pairs with `close`.
    pub(crate) fn arg_list(&mut self, close: SyntaxKind, may_be_empty: bool) -> Res {
        self.arg_list_with(close, may_be_empty, |_, _| {})
    }

    /// Like `arg_list`, and `each` sees the start offset of each argument after its parse.
    fn arg_list_with(
        &mut self,
        close: SyntaxKind,
        may_be_empty: bool,
        mut each: impl FnMut(&Self, usize),
    ) -> Res {
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
                    let start = p.offset();
                    p.expr()?;
                    each(p, start);
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

    /// A primary expression. It sets `ast_place`: a name is a place, a group has the place of
    /// its expression, and a builtin sets its own.
    fn primary(&mut self) -> Res {
        let name = self.is(Ident) && self.next() != Some(ColonColon);
        let keeps = self.is(At) || (self.is(LParen) && !self.at_unit_or_tuple());
        self.ast_place = false;
        self.primary_form()?;
        if name {
            self.ast_place = true;
        } else if !keeps {
            self.ast_place = false;
        }
        Some(())
    }

    fn primary_form(&mut self) -> Res {
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
            Some(At) => return self.builtin(BuiltinExpr),
            _ => {
                self.syntax_error("expected an expression");
                return None;
            }
        }
        self.height = 1;
        Some(())
    }

    /// `@` where no builtin node can stand: a builtin of a later phase is `S004` at the `@`,
    /// and any other name after `@` is `S001` "Not a builtin" at that name.
    fn later_builtin(&mut self) -> Res {
        let name = self.next_text();
        if self.next() != Some(Ident) {
            self.syntax_error_at(self.offset_of(1), "expected a builtin name");
        } else if BUILTINS.contains(&name) {
            self.later_slice(self.offset(), "a builtin");
        } else {
            self.syntax_error_at(
                self.offset_of(1),
                &format!(
                    "`@{}` is not a builtin; use `@TypeOf`, `@typeInfo`, `@Struct`, `@field`, or \
                     `@ports`",
                    str_text(name)
                ),
            );
        }
        None
    }

    /// `@TypeOf(x)`, `@typeInfo(T)`, `@Struct(fs)`, or `@field(x, k)`, a primary, and a builtin in
    /// a type position. The node has the `kind`. It reads all operands, then checks their number
    /// at the name, then the form of the operand of `@TypeOf` at its first token. Thus a syntax
    /// error in an operand comes first. The operand of `@typeInfo` and of `@Struct` is any
    /// expression. `@ports` is `S004`.
    fn builtin(&mut self, kind: SyntaxKind) -> Res {
        let known = (self.next() == Some(Ident))
            .then(|| Builtin::of_name(self.next_text()))
            .flatten();
        let Some(builtin) = known else {
            return self.later_builtin();
        };
        let name_offset = self.offset_of(1);
        let mut operands = Vec::new();
        self.node(kind, |p| {
            p.bump();
            p.bump();
            p.arg_list_with(RParen, true, |p, start| operands.push((start, p.ast_place)))
        })?;
        if operands.len() != builtin.arity() {
            self.syntax_error_at(
                name_offset,
                &format!(
                    "`{}` takes {} argument(s), but it has {}; write `{}`",
                    builtin.at_name(),
                    builtin.arity(),
                    operands.len(),
                    builtin.form()
                ),
            );
            return None;
        }
        if builtin == Builtin::TypeOf
            && let Some(&(start, false)) = operands.first()
        {
            self.syntax_error_at(
                start,
                &format!(
                    "`{}` takes a name or a selection of a name; bind the value with `let` and \
                     pass the name",
                    builtin.at_name()
                ),
            );
            return None;
        }
        self.height += 1;
        // The `@field` of a place is a place, so it can be a target.
        self.ast_place = builtin == Builtin::Field && operands.first().is_some_and(|o| o.1);
        Some(())
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

/// A string in a message: at most 64 characters, then a note of the full length.
fn str_text(m: &str) -> String {
    match m.char_indices().nth(64) {
        None => m.to_owned(),
        Some((cut, _)) => format!("{}... ({} characters)", &m[..cut], m.chars().count()),
    }
}
