//! The grammar of blocks and statements.
#![allow(clippy::enum_glob_use)] // The grammar names token kinds on almost every line.

use crate::parser::{Parser, Res};
use syntax::SyntaxKind::{self, *};

/// Whether a token starts a statement of any slice, other than an expression.
fn starts_stmt(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        LetKw
            | RegKw
            | WireKw
            | MemKw
            | TypeKw
            | InputKw
            | OutputKw
            | InstanceKw
            | ReturnKw
            | ComptimeKw
    )
}

impl Parser<'_> {
    /// A block: statements between braces. Statements recover from an error, so the block
    /// always ends at its closing brace or at the end of the input.
    pub(crate) fn block(&mut self) -> Res {
        self.block_level(|p| {
            p.node(Block, |p| {
                p.expect(LBrace, "`{`")?;
                while !p.is(RBrace) && p.cur().is_some() {
                    let before = p.offset();
                    let first = p.cur();
                    if p.stmt().is_some() {
                        continue;
                    }
                    // The failed statement may have consumed nothing, so the loop must move.
                    if p.offset() == before {
                        p.start(ErrorNode);
                        p.bump();
                        p.finish_node();
                        if first == Some(Semi) {
                            continue;
                        }
                    }
                    p.skip_stmt();
                }
                p.expect(RBrace, "`}`")
            })
        })
    }

    /// Skips to the end of the statement: after its `;`, or before the `}` of the block.
    fn skip_stmt(&mut self) {
        self.start(ErrorNode);
        let mut braces = 0;
        while let Some(kind) = self.cur() {
            match kind {
                LBrace => braces += 1,
                RBrace if braces == 0 => break,
                RBrace => braces -= 1,
                Semi if braces == 0 => {
                    self.bump();
                    break;
                }
                _ if braces == 0 && starts_stmt(kind) => break,
                _ => {}
            }
            self.bump();
        }
        self.finish_node();
    }

    fn stmt(&mut self) -> Res {
        match self.cur()? {
            LetKw => self.node(LetStmt, Self::let_stmt),
            RegKw => self.node(RegStmt, Self::reg_stmt),
            WireKw => self.node(WireStmt, |p| p.declaration(true)),
            InputKw => self.node(InputStmt, Self::port),
            OutputKw => self.node(OutputStmt, Self::port),
            InstanceKw => self.node(InstStmt, Self::inst_stmt),
            ReturnKw => self.node(ReturnStmt, Self::return_stmt),
            ComptimeKw => self.comptime_stmt(),
            MemKw | TypeKw => {
                self.later_slice(self.offset(), "this statement");
                None
            }
            LBrace => self.block(),
            Error => {
                self.bump();
                Some(())
            }
            _ => self.expr_or_assign(),
        }
    }

    /// The `in d` domain annotation belongs to the clock domains of a later slice.
    fn no_domain_annotation(&mut self) -> Res {
        if self.is(InKw) {
            self.later_slice(self.offset(), "a domain annotation");
            None
        } else {
            Some(())
        }
    }

    fn let_stmt(&mut self) -> Res {
        self.bump();
        self.eat(MutKw);
        self.expect(Ident, "a name")?;
        if self.eat(Colon) {
            self.type_expr()?;
        }
        self.expect(Eq, "`=`")?;
        self.expr()?;
        self.expect(Semi, "`;`")
    }

    fn reg_stmt(&mut self) -> Res {
        self.declaration(false)
    }

    /// `reg x: T = e;` or `wire x: T;`
    fn declaration(&mut self, wire: bool) -> Res {
        self.bump();
        self.expect(Ident, "a name")?;
        self.expect(Colon, "`:`")?;
        self.type_expr()?;
        self.no_domain_annotation()?;
        if !wire {
            self.expect(Eq, "`=`")?;
            self.expr()?;
        }
        self.expect(Semi, "`;`")
    }

    /// `input x: T;` or `output x: T;`
    fn port(&mut self) -> Res {
        self.bump();
        self.expect(Ident, "a name")?;
        if self.is(LBracket) {
            self.later_slice(self.offset(), "a port family");
            return None;
        }
        self.expect(Colon, "`:`")?;
        self.type_expr()?;
        self.no_domain_annotation()?;
        if self.is(AsKw) {
            self.later_slice(self.offset(), "a key with `as`");
            return None;
        }
        self.expect(Semi, "`;`")
    }

    fn inst_stmt(&mut self) -> Res {
        self.bump();
        self.expect(Ident, "a name")?;
        self.expect(Eq, "`=`")?;
        self.expect(Ident, "a module name")?;
        if self.is(ColonColon) {
            self.later_slice(self.offset(), "a path");
            return None;
        }
        let start = self.offset();
        self.arg_list(RParen, true, start)?;
        if self.is(WithKw) {
            self.later_slice(self.offset(), "a domain map");
            return None;
        }
        self.expect(Semi, "`;`")
    }

    fn return_stmt(&mut self) -> Res {
        self.bump();
        if !self.is(Semi) {
            self.expr()?;
        }
        self.expect(Semi, "`;`")
    }

    /// `comptime if` or `comptime for`.
    fn comptime_stmt(&mut self) -> Res {
        match self.next() {
            Some(IfKw) => self.node(CtIfStmt, |p| {
                p.bump();
                p.bump();
                p.expect(LParen, "`(`")?;
                p.expr()?;
                p.expect(RParen, "`)`")?;
                p.block()?;
                if p.eat(ElseKw) {
                    p.block()?;
                }
                Some(())
            }),
            Some(ForKw) => self.node(CtForStmt, |p| {
                p.bump();
                p.bump();
                p.expect(Ident, "a name")?;
                p.expect(InKw, "`in`")?;
                p.expr()?;
                p.expect(DotDot, "`..`")?;
                p.expr()?;
                p.block()
            }),
            _ => {
                self.syntax_error_at(self.offset_of(1), "expected `if` or `for`");
                None
            }
        }
    }

    /// An assignment, a connection, or an expression statement. A statement that starts with
    /// a name parses its postfix form first, because it can be a place.
    fn expr_or_assign(&mut self) -> Res {
        if !self.is(Ident) {
            return self.node(ExprStmt, |p| {
                p.expr()?;
                p.expect(Semi, "`;`")
            });
        }
        let start = self.offset();
        if self.at_later_place() {
            self.later_slice(start, "a place with an index or a tuple selector");
            return None;
        }
        let checkpoint = self.checkpoint();
        self.postfix_expr()?;
        let (place, indexed) = (self.place, self.indexed);
        if let Some(op @ (Eq | ColonEq)) = self.cur() {
            if !place {
                if indexed {
                    self.later_slice(start, "a place with an index");
                } else {
                    self.syntax_error("expected `;`");
                }
                return None;
            }
            let kind = if op == ColonEq {
                ConnectStmt
            } else {
                AssignStmt
            };
            return self.node_at(checkpoint, kind, |p| {
                p.bump();
                p.expr()?;
                p.expect(Semi, "`;`")
            });
        }
        self.climb(checkpoint, start, 0)?;
        self.node_at(checkpoint, ExprStmt, |p| p.expect(Semi, "`;`"))
    }
}
