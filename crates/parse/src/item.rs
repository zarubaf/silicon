// SPDX-License-Identifier: Apache-2.0
//! The grammar of items: constants, functions, and modules.
#![allow(clippy::enum_glob_use)] // The grammar names token kinds on almost every line.

use crate::parser::{Parser, Res};
use syntax::SyntaxKind::{self, *};

/// Whether a token starts an item of any slice.
fn starts_item(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        ConstKw | FnKw | ModuleKw | ComptimeKw | ImportKw | PubKw | TypeKw | StructKw | ExternKw
    )
}

impl Parser<'_> {
    pub(crate) fn source(&mut self) {
        while let Some(kind) = self.cur() {
            let before = self.offset();
            self.item(kind);
            // A parse function that fails at once consumes nothing.
            if self.offset() == before {
                self.start(ErrorNode);
                self.bump();
                self.skip_item();
                self.finish_node();
            }
        }
    }

    fn item(&mut self, kind: SyntaxKind) {
        let res = match kind {
            ConstKw => self.node(ConstItem, Self::const_item),
            FnKw => self.node(FnItem, Self::fn_item),
            ComptimeKw if self.next() == Some(FnKw) => self.node(FnItem, Self::fn_item),
            ComptimeKw => {
                self.syntax_error_at(self.offset_of(1), "expected `fn`");
                None
            }
            ModuleKw => self.node(ModuleItem, Self::module_item),
            ImportKw | PubKw | TypeKw | StructKw | ExternKw => {
                self.later_slice(self.offset(), "this item");
                None
            }
            _ => {
                self.syntax_error("expected an item");
                None
            }
        };
        if res.is_none() {
            self.start(ErrorNode);
            self.skip_item();
            self.finish_node();
        }
    }

    /// Skips to the end of the item: after its `;` or its closing brace, or before the
    /// next item.
    fn skip_item(&mut self) {
        let mut braces = 0;
        while let Some(kind) = self.cur() {
            match kind {
                LBrace => braces += 1,
                RBrace if braces > 0 => {
                    braces -= 1;
                    self.bump();
                    if braces == 0 {
                        return;
                    }
                    continue;
                }
                Semi if braces == 0 => {
                    self.bump();
                    return;
                }
                _ if braces == 0 && starts_item(kind) => return,
                _ => {}
            }
            self.bump();
        }
    }

    fn const_item(&mut self) -> Res {
        self.bump();
        self.expect(Ident, "a name")?;
        self.expect(Colon, "`:`")?;
        self.type_expr()?;
        self.expect(Eq, "`=`")?;
        self.expr()?;
        self.expect(Semi, "`;`")
    }

    fn fn_item(&mut self) -> Res {
        let plain = !self.eat(ComptimeKw);
        self.bump();
        self.expect(Ident, "a name")?;
        self.param_list(false)?;
        self.expect(Arrow, "`->`")?;
        self.type_expr()?;
        self.in_plain_fn = plain;
        let body = self.block();
        self.in_plain_fn = false;
        body
    }

    fn module_item(&mut self) -> Res {
        self.bump();
        self.expect(Ident, "a name")?;
        self.param_list(true)?;
        if self.is(DomainsKw) {
            self.domains_clause()?;
        }
        if self.is(ConformsKw) {
            self.later_slice(self.offset(), "a contract");
            return None;
        }
        self.block()
    }

    /// The parameters. A module parameter must have `comptime`.
    fn param_list(&mut self, module: bool) -> Res {
        self.node(ParamList, |p| {
            p.expect(LParen, "`(`")?;
            while !p.is(RParen) {
                p.param(module)?;
                if !p.eat(Comma) {
                    break;
                }
            }
            p.expect(RParen, "`)`")
        })
    }

    fn param(&mut self, module: bool) -> Res {
        self.node(Param, |p| {
            if p.is(MutKw) && !module {
                p.later_slice(p.offset(), "a `mut` parameter");
                return None;
            }
            if module {
                p.expect(ComptimeKw, "`comptime`")?;
            } else {
                p.eat(ComptimeKw);
            }
            p.expect(Ident, "a name")?;
            p.expect(Colon, "`:`")?;
            p.type_expr()
        })
    }

    /// `domains(d)`. A second name needs the clock domains of a later slice.
    fn domains_clause(&mut self) -> Res {
        self.node(DomainsClause, |p| {
            p.bump();
            p.expect(LParen, "`(`")?;
            let mut names = 0;
            while !p.is(RParen) {
                // Only a name after the comma is a second domain.
                if names == 1 && p.is(Ident) {
                    p.later_slice(p.offset(), "a second clock domain");
                    return None;
                }
                p.expect(Ident, "a domain name")?;
                names += 1;
                if !p.eat(Comma) {
                    break;
                }
            }
            p.expect(RParen, "`)`")
        })
    }
}
