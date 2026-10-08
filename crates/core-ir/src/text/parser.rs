//! Recursive-descent parser. It checks the grammar only; it resolves no names.

use super::lexer::{Tok, Token, lex};
use super::{
    BINOPS, PREDS, UNOPS, binop_keyword, is_keyword, pred_keyword, syntax_error, unop_keyword,
};
use crate::ast::{
    Conn, Dep, Design, Dir, Expr, Extern, Item, Module, Name, Num, Port, Reset, Stmt, Ty,
};
use crate::diag::{Diagnostic, Span};
use num_bigint::BigUint;

/// Bounds the recursion on hostile input.
const MAX_DEPTH: u32 = 256;

type Parsed<T> = Result<T, Diagnostic>;

/// Parses a `.sil` file. A grammar error is `E001` at the first token that
/// does not match, or at the end of the file.
///
/// # Errors
/// Returns the `E001` diagnostic of the first grammar error.
pub fn parse(src: &str) -> Result<Design, Diagnostic> {
    let mut p = Parser {
        tokens: lex(src),
        pos: 0,
        depth: 0,
    };
    let design = p.design()?;
    if p.peek() != &Tok::End {
        return Err(p.fail("the end of the file"));
    }
    Ok(design)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    depth: u32,
}

impl Parser {
    // The lexer ends every token list with `End`, and `bump` never moves past it.
    fn current(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn peek(&self) -> &Tok {
        &self.current().tok
    }

    fn span(&self) -> Span {
        self.current().span
    }

    /// The token after the current one.
    fn peek_second(&self) -> &Tok {
        &self.tokens[(self.pos + 1).min(self.tokens.len() - 1)].tok
    }

    fn bump(&mut self) -> Token {
        let token = self.current().clone();
        if token.tok != Tok::End {
            self.pos += 1;
        }
        token
    }

    fn fail(&self, expected: &str) -> Diagnostic {
        let token = self.current();
        let found = match &token.tok {
            Tok::Open => "`(`".to_string(),
            Tok::Close => "`)`".to_string(),
            Tok::Name(n) | Tok::Number(n) => format!("`{n}`"),
            Tok::Dotted(a, b) => format!("`{a}.{b}`"),
            Tok::Invalid(message) => return syntax_error(token.span, message.clone()),
            Tok::End => "the end of the file".to_string(),
        };
        syntax_error(token.span, format!("expected {expected}, found {found}"))
    }

    fn open(&mut self) -> Parsed<Span> {
        if self.peek() == &Tok::Open {
            Ok(self.bump().span)
        } else {
            Err(self.fail("`(`"))
        }
    }

    fn close(&mut self) -> Parsed<()> {
        if self.peek() == &Tok::Close {
            self.bump();
            Ok(())
        } else {
            Err(self.fail("`)`"))
        }
    }

    fn keyword(&mut self, word: &str) -> Parsed<()> {
        if self.peek() == &Tok::Name(word.to_string()) {
            self.bump();
            Ok(())
        } else {
            Err(self.fail(&format!("`{word}`")))
        }
    }

    /// The head word of a list, after its `(`.
    fn head(&mut self) -> Parsed<(String, Span)> {
        match self.peek().clone() {
            Tok::Name(word) => Ok((word, self.bump().span)),
            _ => Err(self.fail("a keyword")),
        }
    }

    fn name(&mut self) -> Parsed<Name> {
        match self.peek() {
            Tok::Name(text) if !is_keyword(text) => {
                let token = self.bump();
                match token.tok {
                    Tok::Name(text) => Ok(Name {
                        text,
                        span: token.span,
                    }),
                    _ => Err(self.fail("a name")),
                }
            }
            _ => Err(self.fail("a name")),
        }
    }

    fn number_text(&mut self) -> Parsed<String> {
        match self.peek() {
            Tok::Number(_) => match self.bump().tok {
                Tok::Number(text) => Ok(text),
                _ => Err(self.fail("a number")),
            },
            _ => Err(self.fail("a number")),
        }
    }

    fn number(&mut self) -> Parsed<u32> {
        self.num().map(|n| n.value)
    }

    fn num(&mut self) -> Parsed<Num> {
        let span = self.span();
        let text = self.number_text()?;
        let value = text
            .parse::<u32>()
            .map_err(|_| syntax_error(span, format!("the number `{text}` is too large")))?;
        Ok(Num { value, span })
    }

    fn design(&mut self) -> Parsed<Design> {
        let span = self.open()?;
        self.keyword("design")?;
        let top = self.name()?;
        let mut items = Vec::new();
        while self.peek() != &Tok::Close {
            items.push(self.item()?);
        }
        self.close()?;
        Ok(Design { top, items, span })
    }

    fn item(&mut self) -> Parsed<Item> {
        let span = self.open()?;
        let (word, _) = self.head().map_err(|_| self.fail("`module` or `extern`"))?;
        match word.as_str() {
            "module" => {
                let name = self.name()?;
                let ports = self.ports()?;
                let mut stmts = Vec::new();
                while self.peek() != &Tok::Close {
                    stmts.push(self.stmt()?);
                }
                self.close()?;
                Ok(Item::Module(Module {
                    name,
                    ports,
                    stmts,
                    span,
                }))
            }
            "extern" => {
                let name = self.name()?;
                let ports = self.ports()?;
                let mut deps = Vec::new();
                while self.peek() != &Tok::Close {
                    deps.push(self.dep()?);
                }
                self.close()?;
                Ok(Item::Extern(Extern {
                    name,
                    ports,
                    deps,
                    span,
                }))
            }
            _ => {
                self.pos -= 1;
                Err(self.fail("`module` or `extern`"))
            }
        }
    }

    fn ports(&mut self) -> Parsed<Vec<Port>> {
        let mut ports = Vec::new();
        while self.peek() == &Tok::Open
            && matches!(self.peek_second(), Tok::Name(w) if w == "input" || w == "output")
        {
            let span = self.open()?;
            let (word, _) = self.head()?;
            let dir = if word == "input" {
                Dir::Input
            } else {
                Dir::Output
            };
            let name = self.name()?;
            let ty = self.ty()?;
            self.close()?;
            ports.push(Port {
                dir,
                name,
                ty,
                span,
            });
        }
        Ok(ports)
    }

    fn ty(&mut self) -> Parsed<Ty> {
        if self.peek() == &Tok::Name("clock".to_string()) {
            self.bump();
            return Ok(Ty::Clock);
        }
        if self.peek() != &Tok::Open {
            return Err(self.fail("`clock` or `(bits N)`"));
        }
        Ok(Ty::Bits(self.bits()?))
    }

    /// `(bits N)`
    fn bits(&mut self) -> Parsed<Num> {
        self.open()?;
        self.keyword("bits")?;
        let width = self.num()?;
        self.close()?;
        Ok(width)
    }

    fn dep(&mut self) -> Parsed<Dep> {
        let span = self.open()?;
        self.keyword("deps")?;
        let out = self.name()?;
        self.open()?;
        let mut ins = Vec::new();
        while self.peek() != &Tok::Close {
            ins.push(self.name()?);
        }
        self.close()?;
        self.close()?;
        Ok(Dep { out, ins, span })
    }

    fn stmt(&mut self) -> Parsed<Stmt> {
        let span = self.open()?;
        let (word, _) = self.head()?;
        let stmt = match word.as_str() {
            "let" => {
                let name = self.name()?;
                let width = self.bits()?;
                let expr = self.expr()?;
                Stmt::Let {
                    name,
                    width,
                    expr,
                    span,
                }
            }
            "reg" => {
                let name = self.name()?;
                let width = self.bits()?;
                let clk = self.name()?;
                let reset = if self.peek() == &Tok::Open {
                    Some(self.reset()?)
                } else {
                    None
                };
                Stmt::Reg {
                    name,
                    width,
                    clk,
                    reset,
                    span,
                }
            }
            "next" => Stmt::Next {
                reg: self.name()?,
                expr: self.expr()?,
                span,
            },
            "mem" => {
                let name = self.name()?;
                let width = self.bits()?;
                let depth = self.num()?;
                let clk = self.name()?;
                Stmt::Mem {
                    name,
                    width,
                    depth,
                    clk,
                    span,
                }
            }
            "write" => {
                let mem = self.name()?;
                let port = self.number()?;
                let addr = self.expr()?;
                let data = self.expr()?;
                let en = self.expr()?;
                Stmt::Write {
                    mem,
                    port,
                    addr,
                    data,
                    en,
                    span,
                }
            }
            "inst" => {
                let name = self.name()?;
                let module = self.name()?;
                let mut conns = Vec::new();
                while self.peek() != &Tok::Close {
                    let span = self.open()?;
                    let port = self.name()?;
                    let expr = self.expr()?;
                    self.close()?;
                    conns.push(Conn { port, expr, span });
                }
                Stmt::Inst {
                    name,
                    module,
                    conns,
                    span,
                }
            }
            "assign" => Stmt::Assign {
                out: self.name()?,
                expr: self.expr()?,
                span,
            },
            _ => {
                self.pos -= 1;
                return Err(self.fail("a statement keyword"));
            }
        };
        self.close()?;
        Ok(stmt)
    }

    fn reset(&mut self) -> Parsed<Reset> {
        let span = self.open()?;
        self.keyword("reset")?;
        self.keyword("sync")?;
        let signal = self.expr()?;
        let value = self.expr()?;
        self.close()?;
        Ok(Reset {
            signal,
            value,
            span,
        })
    }

    fn expr(&mut self) -> Parsed<Expr> {
        self.expr_inner()
    }

    fn boxed(&mut self) -> Parsed<Box<Expr>> {
        self.expr().map(Box::new)
    }

    fn expr_inner(&mut self) -> Parsed<Expr> {
        match self.peek().clone() {
            Tok::Name(_) => Ok(Expr::Ref(self.name()?)),
            Tok::Dotted(inst, port) => {
                let span = self.span();
                if is_keyword(&inst) || is_keyword(&port) {
                    return Err(self.fail("a name"));
                }
                self.bump();
                let inst_len = inst.chars().fold(0u32, |n, _| n.saturating_add(1));
                let port_span = Span {
                    line: span.line,
                    col: span.col.saturating_add(inst_len).saturating_add(1),
                };
                Ok(Expr::InstOut {
                    inst: Name { text: inst, span },
                    port: Name {
                        text: port,
                        span: port_span,
                    },
                    span,
                })
            }
            Tok::Open => self.compound(),
            _ => Err(self.fail("an expression")),
        }
    }

    fn compound(&mut self) -> Parsed<Expr> {
        if self.depth >= MAX_DEPTH {
            return Err(syntax_error(
                self.span(),
                "expression nesting is too deep".to_string(),
            ));
        }
        self.depth += 1;
        let result = self.compound_inner();
        self.depth -= 1;
        result
    }

    fn compound_inner(&mut self) -> Parsed<Expr> {
        let span = self.open()?;
        let (word, _) = self.head().map_err(|_| self.fail("an operation"))?;
        let word = word.as_str();
        let expr = if word == "const" {
            let width = self.num()?;
            let value_span = self.span();
            let digits = self.number_text()?;
            let value = BigUint::parse_bytes(digits.as_bytes(), 10).unwrap_or_default();
            Expr::Const {
                width,
                value,
                value_span,
                span,
            }
        } else if let Some(op) = UNOPS.iter().find(|op| unop_keyword(**op) == word) {
            Expr::Unary {
                op: *op,
                arg: self.boxed()?,
                span,
            }
        } else if let Some(op) = BINOPS.iter().find(|op| binop_keyword(**op) == word) {
            Expr::Binary {
                op: *op,
                lhs: self.boxed()?,
                rhs: self.boxed()?,
                span,
            }
        } else if word == "icmp" {
            let pred = self.pred()?;
            Expr::Icmp {
                pred,
                lhs: self.boxed()?,
                rhs: self.boxed()?,
                span,
            }
        } else if word == "mux" {
            Expr::Mux {
                cond: self.boxed()?,
                then: self.boxed()?,
                els: self.boxed()?,
                span,
            }
        } else if word == "extract" {
            Expr::Extract {
                arg: self.boxed()?,
                lo: self.number()?,
                width: self.num()?,
                span,
            }
        } else if word == "replicate" {
            Expr::Replicate {
                arg: self.boxed()?,
                count: self.num()?,
                span,
            }
        } else if word == "read" {
            Expr::Read {
                mem: self.name()?,
                addr: self.boxed()?,
                span,
            }
        } else {
            self.pos -= 1;
            return Err(self.fail("an operation"));
        };
        self.close()?;
        Ok(expr)
    }

    fn pred(&mut self) -> Parsed<crate::Pred> {
        if let Tok::Name(word) = self.peek()
            && let Some(pred) = PREDS.iter().find(|p| pred_keyword(**p) == *word)
        {
            let pred = *pred;
            self.bump();
            return Ok(pred);
        }
        Err(self.fail("a comparison predicate"))
    }
}
