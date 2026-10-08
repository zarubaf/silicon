//! Splits `.sil` text into tokens with positions.

use crate::diag::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Open,
    Close,
    Name(String),
    Number(String),
    /// `NAME.PORT`
    Dotted(String, String),
    /// A character that starts no token. The parser reports it when it
    /// reaches it, so an earlier grammar error wins.
    Invalid(String),
    End,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

fn is_name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '$'
}

struct Cursor<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    line: u32,
    col: u32,
}

impl Cursor<'_> {
    fn span(&self) -> Span {
        Span {
            line: self.line,
            col: self.col,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        if c == '\n' {
            self.line = self.line.saturating_add(1);
            self.col = 1;
        } else {
            self.col = self.col.saturating_add(1);
        }
        Some(c)
    }

    fn take_while(&mut self, pred: fn(char) -> bool) -> String {
        let mut text = String::new();
        while let Some(c) = self.peek().filter(|c| pred(*c)) {
            text.push(c);
            self.bump();
        }
        text
    }
}

/// Always ends with `Tok::End`, placed just after the last character.
/// A malformed token becomes `Tok::Invalid`, and lexing stops there.
pub fn lex(src: &str) -> Vec<Token> {
    let mut cur = Cursor {
        chars: src.chars().peekable(),
        line: 1,
        col: 1,
    };
    let mut tokens = Vec::new();
    loop {
        let span = cur.span();
        let tok = match cur.peek() {
            None => {
                tokens.push(Token {
                    tok: Tok::End,
                    span,
                });
                return tokens;
            }
            Some(c) if c.is_whitespace() => {
                cur.bump();
                continue;
            }
            Some(';') => {
                while cur.peek().is_some_and(|c| c != '\n') {
                    cur.bump();
                }
                continue;
            }
            Some('(') => {
                cur.bump();
                Tok::Open
            }
            Some(')') => {
                cur.bump();
                Tok::Close
            }
            Some(c) if c.is_ascii_digit() => {
                let digits = cur.take_while(|c| c.is_ascii_digit());
                if cur.peek().is_some_and(is_name_char) {
                    Tok::Invalid(format!("malformed number `{digits}...`"))
                } else {
                    Tok::Number(digits)
                }
            }
            Some(c) if is_name_start(c) => {
                let head = cur.take_while(is_name_char);
                if cur.peek() == Some('.') {
                    cur.bump();
                    if cur.peek().is_some_and(is_name_start) {
                        Tok::Dotted(head, cur.take_while(is_name_char))
                    } else {
                        Tok::Invalid(format!("expected a port name after `{head}.`"))
                    }
                } else {
                    Tok::Name(head)
                }
            }
            Some(c) => {
                cur.bump();
                Tok::Invalid(format!("unexpected character `{c}`"))
            }
        };
        let stop = matches!(tok, Tok::Invalid(_));
        tokens.push(Token { tok, span });
        if stop {
            tokens.push(Token {
                tok: Tok::End,
                span: cur.span(),
            });
            return tokens;
        }
    }
}
