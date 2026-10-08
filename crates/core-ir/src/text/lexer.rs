//! Splits `.sil` text into tokens with positions.

use crate::diag::Span;
use num_bigint::BigUint;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Open,
    Close,
    Name(String),
    Number(BigUint),
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

/// A token holds only these characters; one outside the set is an error at
/// that character.
fn is_token_char(c: char) -> bool {
    is_name_char(c) || c == '.'
}

fn is_name(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(is_name_start) && chars.all(is_name_char)
}

/// The value of a run of decimal digits. Nine digits at a time keep the
/// multiplications few.
fn from_digits(digits: &str) -> BigUint {
    digits
        .as_bytes()
        .chunks(9)
        .fold(BigUint::default(), |acc, chunk| {
            let (value, scale) = chunk.iter().fold((0u32, 1u32), |(value, scale), byte| {
                (value * 10 + u32::from(byte - b'0'), scale * 10)
            });
            acc * scale + value
        })
}

/// A token of valid characters is a name, `NAME.PORT`, or a number. Anything
/// else is invalid at the start of the token.
fn classify(text: &str) -> Tok {
    if is_name(text) {
        return Tok::Name(text.to_string());
    }
    if !text.is_empty() && text.chars().all(|c| c.is_ascii_digit()) {
        return Tok::Number(from_digits(text));
    }
    if let Some((head, port)) = text.split_once('.')
        && is_name(head)
        && is_name(port)
    {
        return Tok::Dotted(head.to_string(), port.to_string());
    }
    Tok::Invalid(format!("malformed token `{text}`"))
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

    /// Takes the maximal run of characters that are no whitespace, no
    /// parenthesis, and no comment start. Also returns the position of the
    /// first character outside the token set.
    fn take_token(&mut self) -> (String, Option<Span>) {
        let mut text = String::new();
        let mut bad = None;
        while let Some(c) = self
            .peek()
            .filter(|c| !matches!(c, ' ' | '\t' | '\r' | '\n' | '(' | ')' | ';'))
        {
            if bad.is_none() && !is_token_char(c) {
                bad = Some(self.span());
            }
            text.push(c);
            self.bump();
        }
        (text, bad)
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
        let mut span = cur.span();
        let tok = match cur.peek() {
            None => {
                tokens.push(Token {
                    tok: Tok::End,
                    span,
                });
                return tokens;
            }
            Some(' ' | '\t' | '\r' | '\n') => {
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
            Some(_) => {
                let (text, bad) = cur.take_token();
                match bad {
                    Some(at) => {
                        span = at;
                        Tok::Invalid("unexpected character".to_string())
                    }
                    None => classify(&text),
                }
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
