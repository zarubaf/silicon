//! The lexer: text to tokens with byte ranges, lossless for every input.

use crate::SyntaxKind;
use std::ops::Range;

/// The code of every lexical error.
const LEX_CODE: &str = "S001";

/// A token: its kind and its byte range in the input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: SyntaxKind,
    pub range: Range<usize>,
}

/// A lexical error as data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    /// The error code, `S001`.
    pub code: &'static str,
    /// The byte offset of the start of the offending token.
    pub offset: usize,
    pub message: &'static str,
}

/// The result of lexing: the tokens cover the input without gap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lexed {
    pub tokens: Vec<Token>,
    pub errors: Vec<LexError>,
}

/// Splits the input into tokens. The texts of the tokens, joined, equal the input.
#[must_use]
pub fn lex(input: &str) -> Lexed {
    let mut lexer = Lexer { input, pos: 0 };
    let mut out = Lexed {
        tokens: Vec::new(),
        errors: Vec::new(),
    };
    while lexer.pos < input.len() {
        let start = lexer.pos;
        let (kind, message) = lexer.next_token();
        debug_assert!(lexer.pos > start && input.is_char_boundary(lexer.pos));
        if let Some(message) = message {
            out.errors.push(LexError {
                code: LEX_CODE,
                offset: start,
                message,
            });
        }
        out.tokens.push(Token {
            kind,
            range: start..lexer.pos,
        });
    }
    out
}

/// Whitespace is space, tab, CR, and LF only. Every other character, also U+FEFF and
/// Unicode whitespace, is an invalid character, as in the Lean lexer.
fn is_whitespace(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n')
}

struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

/// Operators, longest first within the same first character.
const OPERATORS: &[(&str, SyntaxKind)] = &[
    (":=", SyntaxKind::ColonEq),
    ("::", SyntaxKind::ColonColon),
    ("->", SyntaxKind::Arrow),
    ("..", SyntaxKind::DotDot),
    ("+%", SyntaxKind::PlusPercent),
    ("-%", SyntaxKind::MinusPercent),
    ("*%", SyntaxKind::StarPercent),
    ("==", SyntaxKind::EqEq),
    ("!=", SyntaxKind::BangEq),
    ("<=", SyntaxKind::LtEq),
    (">=", SyntaxKind::GtEq),
    ("<<", SyntaxKind::Shl),
    (">>", SyntaxKind::Shr),
    ("&&", SyntaxKind::AmpAmp),
    ("||", SyntaxKind::PipePipe),
    ("(", SyntaxKind::LParen),
    (")", SyntaxKind::RParen),
    ("{", SyntaxKind::LBrace),
    ("}", SyntaxKind::RBrace),
    ("[", SyntaxKind::LBracket),
    ("]", SyntaxKind::RBracket),
    (",", SyntaxKind::Comma),
    (";", SyntaxKind::Semi),
    (":", SyntaxKind::Colon),
    (".", SyntaxKind::Dot),
    ("=", SyntaxKind::Eq),
    ("<", SyntaxKind::Lt),
    (">", SyntaxKind::Gt),
    ("+", SyntaxKind::Plus),
    ("-", SyntaxKind::Minus),
    ("*", SyntaxKind::Star),
    ("/", SyntaxKind::Slash),
    ("%", SyntaxKind::Percent),
    ("&", SyntaxKind::Amp),
    ("|", SyntaxKind::Pipe),
    ("^", SyntaxKind::Caret),
    ("~", SyntaxKind::Tilde),
    ("!", SyntaxKind::Bang),
    ("@", SyntaxKind::At),
];

type Scanned = (SyntaxKind, Option<&'static str>);

impl Lexer<'_> {
    fn rest(&self) -> &str {
        &self.input[self.pos..]
    }

    /// Advances over the longest prefix of the rest whose characters satisfy `pred`.
    fn eat_while(&mut self, pred: impl Fn(char) -> bool) {
        let len = self.rest().find(|c| !pred(c)).unwrap_or(self.rest().len());
        self.pos += len;
    }

    fn next_token(&mut self) -> Scanned {
        let rest = self.rest();
        let Some(first) = rest.chars().next() else {
            return (SyntaxKind::Error, None);
        };
        if is_whitespace(first) {
            self.eat_while(is_whitespace);
            return (SyntaxKind::Whitespace, None);
        }
        if rest.starts_with("//") {
            self.eat_while(|c| c != '\n');
            return (SyntaxKind::LineComment, None);
        }
        if rest.starts_with("/*") {
            return self.block_comment();
        }
        if first == '"' {
            return self.string();
        }
        if first.is_ascii_digit() {
            return self.number();
        }
        if first.is_ascii_alphabetic() || first == '_' {
            let start = self.pos;
            self.eat_while(|c| c.is_ascii_alphanumeric() || c == '_');
            let text = &self.input[start..self.pos];
            return (SyntaxKind::keyword(text).unwrap_or(SyntaxKind::Ident), None);
        }
        if let Some((text, kind)) = OPERATORS.iter().find(|(text, _)| rest.starts_with(text)) {
            self.pos += text.len();
            return (*kind, None);
        }
        self.pos += first.len_utf8();
        (SyntaxKind::Error, Some("invalid character"))
    }

    fn block_comment(&mut self) -> Scanned {
        if let Some(end) = self.rest()[2..].find("*/") {
            self.pos += 2 + end + 2;
            (SyntaxKind::BlockComment, None)
        } else {
            self.pos = self.input.len();
            (SyntaxKind::Error, Some("unterminated comment"))
        }
    }

    fn number(&mut self) -> Scanned {
        let rest = self.rest();
        let radix = |prefix: &str, digit: fn(&char) -> bool| {
            let body = rest.strip_prefix(prefix)?;
            let len = body.find(|c: char| !digit(&c)).unwrap_or(body.len());
            (len > 0).then_some(prefix.len() + len)
        };
        let hex = |c: &char| c.is_ascii_hexdigit();
        let bin = |c: &char| matches!(c, '0' | '1');
        if let Some(len) = radix("0x", hex) {
            self.pos += len;
            return (SyntaxKind::Hex, None);
        }
        if let Some(len) = radix("0b", bin) {
            self.pos += len;
            return (SyntaxKind::Bin, None);
        }
        self.eat_while(|c| c.is_ascii_digit());
        (SyntaxKind::Dec, None)
    }

    /// A string ends at its closing quote. An invalid escape or a control character makes
    /// the token an error. A string stops at a line feed, which no string can contain.
    fn string(&mut self) -> Scanned {
        let mut chars = self.rest().char_indices().skip(1);
        let mut bad = false;
        while let Some((i, c)) = chars.next() {
            match c {
                '"' => {
                    self.pos += i + 1;
                    return if bad {
                        (SyntaxKind::Error, Some("invalid character in string"))
                    } else {
                        (SyntaxKind::Str, None)
                    };
                }
                '\\' => match chars.next() {
                    Some((_, '"' | '\\' | 'n' | 'r' | 't')) => {}
                    Some((_, '\n')) | None => {
                        self.pos += i + 1;
                        return (SyntaxKind::Error, Some("unterminated string"));
                    }
                    Some(_) => bad = true,
                },
                '\n' => {
                    self.pos += i;
                    return (SyntaxKind::Error, Some("unterminated string"));
                }
                c if c.is_control() => bad = true,
                _ => {}
            }
        }
        self.pos = self.input.len();
        (SyntaxKind::Error, Some("unterminated string"))
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::enum_glob_use)]
    use super::*;
    use proptest::prelude::*;

    fn kinds(input: &str) -> Vec<SyntaxKind> {
        lex(input)
            .tokens
            .iter()
            .map(|t| t.kind)
            .filter(|k| *k != SyntaxKind::Whitespace)
            .collect()
    }

    #[test]
    fn keywords_and_identifiers() {
        assert_eq!(kinds("module"), [SyntaxKind::ModuleKw]);
        assert_eq!(kinds("modules _a1"), [SyntaxKind::Ident, SyntaxKind::Ident]);
        assert_eq!(
            kinds("true false"),
            [SyntaxKind::TrueKw, SyntaxKind::FalseKw]
        );
    }

    #[test]
    fn every_keyword_of_the_grammar() {
        let words = "import as pub const type struct comptime fn module extern let mut return \
                     if else for in conforms using true false reg wire mem input output \
                     instance domains with";
        let lexed = kinds(words);
        assert_eq!(lexed.len(), 29);
        assert!(lexed.iter().all(|k| format!("{k:?}").ends_with("Kw")));
    }

    #[test]
    fn only_four_characters_are_whitespace() {
        assert_eq!(kinds(" \t\r\n1 \n"), [SyntaxKind::Dec]);
        for c in ['\u{feff}', '\u{a0}', '\u{85}', '\u{2003}', '\u{b}', '\u{c}'] {
            let input = format!("1{c}2");
            let lexed = lex(&input);
            assert_eq!(
                lexed.tokens.iter().map(|t| t.kind).collect::<Vec<_>>(),
                [SyntaxKind::Dec, SyntaxKind::Error, SyntaxKind::Dec],
                "{c:?}"
            );
            assert_eq!(lexed.errors.len(), 1);
            assert_eq!((lexed.errors[0].code, lexed.errors[0].offset), ("S001", 1));
        }
    }

    #[test]
    fn numbers() {
        assert_eq!(kinds("42"), [SyntaxKind::Dec]);
        assert_eq!(kinds("0xFf09"), [SyntaxKind::Hex]);
        assert_eq!(kinds("0b101"), [SyntaxKind::Bin]);
        // No digits after the prefix: a number, then a name.
        assert_eq!(kinds("0x"), [SyntaxKind::Dec, SyntaxKind::Ident]);
        assert_eq!(kinds("0b2"), [SyntaxKind::Dec, SyntaxKind::Ident]);
    }

    #[test]
    fn strings() {
        assert_eq!(kinds(r#""a\n\"\\b""#), [SyntaxKind::Str]);
        let bad = lex(r#""a\qb""#);
        assert_eq!(bad.tokens.len(), 1);
        assert_eq!(bad.tokens[0].kind, SyntaxKind::Error);
    }

    #[test]
    fn comments() {
        assert_eq!(kinds("// x\n1"), [SyntaxKind::LineComment, SyntaxKind::Dec]);
        assert_eq!(
            kinds("/* a * / */1"),
            [SyntaxKind::BlockComment, SyntaxKind::Dec]
        );
        assert_eq!(
            kinds("/* a /* b */ c */"),
            [
                SyntaxKind::BlockComment,
                SyntaxKind::Ident,
                SyntaxKind::Star,
                SyntaxKind::Slash
            ]
        );
    }

    #[test]
    fn longest_match() {
        use SyntaxKind::*;
        assert_eq!(kinds(">>"), [Shr]);
        assert_eq!(kinds(":="), [ColonEq]);
        assert_eq!(kinds("+%"), [PlusPercent]);
        assert_eq!(kinds(".."), [DotDot]);
        assert_eq!(kinds("::"), [ColonColon]);
        assert_eq!(kinds("->"), [Arrow]);
        assert_eq!(kinds(">>>"), [Shr, Gt]);
        assert_eq!(kinds("a.b"), [Ident, Dot, Ident]);
        assert_eq!(kinds("<<= "), [Shl, Eq]);
        assert_eq!(kinds("@TypeOf"), [At, Ident]);
    }

    #[test]
    fn errors_are_data() {
        let lexed = lex("a $ \"x\n/* y");
        let found: Vec<_> = lexed.errors.iter().map(|e| (e.code, e.offset)).collect();
        assert_eq!(found, [("S001", 2), ("S001", 4), ("S001", 7)]);
        let joined: String = lexed
            .tokens
            .iter()
            .map(|t| &"a $ \"x\n/* y"[t.range.clone()])
            .collect();
        assert_eq!(joined, "a $ \"x\n/* y");
    }

    proptest! {
        #[test]
        fn lossless_and_total(input in any::<String>()) {
            let lexed = lex(&input);
            let mut end = 0;
            for token in &lexed.tokens {
                prop_assert_eq!(token.range.start, end);
                prop_assert!(token.range.end > end);
                end = token.range.end;
            }
            prop_assert_eq!(end, input.len());
            let joined: String = lexed.tokens.iter().map(|t| &input[t.range.clone()]).collect();
            prop_assert_eq!(joined, input);
        }

        #[test]
        fn lossless_on_source_like_text(input in "[a-z0-9 \\n\"/*\\\\@:=<>+%.&|!{}()\\[\\]-]{0,80}") {
            let lexed = lex(&input);
            let joined: String = lexed.tokens.iter().map(|t| &input[t.range.clone()]).collect();
            prop_assert_eq!(joined, input);
        }
    }
}
