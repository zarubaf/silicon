// SPDX-License-Identifier: Apache-2.0
//! Static strings: literals, `+`, `str(n)`, a static index, `len`, and `==`.
//!
//! A string has at most 16 scalars (`MAX_STRING`). The evaluator rejects a
//! longer one, so a position that holds one takes its fallback. The
//! alphabet has scalars of one, two, three, and four bytes, and the escapes
//! of the grammar, so `len` counts scalars and not bytes.

use super::Builder;
use super::stat::{Kind, Reach, bin};
use crate::eval::{MAX_STRING, Value};
use crate::program::{SBin, SExpr};

const ALPHABET: [char; 12] = [
    'a',
    'b',
    'Z',
    '0',
    ' ',
    '\u{e9}',
    '\u{3bb}',
    '\u{1f600}',
    '"',
    '\\',
    '\n',
    '\t',
];

impl Builder {
    /// A string literal of `0..=6` scalars.
    pub(super) fn string_literal(&mut self) -> SExpr {
        let n = self.tape.below(7);
        let text: String = (0..n)
            .map(|_| ALPHABET[self.tape.index(ALPHABET.len())])
            .collect();
        SExpr::Str(text)
    }

    /// A random static string: a literal, a name, `str(n)`, a join, an
    /// `if`, or one scalar of a string.
    pub(super) fn string_expr(&mut self, depth: u32, r: Reach<'_>) -> SExpr {
        let names: Vec<&String> = r
            .names
            .iter()
            .filter(|(_, t)| super::stat::kind(t) == Some(Kind::Str))
            .map(|(n, _)| n)
            .collect();
        let choice = if depth == 0 {
            self.tape.below(2)
        } else {
            self.tape.below(9)
        };
        let d = depth.saturating_sub(1);
        match choice {
            1 if !names.is_empty() => {
                let i = self.tape.index(names.len());
                names
                    .get(i)
                    .map_or_else(|| SExpr::Str(String::new()), |n| SExpr::Name((*n).clone()))
            }
            2 | 7 => {
                note!(self, str_of);
                SExpr::StrOf(Box::new(self.sexpr(Kind::Int, d, r)))
            }
            3 | 6 => {
                note!(self, joins);
                bin(
                    SBin::Add,
                    self.sexpr(Kind::Str, d, r),
                    self.sexpr(Kind::Str, d, r),
                )
            }
            4 => {
                let cond = self.sexpr(Kind::Bool, d, r);
                let then = self.sexpr(Kind::Str, d, r);
                let els = self.sexpr(Kind::Str, d, r);
                SExpr::If(Box::new(cond), Box::new(then), Box::new(els))
            }
            5 | 8 => self.scalar_of(d, r),
            _ => self.string_literal(),
        }
    }

    /// `s[i]` with `i` in range in each env: `s` is a name or a literal, so
    /// its length is known. An empty string, or no position that holds,
    /// gives `s`.
    fn scalar_of(&mut self, d: u32, r: Reach<'_>) -> SExpr {
        let base = if self.tape.flag() {
            self.string_literal()
        } else {
            self.sexpr(Kind::Str, 0, r)
        };
        let envs = r.envs.unwrap_or_default();
        let lens = if envs.is_empty() {
            literal_len(&base).map(|n| vec![n])
        } else {
            self.values(&SExpr::Len(Box::new(base.clone())), envs)
                .and_then(|vs| vs.iter().map(small).collect())
        };
        let Some(shortest) = lens.and_then(|ls| ls.into_iter().min()) else {
            return base;
        };
        let Some(n) = u32::try_from(shortest).ok().filter(|n| *n >= 1) else {
            return base;
        };
        note!(self, scalars);
        let at = self.index(n, d, r);
        SExpr::Index(Box::new(base), Box::new(at))
    }

    /// An exit from a string: its length in scalars, or the equality of
    /// two strings.
    pub(super) fn string_exit(&mut self, kind: Kind, depth: u32, r: Reach<'_>) -> Option<SExpr> {
        let d = depth.saturating_sub(1);
        match kind {
            Kind::Int => {
                note!(self, str_lens);
                Some(SExpr::Len(Box::new(self.sexpr(Kind::Str, d, r))))
            }
            Kind::Bool => {
                note!(self, str_eqs);
                let op = if self.tape.flag() { SBin::Eq } else { SBin::Ne };
                Some(bin(
                    op,
                    self.sexpr(Kind::Str, d, r),
                    self.sexpr(Kind::Str, d, r),
                ))
            }
            Kind::Str => None,
        }
    }

    /// The fallback of a string position.
    pub(super) fn empty_string() -> (SExpr, Value) {
        (SExpr::Str(String::new()), Value::Str(String::new()))
    }
}

fn small(v: &Value) -> Option<usize> {
    match v {
        Value::Int(n) => usize::try_from(n).ok().filter(|n| *n <= MAX_STRING),
        _ => None,
    }
}

fn literal_len(e: &SExpr) -> Option<usize> {
    match e {
        SExpr::Str(s) => Some(s.chars().count()),
        _ => None,
    }
}
