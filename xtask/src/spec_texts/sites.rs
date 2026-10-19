// SPDX-License-Identifier: Apache-2.0
//! The error sites of the front ends: the places that build a diagnostic with a code.
//!
//! A Lean site is a `fail .Sxxx` call, a `typeError` call, a `(.Sxxx, "...")` pair, `⟨.Sxxx, ...⟩`,
//! or a lexer `⟨pos, .error "..."⟩` token. A Rust site is a `type_error(...)`, `syntax_error(...)`
//! or `syntax_error_at(...)` call, the message of a lexer `SyntaxKind::Error`, or the bracket
//! group that holds a `Code::Sxxx,` argument or field.
//! The message literals of a site are the string literals in its span. A site with no literal
//! builds its message in a helper, which the scanner cannot see: it is unscannable.

use anyhow::Result;
use regex::Regex;

use super::scan::{Lang, runs};

/// A message literal at an error site, or the site itself when it has none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Site {
    pub path: String,
    pub line: usize,
    pub code: String,
    /// The text with `{}` for each hole, or `None` when the site has no scannable literal.
    pub text: Option<String>,
}

/// The texts of a span that read as a message: at least two words, not counting the holes.
fn messages(span: &str, lang: Lang) -> Vec<String> {
    runs(span, lang)
        .into_iter()
        .filter(|t| t.replace("{}", "").split_whitespace().count() >= 2)
        .collect()
}

fn sites_of(
    path: &str,
    line: usize,
    code: &str,
    span: &str,
    lang: Lang,
    report_bare: bool,
) -> Vec<Site> {
    let found = messages(span, lang);
    let make = |text| Site {
        path: path.to_owned(),
        line,
        code: code.to_owned(),
        text,
    };
    if found.is_empty() {
        return if report_bare {
            vec![make(None)]
        } else {
            vec![]
        };
    }
    found.into_iter().map(|t| make(Some(t))).collect()
}

fn indent(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// The sites of a Lean file. A site spans its line from the trigger and the lines below with a
/// deeper indent.
pub fn lean_sites(path: &str, src: &str) -> Result<Vec<Site>> {
    let fail = Regex::new(r"\bfail\s+\.(S\d{3})\b")?;
    let pair = Regex::new(r"[(⟨]\.(S\d{3}),")?;
    let token = Regex::new(r#"⟨[^⟨⟩]*,\s*\.error\s+""#)?;
    let type_error = Regex::new(r"\btypeError\b")?;
    let lines: Vec<&str> = src.lines().collect();
    let mut starts: Vec<(usize, String, bool)> = Vec::new();
    for m in fail.captures_iter(src) {
        starts.push((m.get(0).map_or(0, |x| x.start()), m[1].to_owned(), true));
    }
    for m in pair.captures_iter(src) {
        starts.push((m.get(0).map_or(0, |x| x.start()), m[1].to_owned(), false));
    }
    for m in token.find_iter(src) {
        starts.push((m.start(), "S001".to_owned(), false));
    }
    for m in type_error.find_iter(src) {
        starts.push((m.start(), "S010".to_owned(), true));
    }
    starts.sort();
    let mut out = Vec::new();
    let mut done = std::collections::HashSet::new();
    for (at, code, bare) in starts {
        let i = src[..at].matches('\n').count();
        let line = lines[i];
        let trimmed = line.trim_start();
        if trimmed.starts_with("--") || trimmed.starts_with("def typeError") || !done.insert(i) {
            continue;
        }
        let from = src[..at].rfind('\n').map_or(0, |n| n + 1);
        let mut span = line[at - from..].to_owned();
        let floor = indent(line);
        for next in &lines[i + 1..] {
            if next.trim().is_empty() || indent(next) <= floor {
                break;
            }
            span.push('\n');
            span.push_str(next);
        }
        out.extend(sites_of(path, i + 1, &code, &span, Lang::Lean, bare));
    }
    Ok(out)
}

/// A trigger of a Rust site: where it is, the bracket that holds it, and the code.
struct Trigger {
    at: usize,
    open: usize,
    code: String,
}

fn ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn skip_quoted(c: &[char], mut i: usize) -> usize {
    i += 1;
    while i < c.len() && c[i] != '"' {
        i += if c[i] == '\\' { 2 } else { 1 };
    }
    i + 1
}

fn prev_char(c: &[char], i: usize) -> Option<char> {
    c[..i].iter().rev().find(|ch| !ch.is_whitespace()).copied()
}

fn next_char(c: &[char], i: usize) -> Option<char> {
    c[i..].iter().find(|ch| !ch.is_whitespace()).copied()
}

fn starts(c: &[char], i: usize, s: &str) -> bool {
    s.chars()
        .enumerate()
        .all(|(k, ch)| c.get(i + k) == Some(&ch))
}

/// The index of the `(` of a call to `name` at `i`, with any whitespace before the `(`.
fn call_open(c: &[char], i: usize, name: &str) -> Option<usize> {
    if (i > 0 && ident_char(c[i - 1])) || !starts(c, i, name) {
        return None;
    }
    let after = i + name.chars().count();
    let skip = c[after..].iter().take_while(|x| x.is_whitespace()).count();
    (c.get(after + skip) == Some(&'(')).then_some(after + skip)
}

/// True when `SyntaxKind::Error,` at `i` has a message expression after it, which is `None`
/// for a token that needs no message.
fn lexer_error_message(c: &[char], i: usize) -> bool {
    let name = "SyntaxKind::Error";
    if (i > 0 && ident_char(c[i - 1])) || !starts(c, i, name) {
        return false;
    }
    let j = i + name.len();
    let mut rest = c[j..].iter().skip_while(|x| x.is_whitespace());
    if rest.next() != Some(&',') {
        return false;
    }
    let tail: String = rest.skip_while(|x| x.is_whitespace()).take(4).collect();
    !tail.is_empty() && tail != "None"
}

/// The triggers of a Rust file, and the end of each bracket that is open at a trigger.
fn rust_triggers(c: &[char]) -> (Vec<Trigger>, std::collections::HashMap<usize, usize>) {
    let mut triggers = Vec::new();
    let mut ends = std::collections::HashMap::new();
    let mut stack: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < c.len() {
        let ch = c[i];
        if starts(c, i, "//") {
            while i < c.len() && c[i] != '\n' {
                i += 1;
            }
        } else if starts(c, i, "/*") {
            while i < c.len() && !starts(c, i, "*/") {
                i += 1;
            }
            i += 2;
        } else if ch == '"' {
            i = skip_quoted(c, i);
        } else if ch == '\'' {
            i += if c.get(i + 1) == Some(&'\\') {
                c[i + 2..]
                    .iter()
                    .position(|x| *x == '\'')
                    .map_or(1, |n| n + 3)
            } else if c.get(i + 2) == Some(&'\'') {
                3
            } else {
                1
            };
        } else if matches!(ch, '(' | '[' | '{') {
            stack.push(i);
            i += 1;
        } else if matches!(ch, ')' | ']' | '}') {
            if let Some(open) = stack.pop() {
                ends.insert(open, i);
            }
            i += 1;
        } else if let Some(open) = call_open(c, i, "type_error") {
            triggers.push(Trigger {
                at: i,
                open,
                code: "S010".to_owned(),
            });
            i = open;
        } else if let Some(open) =
            call_open(c, i, "syntax_error_at").or_else(|| call_open(c, i, "syntax_error"))
        {
            triggers.push(Trigger {
                at: i,
                open,
                code: "S001".to_owned(),
            });
            i = open;
        } else if lexer_error_message(c, i)
            && let Some(&open) = stack.last()
        {
            triggers.push(Trigger {
                at: i,
                open,
                code: "S001".to_owned(),
            });
            i += "SyntaxKind::Error".len();
        } else if (i == 0 || !ident_char(c[i - 1])) && starts(c, i, "Code::S") {
            let digits: String = c[i + 7..].iter().take(3).collect();
            let after = i + 7 + 3;
            if digits.len() == 3
                && digits.chars().all(|d| d.is_ascii_digit())
                && matches!(prev_char(c, i), Some('(' | ':'))
                && next_char(c, after) == Some(',')
                && let Some(&open) = stack.last()
            {
                triggers.push(Trigger {
                    at: i,
                    open,
                    code: format!("S{digits}"),
                });
            }
            i += 7;
        } else {
            i += 1;
        }
    }
    (triggers, ends)
}

/// The sites of the non-test code of a Rust file.
pub fn rust_sites(path: &str, src: &str) -> Vec<Site> {
    let c: Vec<char> = src.chars().collect();
    let (triggers, ends) = rust_triggers(&c);
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    for t in triggers {
        let Some(&end) = ends.get(&t.open) else {
            continue;
        };
        if !seen.insert(t.open) {
            continue;
        }
        let span: String = c[t.open..=end].iter().collect();
        let line = 1 + c[..t.at].iter().filter(|x| **x == '\n').count();
        out.extend(sites_of(path, line, &t.code, &span, Lang::Rust, true));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn texts(sites: &[Site]) -> Vec<(String, Option<String>)> {
        sites
            .iter()
            .map(|s| (s.code.clone(), s.text.clone()))
            .collect()
    }

    #[test]
    fn a_lean_site_spans_its_continuation_lines() {
        let src = "def f :=\n  if a then fail .S010 p s!\"`{x}` is a memory, \" ++\n    \"not data\"\n  else fail .S017 s partText\n  -- fail .S001 p \"no\"\n  x\n";
        let got = lean_sites("a.lean", src).unwrap();
        assert_eq!(
            texts(&got),
            [
                (
                    "S010".to_owned(),
                    Some("`{}` is a memory, not data".to_owned())
                ),
                ("S017".to_owned(), None),
            ]
        );
        assert_eq!((got[0].line, got[1].line), (2, 4));
    }

    #[test]
    fn a_trigger_split_over_lines_is_a_site() {
        let rs = "fn f() {\n    (\n        SyntaxKind::Error,\n        Some(\"invalid character in string\".into()),\n    )\n}\n";
        let got = rust_sites("lexer.rs", rs);
        assert_eq!(
            texts(&got),
            [(
                "S001".to_owned(),
                Some("invalid character in string".to_owned())
            )]
        );
        let rs = "x(\n  SyntaxKind::Error,\n  first.then(|| Some(\"two words\".into())),\n)\n";
        assert_eq!(
            texts(&rust_sites("l.rs", rs)),
            [("S001".to_owned(), Some("two words".to_owned()))]
        );
        assert!(rust_sites("l.rs", "x(SyntaxKind::Error, None)").is_empty());
        let rs = "syntax_error\n(\"expected a type\")";
        assert_eq!(rust_sites("p.rs", rs).len(), 1);
        let lean = "def f :=\n  fail\n    .S010 p \"two words here\"\n";
        assert_eq!(
            texts(&lean_sites("a.lean", lean).unwrap()),
            [("S010".to_owned(), Some("two words here".to_owned()))]
        );
    }

    #[test]
    fn a_rust_site_is_the_bracket_group_of_a_code_argument() {
        let src = "fn f() {\n    fail(\n        Code::S010,\n        pos,\n        format!(\"a port has {n} bits; \\\n            widen it\"),\n    );\n    let ok = code == Code::S001;\n    Err(type_error(format!(\"two words {x}\")));\n    Err((Code::S013, msg()))\n}\n";
        let got = rust_sites("a.rs", src);
        assert_eq!(
            texts(&got),
            [
                (
                    "S010".to_owned(),
                    Some("a port has {} bits; widen it".to_owned())
                ),
                ("S010".to_owned(), Some("two words {}".to_owned())),
                ("S013".to_owned(), None),
            ]
        );
        assert_eq!(got[0].line, 3);
    }
}
