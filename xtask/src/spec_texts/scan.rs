// SPDX-License-Identifier: Apache-2.0
//! The scanner of string literals for the rule `spec-texts`.

use std::path::Path;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Lang {
    Rust,
    Lean,
}

pub struct Scan<'a> {
    c: &'a [char],
    i: usize,
}

impl Scan<'_> {
    fn starts(&self, s: &str) -> bool {
        s.chars()
            .enumerate()
            .all(|(k, ch)| self.c.get(self.i + k) == Some(&ch))
    }

    fn skip_to(&mut self, end: &str) {
        while self.i < self.c.len() && !self.starts(end) {
            self.i += 1;
        }
        self.i = (self.i + end.len()).min(self.c.len());
    }

    fn skip_space(&mut self) {
        while self.c.get(self.i).is_some_and(|c| c.is_whitespace()) {
            self.i += 1;
        }
    }
}

/// The text of the string literal that starts at the opening quote `s.i`. A `{...}` hole of an
/// interpolated string is `{}`.
fn literal(s: &mut Scan, lang: Lang, holes: bool) -> String {
    let mut out = String::new();
    s.i += 1;
    while let Some(&ch) = s.c.get(s.i) {
        s.i += 1;
        match ch {
            '"' => break,
            '\\' => {
                let Some(&e) = s.c.get(s.i) else { break };
                s.i += 1;
                match e {
                    'n' => out.push('\n'),
                    '\n' => s.skip_space(),
                    other => out.push(other),
                }
            }
            '{' if lang == Lang::Rust && s.c.get(s.i) == Some(&'{') => {
                s.i += 1;
                out.push('{');
            }
            '}' if lang == Lang::Rust && s.c.get(s.i) == Some(&'}') => {
                s.i += 1;
                out.push('}');
            }
            '{' if lang == Lang::Rust => {
                let hole = s.c[s.i..]
                    .iter()
                    .position(|c| !(c.is_alphanumeric() || "_:?.#".contains(*c)));
                match hole {
                    Some(n) if s.c[s.i + n] == '}' => {
                        s.i += n + 1;
                        out.push_str("{}");
                    }
                    _ => out.push('{'),
                }
            }
            '{' if holes => {
                let mut depth = 1;
                while depth > 0 && s.i < s.c.len() {
                    match s.c[s.i] {
                        '{' => depth += 1,
                        '}' => depth -= 1,
                        _ => {}
                    }
                    s.i += 1;
                }
                out.push_str("{}");
            }
            other => out.push(other),
        }
    }
    out
}

/// The string literals of `src`. A literal that a `++` joins to the next one is one entry. The
/// holes of format strings and of `s!` strings are `{}`.
pub fn runs(src: &str, lang: Lang) -> Vec<String> {
    let c: Vec<char> = src.chars().collect();
    let mut s = Scan { c: &c, i: 0 };
    let line_comment = if lang == Lang::Rust { "//" } else { "--" };
    let (open, close) = if lang == Lang::Rust {
        ("/*", "*/")
    } else {
        ("/-", "-/")
    };
    let mut out = Vec::new();
    let mut run: Option<String> = None;
    while s.i < c.len() {
        if s.starts(line_comment) {
            s.skip_to("\n");
        } else if s.starts(open) {
            s.skip_to(close);
        } else if s.starts("'\"'") {
            s.i += 3;
        } else if s.starts("s!\"") || s.starts("\"") {
            let holes = s.starts("s!\"");
            s.i += if holes { 2 } else { 0 };
            let text = literal(&mut s, lang, holes);
            run.get_or_insert_with(String::new).push_str(&text);
            let end = s.i;
            s.skip_space();
            let joined = lang == Lang::Lean && s.starts("++") && {
                s.i += 2;
                s.skip_space();
                s.starts("\"") || s.starts("s!\"")
            };
            if !joined {
                out.extend(run.take());
                s.i = end;
            }
        } else {
            s.i += 1;
        }
    }
    out.iter().map(|r| r.replace("{}:{}", "{}")).collect()
}

/// A Rust file without its test module and without a test file.
pub fn rust_non_test(path: &str, src: &str) -> Option<String> {
    let p = Path::new(path);
    let test_file = p.components().any(|c| c.as_os_str() == "tests")
        || p.file_stem()
            .and_then(|s| s.to_str())
            .is_some_and(|s| s.starts_with("tests"))
        || path.starts_with("crates/testkit/");
    if test_file || p.extension() != Some("rs".as_ref()) {
        return None;
    }
    let cut = src
        .match_indices("\n#[cfg(test)]\nmod ")
        .find(|(i, m)| {
            src[i + m.len()..]
                .lines()
                .next()
                .is_some_and(|l| l.ends_with(" {"))
        })
        .map_or(src.len(), |(i, _)| i);
    Some(src[..cut].to_owned())
}

pub fn lean_non_test(path: &str) -> bool {
    Path::new(path).extension() == Some("lean".as_ref())
        && !path.contains("/Test/")
        && !path.contains("/Proof/")
}
