// SPDX-License-Identifier: Apache-2.0
//! The Rust subset of the elaborator core (front-end spec, section 4.5). A text scan of the
//! non-test code of `crates/elab` finds the constructs that Aeneas cannot translate. The scan
//! cannot see a closure that captures a mutable value without the word `FnMut`, so it checks
//! the signatures that spell the bound.

use std::path::Path;
use std::sync::LazyLock;

use anyhow::Result;
use regex::Regex;

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

const SCANNED_DIR: &str = "crates/elab/src/";

/// A banned construct that the code may still use: the file, the construct, and the reason.
/// An entry needs an issue that removes it.
const ALLOWED: &[(&str, &str, &str)] = &[];

static BANNED: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"\b(Cell|RefCell|Rc|Arc|Mutex|RwLock|FnMut|HashMap|HashSet|unsafe|dyn)\b|\bthread_local!|\bstd::thread\b|\bstatic\s+mut\b",
    )
    .unwrap_or_else(|e| unreachable!("{e}"))
});

/// True for a file that only the tests compile.
fn is_test_file(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_default();
    name == "counters.rs" || name.starts_with("tests")
}

/// The line without its comment, the text of its string literals, and its character literals.
/// `in_str` tells that the line starts inside a string that an earlier line opened. On return, it
/// tells the same of the next line.
fn code_of(line: &str, in_str: &mut bool) -> String {
    let mut out = String::new();
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        match (*in_str, c) {
            (true, '\\') => {
                chars.next();
            }
            (true, '"') => *in_str = false,
            (true, _) => {}
            (false, '"') => *in_str = true,
            (false, '\'') => {
                // A lifetime has no closing quote, so it stays in the code.
                let ahead: Vec<char> = chars.clone().take(10).collect();
                let skip = match ahead.as_slice() {
                    ['\\', ..] => ahead
                        .iter()
                        .skip(2)
                        .position(|c| *c == '\'')
                        .map_or(1, |p| p + 3),
                    [_, '\'', ..] => 2,
                    _ => 0,
                };
                for _ in 0..skip {
                    chars.next();
                }
            }
            (false, '/') if chars.peek() == Some(&'/') => break,
            (false, _) => out.push(c),
        }
    }
    out
}

/// The change of the nesting depth of brackets that `code` makes.
fn depth_change(code: &str) -> i64 {
    code.chars().fold(0, |d, c| match c {
        '(' | '[' | '{' => d + 1,
        ')' | ']' | '}' => d - 1,
        _ => d,
    })
}

/// The item or statement after a `#[cfg(test)]` line: it ends when the brackets close at a
/// `;`, a `}`, or a `,`.
struct Skip {
    depth: i64,
    started: bool,
}

impl Skip {
    /// Takes one line of code. Returns true when the skipped item ends on it.
    fn take(&mut self, code: &str) -> bool {
        let code = code.trim();
        if code.is_empty() || (!self.started && code.starts_with("#[")) {
            return false;
        }
        self.started = true;
        self.depth += depth_change(code);
        self.depth <= 0 && code.ends_with([';', '}', ','])
    }
}

/// Returns the 1-based line and the construct for each banned construct in the non-test code
/// of `text`.
pub fn banned_constructs(text: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut skip: Option<Skip> = None;
    let mut in_str = false;
    for (i, line) in text.lines().enumerate() {
        let code = code_of(line, &mut in_str);
        if let Some(s) = skip.as_mut() {
            if s.take(&code) {
                skip = None;
            }
            continue;
        }
        if code.trim() == "#[cfg(test)]" {
            skip = Some(Skip {
                depth: 0,
                started: false,
            });
            continue;
        }
        for m in BANNED.find_iter(&code) {
            out.push((i + 1, m.as_str().to_owned()));
        }
    }
    out
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    for file in &repo.files {
        let name = file.path.to_string_lossy();
        if file.is_symlink
            || !name.starts_with(SCANNED_DIR)
            || !name.ends_with(".rs")
            || is_test_file(&file.path)
        {
            continue;
        }
        for (line, construct) in banned_constructs(&repo.read(&file.path)?) {
            if ALLOWED
                .iter()
                .any(|(path, token, _)| *path == name && *token == construct)
            {
                continue;
            }
            out.push(Violation {
                path: file.path.clone(),
                line: Some(line),
                rule: "elab-subset",
                severity: Severity::Error,
                message: format!(
                    "`{construct}` is outside the Rust subset of the elaborator core \
                     (front-end spec, section 4.5); pass state as a parameter and use owned data"
                ),
            });
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::TrackedFile;

    fn found(text: &str) -> Vec<(usize, String)> {
        banned_constructs(text)
    }

    #[test]
    fn finds_each_banned_construct() {
        for construct in [
            "Cell", "RefCell", "Rc", "Arc", "Mutex", "RwLock", "FnMut", "HashMap", "HashSet",
            "unsafe", "dyn",
        ] {
            let text = format!("fn f(x: &{construct}<u8>) {{}}\n");
            assert_eq!(found(&text), [(1, construct.to_owned())], "{construct}");
        }
        assert_eq!(
            found("thread_local! { }\n"),
            [(1, "thread_local!".to_owned())]
        );
        assert_eq!(found("use std::thread;\n"), [(1, "std::thread".to_owned())]);
        assert_eq!(
            found("static mut N: u8 = 0;\n"),
            [(1, "static mut".to_owned())]
        );
    }

    #[test]
    fn a_longer_word_is_not_a_construct() {
        assert!(found("let unsafe_code = OnceCell::new(); let Arcs = 1;\n").is_empty());
    }

    #[test]
    fn a_comment_and_a_string_are_not_code() {
        let text = "// a Cell\n/// an Arc<str>\nlet m = \"a Mutex \\\" and dyn\"; // HashMap\n";
        assert!(found(text).is_empty());
    }

    #[test]
    fn a_literal_does_not_confuse_the_skip() {
        let text = "#[cfg(test)]\nmod tests {\n    fn f<'a>(x: &'a str) {\n        let a = '{';\n        let b = '\\'';\n        let s = \"a {\n  b\";\n        let c: Cell<u8>;\n    }\n}\nfn g(x: Rc<u8>) {}\n";
        assert_eq!(found(text), [(11, "Rc".to_owned())]);
    }

    #[test]
    fn a_test_module_is_skipped() {
        let text = "#[cfg(test)]\nmod tests {\n    use std::cell::Cell;\n    fn f() {\n        let c = Cell::new(0);\n    }\n}\nfn g(x: Rc<u8>) {}\n";
        assert_eq!(found(text), [(8, "Rc".to_owned())]);
    }

    #[test]
    fn a_test_item_of_one_statement_is_skipped() {
        let text = "struct S {\n    #[cfg(test)]\n    steps: Cell<u64>,\n    x: Rc<u8>,\n}\n\
                    #[cfg(test)]\n#[allow(dead_code)]\nstatic C: Mutex<u8> =\n    Mutex::new(0);\n\
                    fn f() {\n    #[cfg(test)]\n    {\n        let c: Cell<u8>;\n    }\n    let d: Arc<u8>;\n}\n";
        assert_eq!(found(text), [(4, "Rc".to_owned()), (15, "Arc".to_owned())]);
    }

    #[test]
    fn a_not_test_item_is_scanned() {
        assert_eq!(
            found("#[cfg(not(test))]\nfn f(c: Cell<u8>) {}\n"),
            [(2, "Cell".to_owned())]
        );
    }

    #[test]
    fn check_scans_the_non_test_files_of_elab() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        let dir = root.join("crates/elab/src");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::create_dir_all(root.join("crates/parse/src")).unwrap();
        for (name, text) in [
            ("crates/elab/src/eval.rs", "fn f(c: Cell<u8>) {}\n"),
            ("crates/elab/src/tests_eval.rs", "fn f(c: Cell<u8>) {}\n"),
            ("crates/elab/src/counters.rs", "fn f(c: Cell<u8>) {}\n"),
            ("crates/parse/src/error.rs", "fn f(c: Cell<u8>) {}\n"),
        ] {
            std::fs::write(root.join(name), text).unwrap();
        }
        let file = |p: &str| TrackedFile {
            path: p.into(),
            is_symlink: false,
            is_executable: false,
        };
        let repo = Repo::from_parts(
            root.to_path_buf(),
            vec![
                file("crates/elab/src/eval.rs"),
                file("crates/elab/src/tests_eval.rs"),
                file("crates/elab/src/counters.rs"),
                file("crates/parse/src/error.rs"),
            ],
        );
        let got: Vec<String> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| format!("{}:{:?}:{}", v.path.display(), v.line, v.rule))
            .collect();
        assert_eq!(got, ["crates/elab/src/eval.rs:Some(1):elab-subset"]);
    }
}
