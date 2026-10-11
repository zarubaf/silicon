// SPDX-License-Identifier: Apache-2.0
use std::io::Read;
use std::path::Path;
use std::sync::LazyLock;

use anyhow::{Context, Result};
use regex::Regex;

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

/// Top-level entries permitted by the repository layout (design spec section 3).
pub const ROOT_ALLOWLIST: &[&str] = &[
    "AGENTS.md",
    "CLAUDE.md",
    "CONTEXT.md",
    "README.md",
    "LICENSE",
    "flake.nix",
    "flake.lock",
    ".envrc",
    "justfile",
    "Cargo.toml",
    "Cargo.lock",
    "rustfmt.toml",
    "clippy.toml",
    "deny.toml",
    ".config",
    ".cargo",
    ".mdformat.toml",
    ".vale.ini",
    ".vale",
    ".editorconfig",
    ".gitignore",
    "lefthook.yml",
    "taplo.toml",
    ".yamlfmt",
    "crates",
    "xtask",
    "lean",
    "doc",
    "tests",
    ".claude",
    ".codex",
    ".github",
];

const BANNED_EXTENSIONS: &[&str] = &["sh", "log", "orig", "rej", "bak"];
// Split so that this file does not match its own marker scan.
const BANNED_NAMES: &[&str] = &[concat!("TO", "DO.md"), "NOTES.md"];
const TODO_EXTENSIONS: &[&str] = &["rs", "lean", "toml", "yml", "yaml", "nix"];

static TODO_MARKER: LazyLock<Regex> = LazyLock::new(|| {
    // `regex` has no look-ahead, so capture the issue reference and test for its absence.
    Regex::new(concat!(r"\b(TO", r"DO|FIX", r"ME)\b(\(#\d+\))?"))
        .unwrap_or_else(|e| unreachable!("{e}"))
});

/// Returns the entries whose first path component is not in [`ROOT_ALLOWLIST`].
pub fn stray_root_entries(paths: &[&str]) -> Vec<String> {
    let mut stray: Vec<String> = Vec::new();
    for path in paths {
        let top = path.split('/').next().unwrap_or(path);
        if !ROOT_ALLOWLIST.contains(&top) && !stray.iter().any(|s| s == top) {
            stray.push(top.to_owned());
        }
    }
    stray
}

pub fn is_banned(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_default();
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or_default();
    BANNED_EXTENSIONS.contains(&ext)
        || BANNED_NAMES.contains(&name)
        || path.components().any(|c| c.as_os_str() == "superpowers")
}

/// True for an executable file or a file whose first line is a shebang.
///
/// `#![` opens a Rust inner attribute, not a shebang.
pub fn is_script(is_executable: bool, head: &[u8]) -> bool {
    is_executable || (head.starts_with(b"#!") && !head.starts_with(b"#!["))
}

/// Returns the first three bytes of a file, or fewer for a shorter file.
fn head(path: &Path) -> Result<Vec<u8>> {
    let mut buf = Vec::with_capacity(3);
    std::fs::File::open(path)
        .with_context(|| format!("reading {}", path.display()))?
        .take(3)
        .read_to_end(&mut buf)?;
    Ok(buf)
}

pub fn is_todo_scanned(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_default();
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or_default();
    name == "justfile" || TODO_EXTENSIONS.contains(&ext)
}

/// Returns the 1-based lines that hold a marker without an issue reference.
pub fn todo_violations(text: &str) -> Vec<usize> {
    text.lines()
        .enumerate()
        .filter(|(_, line)| TODO_MARKER.captures_iter(line).any(|c| c.get(2).is_none()))
        .map(|(i, _)| i + 1)
        .collect()
}

const CHAINING_TOKENS: &[&str] = &["&&", "||", "|", ";", "$(", "`"];

/// Returns `(line, recipe, reason)` for each recipe that is not one command on one line.
pub fn justfile_violations(text: &str) -> Vec<(usize, String, String)> {
    let mut out = Vec::new();
    let mut recipe: Option<(usize, &str, usize)> = None;
    for (i, line) in text.lines().enumerate() {
        if line.starts_with([' ', '\t']) {
            let body = line.trim();
            let Some((header, name, count)) = recipe.as_mut() else {
                continue;
            };
            if body.is_empty() || body.starts_with('#') {
                continue;
            }
            *count += 1;
            if *count == 2 {
                out.push((
                    *header,
                    (*name).to_owned(),
                    "has more than one body line".into(),
                ));
            }
            if let Some(token) = CHAINING_TOKENS.iter().find(|t| body.contains(**t)) {
                out.push((
                    i + 1,
                    (*name).to_owned(),
                    format!("chains commands with `{token}`"),
                ));
            }
        } else if !line.trim().is_empty() && !line.starts_with('#') {
            recipe = None;
            if line.contains(':') && !line.contains(":=") {
                let header = line.split(':').next().unwrap_or(line);
                let name = header.split_whitespace().next().unwrap_or(header);
                recipe = Some((i + 1, name, 0));
            }
        }
    }
    out
}

/// The first line a Rust or Lean source file must hold, or `None` for other files.
fn spdx_header(path: &Path) -> Option<&'static str> {
    match path.extension().and_then(|e| e.to_str()) {
        Some("rs") => Some("// SPDX-License-Identifier: Apache-2.0"),
        Some("lean") => Some("-- SPDX-License-Identifier: Apache-2.0"),
        _ => None,
    }
}

/// True when `text` starts with the SPDX line its file kind requires.
pub fn spdx_ok(path: &Path, text: &str) -> bool {
    spdx_header(path).is_none_or(|want| text.lines().next() == Some(want))
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    let paths: Vec<String> = repo
        .files
        .iter()
        .map(|f| f.path.to_string_lossy().into_owned())
        .collect();
    let refs: Vec<&str> = paths.iter().map(String::as_str).collect();
    for entry in stray_root_entries(&refs) {
        out.push(Violation {
            path: entry.into(),
            line: None,
            rule: "tree-root",
            severity: Severity::Error,
            message: "top-level entry is not in the repository layout".into(),
        });
    }
    for file in &repo.files {
        let banned = if is_banned(&file.path) {
            Some("file matches a banned artifact pattern")
        } else if !file.is_symlink
            && is_script(file.is_executable, &head(&repo.root.join(&file.path))?)
        {
            Some("file is a script (executable mode or `#!` line); move the logic to xtask")
        } else {
            None
        };
        if let Some(message) = banned {
            out.push(Violation {
                path: file.path.clone(),
                line: None,
                rule: "tree-banned",
                severity: Severity::Error,
                message: message.into(),
            });
        }
        if file.is_symlink {
            continue;
        }
        if is_todo_scanned(&file.path) {
            for line in todo_violations(&repo.read(&file.path)?) {
                out.push(Violation {
                    path: file.path.clone(),
                    line: Some(line),
                    rule: "tree-todo",
                    severity: Severity::Error,
                    message: "task marker needs an issue reference, e.g. (#123)".into(),
                });
            }
        }
        if spdx_header(&file.path).is_some() && !spdx_ok(&file.path, &repo.read(&file.path)?) {
            out.push(Violation {
                path: file.path.clone(),
                line: Some(1),
                rule: "tree-spdx",
                severity: Severity::Error,
                message: "first line must be the Apache-2.0 SPDX identifier".into(),
            });
        }
        if file.path == Path::new("justfile") {
            for (line, name, reason) in justfile_violations(&repo.read(&file.path)?) {
                out.push(Violation {
                    path: file.path.clone(),
                    line: Some(line),
                    rule: "tree-justfile",
                    severity: Severity::Error,
                    message: format!("recipe `{name}` {reason}"),
                });
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::TrackedFile;
    use std::path::Path;

    // Test inputs spell the markers `T0` and `F1` so this file passes its own scan.
    fn mark(s: &str) -> String {
        s.replace("T0", "TOD\x4f").replace("F1", "FIX\x4dE")
    }

    #[test]
    fn root_allowlist_rejects_stray_file() {
        assert_eq!(stray_root_entries(&["PLAN.md", "doc/x.md"]), ["PLAN.md"]);
    }

    #[test]
    fn root_allowlist_accepts_layout() {
        for entry in ROOT_ALLOWLIST {
            assert!(stray_root_entries(&[entry]).is_empty(), "{entry}");
        }
    }

    #[test]
    fn bans_artifact_patterns() {
        for p in [
            "a.sh",
            "x/b.log",
            "c.orig",
            "d.rej",
            "e.bak",
            "TOD\x4f.md",
            "NOTES.md",
            "doc/superpowers/p.md",
        ] {
            assert!(is_banned(Path::new(p)), "{p}");
        }
        assert!(!is_banned(Path::new("doc/notes.rs")));
    }

    #[test]
    fn executables_and_shebangs_are_scripts() {
        assert!(is_script(true, b""));
        assert!(is_script(false, b"#!/usr/bin/env python3\n"));
        assert!(is_script(false, b"#! /bin/sh\n"));
        assert!(!is_script(false, b"#![allow(clippy::x)]\n"));
        assert!(!is_script(false, b"# Title\n"));
        assert!(!is_script(false, b""));
    }

    #[test]
    fn todo_requires_issue() {
        assert_eq!(
            todo_violations(&mark("// T0: x\n// T0(#12): y\n// F1 z")),
            [1, 3]
        );
    }

    #[test]
    fn todo_check_ignores_markdown() {
        assert!(!is_todo_scanned(Path::new("doc/a.md")));
        for p in [
            "a.rs", "a.lean", "a.toml", "a.yml", "a.yaml", "a.nix", "justfile",
        ] {
            assert!(is_todo_scanned(Path::new(p)), "{p}");
        }
    }

    #[test]
    fn spdx_line_must_be_first() {
        let rs = Path::new("a.rs");
        let lean = Path::new("a.lean");
        assert!(spdx_ok(
            rs,
            "// SPDX-License-Identifier: Apache-2.0\nfn f() {}\n"
        ));
        assert!(spdx_ok(
            lean,
            "-- SPDX-License-Identifier: Apache-2.0\nimport Std\n"
        ));
        assert!(!spdx_ok(rs, "fn f() {}\n"));
        assert!(!spdx_ok(
            rs,
            "//! doc\n// SPDX-License-Identifier: Apache-2.0\n"
        ));
        assert!(!spdx_ok(
            lean,
            "-- SPDX-License-Identifier: Apache-2.0\n"
                .replace("--", "//")
                .as_str()
        ));
        assert!(spdx_ok(Path::new("a.md"), "text"));
    }

    #[test]
    fn check_names_the_file_without_spdx() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        std::fs::create_dir(root.join("xtask")).unwrap();
        std::fs::write(
            root.join("xtask/ok.rs"),
            "// SPDX-License-Identifier: Apache-2.0\n",
        )
        .unwrap();
        std::fs::write(
            root.join("xtask/late.rs"),
            "\n// SPDX-License-Identifier: Apache-2.0\n",
        )
        .unwrap();
        let file = |p: &str| TrackedFile {
            path: p.into(),
            is_symlink: false,
            is_executable: false,
        };
        let repo = Repo::from_parts(
            root.to_path_buf(),
            vec![file("xtask/ok.rs"), file("xtask/late.rs")],
        );
        let got: Vec<(String, String)> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.rule.to_owned(), v.path.display().to_string()))
            .collect();
        assert_eq!(got, [("tree-spdx".to_owned(), "xtask/late.rs".to_owned())]);
    }

    #[test]
    fn justfile_recipe_bodies_are_one_line() {
        let text = "ci: check test\n\nfmt:\n    cargo fmt\n\nbad:\n    one\n    two\n";
        let v = justfile_violations(text);
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].1, "bad");
    }

    #[test]
    fn justfile_rejects_shell_chaining() {
        for body in ["a && b", "a || b", "a; b", "echo $(x)", "echo `x`", "a | b"] {
            let v = justfile_violations(&format!("r:\n    {body}\n"));
            assert_eq!(v.len(), 1, "{body}");
            assert_eq!(v[0].1, "r");
        }
    }

    #[test]
    fn justfile_comment_lines_ignored() {
        let text = "r:\n    # why; this && that\n    cargo fmt\n";
        assert!(justfile_violations(text).is_empty());
    }

    #[test]
    fn check_reports_stray_banned_todo_and_skips_symlinks() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        std::fs::write(root.join("stray.txt"), "x").unwrap();
        std::fs::write(root.join("run.sh"), "x").unwrap();
        std::fs::create_dir(root.join("xtask")).unwrap();
        std::fs::write(
            root.join("xtask/a.rs"),
            mark("// SPDX-License-Identifier: Apache-2.0\n// T0 fix\n"),
        )
        .unwrap();
        std::os::unix::fs::symlink("xtask/a.rs", root.join("xtask/link.rs")).unwrap();
        std::fs::write(root.join("xtask/run"), "#!/bin/sh\necho\n").unwrap();
        std::fs::write(root.join("xtask/tool"), "x").unwrap();
        std::fs::write(
            root.join("xtask/main.rs"),
            "// SPDX-License-Identifier: Apache-2.0\n#![allow(x)]\n",
        )
        .unwrap();
        let file = |p: &str, is_symlink| TrackedFile {
            path: p.into(),
            is_symlink,
            is_executable: p == "xtask/tool",
        };
        let repo = Repo::from_parts(
            root.to_path_buf(),
            vec![
                file("stray.txt", false),
                file("run.sh", false),
                file("xtask/a.rs", false),
                file("xtask/link.rs", true),
                file("xtask/run", false),
                file("xtask/tool", false),
                file("xtask/main.rs", false),
            ],
        );
        let got: Vec<(String, String)> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.rule.to_owned(), v.path.display().to_string()))
            .collect();
        let want = [
            ("tree-root", "stray.txt"),
            ("tree-root", "run.sh"),
            ("tree-banned", "run.sh"),
            ("tree-todo", "xtask/a.rs"),
            ("tree-banned", "xtask/run"),
            ("tree-banned", "xtask/tool"),
        ]
        .map(|(r, p)| (r.to_owned(), p.to_owned()));
        assert_eq!(got, want);
    }
}
