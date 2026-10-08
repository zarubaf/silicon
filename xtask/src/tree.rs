use std::path::Path;
use std::sync::LazyLock;

use anyhow::Result;
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

/// Returns `(line, recipe)` for each recipe with more than one body line.
pub fn justfile_violations(text: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut recipe: Option<(usize, &str, usize)> = None;
    let mut flush = |recipe: Option<(usize, &str, usize)>| {
        if let Some((line, name, body)) = recipe
            && body > 1
        {
            out.push((line, name.to_owned()));
        }
    };
    for (i, line) in text.lines().enumerate() {
        if line.starts_with([' ', '\t']) {
            if let Some((_, _, body)) = recipe.as_mut()
                && !line.trim().is_empty()
            {
                *body += 1;
            }
        } else if !line.trim().is_empty() && !line.starts_with('#') {
            flush(recipe.take());
            let header = line.split(':').next().unwrap_or(line);
            if line.contains(':') && !line.contains(":=") {
                let name = header.split_whitespace().next().unwrap_or(header);
                recipe = Some((i + 1, name, 0));
            }
        }
    }
    flush(recipe.take());
    out
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
        if is_banned(&file.path) {
            out.push(Violation {
                path: file.path.clone(),
                line: None,
                rule: "tree-banned",
                severity: Severity::Error,
                message: "file matches a banned artifact pattern".into(),
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
        if file.path == Path::new("justfile") {
            for (line, name) in justfile_violations(&repo.read(&file.path)?) {
                out.push(Violation {
                    path: file.path.clone(),
                    line: Some(line),
                    rule: "tree-justfile",
                    severity: Severity::Error,
                    message: format!("recipe `{name}` has more than one body line"),
                });
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn justfile_recipe_bodies_are_one_line() {
        let text = "ci: check test\n\nfmt:\n    cargo fmt\n\nbad:\n    one\n    two\n";
        let v = justfile_violations(text);
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].1, "bad");
    }
}
