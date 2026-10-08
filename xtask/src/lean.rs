use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

/// Longest allowed Lean source line, in characters.
const MAX_LINE: usize = 100;

/// Exceptions to the proof rules, read from `lean/allowlist.toml`.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Allowlist {
    pub axioms: Vec<String>,
    pub native_decide_files: Vec<PathBuf>,
}

impl Allowlist {
    pub fn parse(text: &str) -> Result<Self> {
        let doc: toml::Table = text.parse().context("parsing lean/allowlist.toml")?;
        let strings = |key: &str| -> Result<Vec<String>> {
            let Some(value) = doc.get(key) else {
                return Ok(Vec::new());
            };
            value
                .as_array()
                .and_then(|a| a.iter().map(|v| v.as_str().map(str::to_owned)).collect())
                .with_context(|| format!("`{key}` must be an array of strings"))
        };
        Ok(Self {
            axioms: strings("axioms")?,
            native_decide_files: strings("native_decide_files")?
                .into_iter()
                .map(PathBuf::from)
                .collect(),
        })
    }
}

/// Blanks comments and string literals, keeping every line break.
pub fn strip_comments_and_strings(src: &str) -> String {
    let chars: Vec<char> = src.chars().collect();
    let mut out = String::with_capacity(src.len());
    let blank = |c: char| if c == '\n' { '\n' } else { ' ' };
    let mut i = 0;
    let mut depth = 0_usize;
    let mut in_string = false;
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        if depth > 0 {
            if c == '/' && next == Some('-') {
                depth += 1;
                out.push_str("  ");
                i += 2;
            } else if c == '-' && next == Some('/') {
                depth -= 1;
                out.push_str("  ");
                i += 2;
            } else {
                out.push(blank(c));
                i += 1;
            }
        } else if in_string {
            if c == '\\' {
                out.push(' ');
                if let Some(n) = next {
                    out.push(blank(n));
                }
                i += 2;
            } else {
                in_string = c != '"';
                out.push(blank(c));
                i += 1;
            }
        } else if c == '/' && next == Some('-') {
            depth = 1;
            out.push_str("  ");
            i += 2;
        } else if c == '-' && next == Some('-') {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
        } else if c == '"' {
            in_string = true;
            out.push(' ');
            i += 1;
        } else if c == '\'' && !prev_is_ident(&chars, i) {
            let len = char_literal_len(&chars[i..]);
            out.extend(std::iter::repeat_n(' ', len.max(1)));
            i += len.max(1);
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

fn prev_is_ident(chars: &[char], i: usize) -> bool {
    i > 0 && is_ident(chars[i - 1])
}

/// Length of a char literal such as `'x'` or `'\n'` at the start of `rest`, else 0.
fn char_literal_len(rest: &[char]) -> usize {
    match rest {
        ['\'', '\\', _, '\'', ..] => 4,
        ['\'', c, '\'', ..] if *c != '\'' => 3,
        _ => 0,
    }
}

fn is_ident(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '.' | '\'' | '!' | '?')
}

/// Identifier-like tokens of `stripped` with their 1-based line numbers.
fn tokens(stripped: &str) -> Vec<(usize, &str)> {
    let mut out = Vec::new();
    for (index, line) in stripped.lines().enumerate() {
        let mut start = None;
        for (at, c) in line
            .char_indices()
            .chain(std::iter::once((line.len(), ' ')))
        {
            match (start, is_ident(c)) {
                (None, true) => start = Some(at),
                (Some(from), false) => {
                    out.push((index + 1, &line[from..at]));
                    start = None;
                }
                _ => {}
            }
        }
    }
    out
}

fn violation(path: &Path, line: usize, rule: &'static str, message: String) -> Violation {
    Violation {
        path: path.to_path_buf(),
        line: Some(line),
        rule,
        severity: Severity::Error,
        message,
    }
}

fn scan(path: &Path, src: &str, allow: &Allowlist) -> Vec<Violation> {
    let mut out = Vec::new();
    let stripped = strip_comments_and_strings(src);
    let toks = tokens(&stripped);
    for (at, &(line, tok)) in toks.iter().enumerate() {
        match tok {
            "sorry" => out.push(violation(
                path,
                line,
                "lean-sorry",
                "`sorry` leaves a proof unproven".into(),
            )),
            "axiom" => {
                let name = toks.get(at + 1).map_or("", |t| t.1);
                if !allow.axioms.iter().any(|a| a == name) {
                    out.push(violation(
                        path,
                        line,
                        "lean-axiom",
                        format!("axiom `{name}` is not in lean/allowlist.toml"),
                    ));
                }
            }
            "native_decide" if !allow.native_decide_files.iter().any(|f| f == path) => {
                out.push(violation(
                    path,
                    line,
                    "lean-native-decide",
                    "`native_decide` is not allowed in this file; see lean/allowlist.toml".into(),
                ));
            }
            _ => {}
        }
    }
    for (index, line) in src.lines().enumerate() {
        let problem = if line.chars().count() > MAX_LINE {
            Some(format!("line is longer than {MAX_LINE} characters"))
        } else if line.ends_with([' ', '\t']) {
            Some("trailing whitespace".to_owned())
        } else if line.contains('\t') {
            Some("tab character; use spaces".to_owned())
        } else {
            None
        };
        if let Some(message) = problem {
            out.push(violation(path, index + 1, "lean-style", message));
        }
    }
    out
}

/// True when `path` is the library root `lean/Silicon.lean` or a module under `lean/Silicon/`.
pub fn in_library(path: &Path) -> bool {
    path == Path::new("lean/Silicon.lean") || path.starts_with("lean/Silicon")
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let allow_path = Path::new("lean/allowlist.toml");
    let allow = if repo.root.join(allow_path).exists() {
        Allowlist::parse(&repo.read(allow_path)?)?
    } else {
        Allowlist::default()
    };
    let mut out = Vec::new();
    for file in &repo.files {
        if file.path.extension().is_none_or(|e| e != "lean") {
            continue;
        }
        if !in_library(&file.path) {
            out.push(Violation {
                path: file.path.clone(),
                line: None,
                rule: "lean-layout",
                severity: Severity::Error,
                message: "Lake builds only lean/Silicon.lean and lean/Silicon/; move the file"
                    .into(),
            });
        }
        if file.path.starts_with("lean") && !file.is_symlink {
            out.extend(scan(&file.path, &repo.read(&file.path)?, &allow));
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::TrackedFile;

    fn rules(src: &str) -> Vec<&'static str> {
        scan(Path::new("lean/A.lean"), src, &Allowlist::default())
            .iter()
            .map(|v| v.rule)
            .collect()
    }

    #[test]
    fn sorry_flagged() {
        assert_eq!(rules("theorem t : True := by\n  sorry\n"), ["lean-sorry"]);
        let v = scan(Path::new("a"), "x\n sorry", &Allowlist::default());
        assert_eq!(v[0].line, Some(2));
    }

    #[test]
    fn sorry_in_line_comment_ignored() {
        assert!(rules("-- sorry later\ndef x := 1\n").is_empty());
    }

    #[test]
    fn sorry_in_string_ignored() {
        assert!(rules("def s := \"sorry \\\" sorry\"\n").is_empty());
    }

    #[test]
    fn nested_block_comment_stripped() {
        let src = "/- a /- b -/ sorry -/\ndef x := 1\n";
        assert!(rules(src).is_empty());
        let src = "/- a\n/- b -/\nsorry -/\n";
        assert_eq!(
            strip_comments_and_strings(src).matches('\n').count(),
            src.matches('\n').count()
        );
    }

    #[test]
    fn axiom_declaration_flagged() {
        assert_eq!(rules("axiom foo : False\n"), ["lean-axiom"]);
        assert_eq!(rules("private axiom foo : False\n"), ["lean-axiom"]);
        assert!(rules("theorem axiomatic : True := trivial\n").is_empty());
    }

    #[test]
    fn allowlisted_axiom_passes() {
        let allow = Allowlist {
            axioms: vec!["foo".into()],
            native_decide_files: vec![],
        };
        assert!(scan(Path::new("a"), "axiom foo : False\n", &allow).is_empty());
        assert_eq!(scan(Path::new("a"), "axiom bar : False\n", &allow).len(), 1);
    }

    #[test]
    fn native_decide_outside_allowlist_flagged() {
        let src = "example : 1 = 1 := by native_decide\n";
        assert_eq!(rules(src), ["lean-native-decide"]);
        let allow = Allowlist {
            axioms: vec![],
            native_decide_files: vec![PathBuf::from("lean/A.lean")],
        };
        assert!(scan(Path::new("lean/A.lean"), src, &allow).is_empty());
    }

    #[test]
    fn line_over_100_chars_flagged() {
        let ok = format!("def x := {}\n", "a".repeat(100 - 9));
        assert!(rules(&ok).is_empty());
        let long = format!("def x := {}\n", "a".repeat(100));
        assert_eq!(rules(&long), ["lean-style"]);
    }

    #[test]
    fn trailing_whitespace_flagged() {
        assert_eq!(rules("def x := 1 \n"), ["lean-style"]);
    }

    #[test]
    fn tab_flagged() {
        assert_eq!(rules("def x :=\t1\n"), ["lean-style"]);
    }

    #[test]
    fn allowlist_parses_and_rejects_malformed() {
        let a = Allowlist::parse("axioms = [\"x\"]\nnative_decide_files = [\"lean/B.lean\"]\n")
            .unwrap();
        assert_eq!(a.axioms, ["x"]);
        assert_eq!(a.native_decide_files, [PathBuf::from("lean/B.lean")]);
        assert_eq!(Allowlist::parse("").unwrap(), Allowlist::default());
        assert!(Allowlist::parse("axioms = 3").is_err());
    }

    fn write(root: &Path, rel: &str, body: &str) {
        let full = root.join(rel);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, body).unwrap();
    }

    fn tracked(rel: &str) -> TrackedFile {
        TrackedFile {
            path: PathBuf::from(rel),
            is_symlink: false,
            is_executable: false,
        }
    }

    #[test]
    fn check_scans_tracked_lean_with_allowlist() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(root, "lean/Silicon.lean", "axiom ok : False\nsorry\n");
        write(root, "lean/allowlist.toml", "axioms = [\"ok\"]\n");
        write(root, "other/B.lean", "sorry\n");
        let files = vec![
            tracked("lean/Silicon.lean"),
            tracked("lean/allowlist.toml"),
            tracked("other/B.lean"),
        ];
        let repo = Repo::from_parts(root.to_path_buf(), files);
        let got: Vec<_> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.rule, v.path.display().to_string()))
            .collect();
        let want = [
            ("lean-sorry", "lean/Silicon.lean"),
            ("lean-layout", "other/B.lean"),
        ]
        .map(|(r, p)| (r, p.to_owned()));
        assert_eq!(got, want);
    }

    #[test]
    fn lean_sources_live_under_the_library_root() {
        for ok in [
            "lean/Silicon.lean",
            "lean/Silicon/Core.lean",
            "lean/Silicon/A/B.lean",
        ] {
            assert!(in_library(Path::new(ok)), "{ok}");
        }
        for bad in [
            "lean/Other.lean",
            "lean/Extra/A.lean",
            "other/B.lean",
            "Silicon.lean",
        ] {
            assert!(!in_library(Path::new(bad)), "{bad}");
        }
    }

    #[test]
    fn check_rejects_lean_outside_the_library() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(root, "lean/Silicon.lean", "def x := 1\n");
        write(root, "lean/Silicon/Core.lean", "def y := 1\n");
        write(root, "lean/Stray.lean", "def z := 1\n");
        let files = vec![
            tracked("lean/Silicon.lean"),
            tracked("lean/Silicon/Core.lean"),
            tracked("lean/Stray.lean"),
        ];
        let repo = Repo::from_parts(root.to_path_buf(), files);
        let got: Vec<_> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.rule, v.path.display().to_string()))
            .collect();
        assert_eq!(got, [("lean-layout", "lean/Stray.lean".to_owned())]);
    }

    #[test]
    fn check_without_lean_files_or_allowlist_is_clean() {
        let tmp = tempfile::tempdir().unwrap();
        let repo = Repo::from_parts(tmp.path().to_path_buf(), vec![]);
        assert!(check(&repo).unwrap().is_empty());
    }
}
