use std::path::{Path, PathBuf};

use anyhow::Result;

use crate::repo::{Repo, TrackedFile};
use crate::violation::{Severity, Violation};

/// Level-2 headings of every L1 `AGENTS.md`, in order (design spec section 4.2).
pub const L1_HEADINGS: [&str; 5] = [
    "Purpose",
    "Owns",
    "Invariants",
    "Dependencies",
    "How to test",
];

const ROOT_LIMIT: usize = 100;
const L1_LIMIT: usize = 60;

/// Returns the maximum line count of an `AGENTS.md` at `path`.
pub fn line_limit(path: &Path) -> usize {
    if path == Path::new("AGENTS.md") {
        ROOT_LIMIT
    } else {
        L1_LIMIT
    }
}

/// Returns the text of each level-2 heading, outside code fences.
pub fn level2_headings(md: &str) -> Vec<String> {
    let mut in_fence = false;
    let mut out = Vec::new();
    for line in md.lines() {
        if line.starts_with("```") || line.starts_with("~~~") {
            in_fence = !in_fence;
        } else if !in_fence && let Some(title) = line.strip_prefix("## ") {
            out.push(title.trim().to_owned());
        }
    }
    out
}

/// Returns the 1-based lines of list items under `## Hard rules` that lack text after `Check:`.
pub fn hard_rules_without_check(md: &str) -> Vec<usize> {
    let mut in_section = false;
    let mut out = Vec::new();
    for (i, line) in md.lines().enumerate() {
        if let Some(title) = line.strip_prefix("## ") {
            in_section = title.trim() == "Hard rules";
        } else if in_section && is_list_item(line) && !has_check(line) {
            out.push(i + 1);
        }
    }
    out
}

/// True when non-whitespace text follows `Check:`.
fn has_check(line: &str) -> bool {
    line.split_once("Check:")
        .is_some_and(|(_, rest)| !rest.trim().is_empty())
}

fn is_list_item(line: &str) -> bool {
    let line = line.trim_start();
    line.starts_with("- ")
        || line.starts_with("* ")
        || line
            .split_once(". ")
            .is_some_and(|(n, _)| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

fn violation(path: &Path, line: Option<usize>, rule: &'static str, message: String) -> Violation {
    Violation {
        path: path.to_path_buf(),
        line,
        rule,
        severity: Severity::Error,
        message,
    }
}

/// Returns the `guidance-pair` problem of a tracked `CLAUDE.md`, if any.
fn claude_md_problem(repo: &Repo, claude: &TrackedFile) -> Option<&'static str> {
    let agents = claude.path.with_file_name("AGENTS.md");
    if !repo.files.iter().any(|f| f.path == agents) {
        Some("CLAUDE.md has no AGENTS.md next to it")
    } else if !claude.is_symlink {
        Some("CLAUDE.md must be a symlink to AGENTS.md")
    } else if std::fs::read_link(repo.root.join(&claude.path))
        .ok()
        .as_deref()
        != Some(Path::new("AGENTS.md"))
    {
        Some("CLAUDE.md symlink target must be AGENTS.md")
    } else {
        None
    }
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    for file in &repo.files {
        let name = file.path.file_name().unwrap_or_default();
        if name == "CLAUDE.md" {
            if let Some(message) = claude_md_problem(repo, file) {
                out.push(violation(&file.path, None, "guidance-pair", message.into()));
            }
            continue;
        }
        if name != "AGENTS.md" {
            continue;
        }
        let is_root = file.path == Path::new("AGENTS.md");
        let text = repo.read(&file.path)?;

        let limit = line_limit(&file.path);
        let lines = text.lines().count();
        if lines > limit {
            out.push(violation(
                &file.path,
                None,
                "guidance-limit",
                format!("{lines} lines; the limit is {limit}"),
            ));
        }

        let claude: PathBuf = file.path.with_file_name("CLAUDE.md");
        if !repo.files.iter().any(|f| f.path == claude) {
            out.push(violation(
                &claude,
                None,
                "guidance-pair",
                "AGENTS.md has no CLAUDE.md next to it".into(),
            ));
        }

        if is_root {
            for line in hard_rules_without_check(&text) {
                out.push(Violation {
                    severity: Severity::Warning,
                    ..violation(
                        &file.path,
                        Some(line),
                        "guidance-hard-rule",
                        "hard rule names no check; add `Check:`".into(),
                    )
                });
            }
        } else if level2_headings(&text) != L1_HEADINGS {
            out.push(violation(
                &file.path,
                None,
                "guidance-headings",
                format!("level-2 headings must be {}", L1_HEADINGS.join(", ")),
            ));
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(n: usize) -> String {
        "x\n".repeat(n)
    }

    fn l1_body() -> String {
        L1_HEADINGS.map(|h| format!("## {h}\n\ntext\n")).concat()
    }

    /// Builds a repo from `(path, contents)`; `CLAUDE.md` entries become symlinks to `AGENTS.md`.
    fn repo_with(files: &[(&str, &str)]) -> (tempfile::TempDir, Repo) {
        let tmp = tempfile::tempdir().unwrap();
        let mut tracked = Vec::new();
        for (path, body) in files {
            let full = tmp.path().join(path);
            std::fs::create_dir_all(full.parent().unwrap()).unwrap();
            let is_symlink = path.ends_with("CLAUDE.md");
            if is_symlink {
                std::os::unix::fs::symlink("AGENTS.md", &full).unwrap();
            } else {
                std::fs::write(&full, body).unwrap();
            }
            tracked.push(TrackedFile {
                path: (*path).into(),
                is_symlink,
            });
        }
        let repo = Repo::from_parts(tmp.path().to_path_buf(), tracked);
        (tmp, repo)
    }

    fn rules(repo: &Repo) -> Vec<&'static str> {
        check(repo).unwrap().iter().map(|v| v.rule).collect()
    }

    #[test]
    fn root_agents_md_max_100_lines() {
        let (_t, ok) = repo_with(&[("AGENTS.md", &lines(100)), ("CLAUDE.md", "")]);
        assert!(rules(&ok).is_empty());
        let (_t, bad) = repo_with(&[("AGENTS.md", &lines(101)), ("CLAUDE.md", "")]);
        assert_eq!(rules(&bad), ["guidance-limit"]);
    }

    #[test]
    fn l1_agents_md_max_60_lines() {
        let body = |n: usize| format!("{}{}", l1_body(), lines(n - 15));
        let (_t, ok) = repo_with(&[
            ("crates/x/AGENTS.md", &body(60)),
            ("crates/x/CLAUDE.md", ""),
        ]);
        assert!(rules(&ok).is_empty());
        let (_t, bad) = repo_with(&[
            ("crates/x/AGENTS.md", &body(61)),
            ("crates/x/CLAUDE.md", ""),
        ]);
        assert_eq!(rules(&bad), ["guidance-limit"]);
    }

    #[test]
    fn claude_md_must_be_symlink_in_index() {
        let (_t, mut repo) = repo_with(&[("AGENTS.md", "x\n"), ("CLAUDE.md", "")]);
        repo.files[1].is_symlink = false;
        assert_eq!(rules(&repo), ["guidance-pair"]);
    }

    #[test]
    fn claude_md_symlink_must_target_agents_md() {
        let (tmp, repo) = repo_with(&[("AGENTS.md", "x\n"), ("CLAUDE.md", "")]);
        std::fs::remove_file(tmp.path().join("CLAUDE.md")).unwrap();
        std::os::unix::fs::symlink("other.md", tmp.path().join("CLAUDE.md")).unwrap();
        assert_eq!(rules(&repo), ["guidance-pair"]);
    }

    #[test]
    fn claude_md_without_agents_md_rejected() {
        let (_t, link) = repo_with(&[("crates/x/CLAUDE.md", "")]);
        assert_eq!(rules(&link), ["guidance-pair"]);

        let (tmp, mut plain) = repo_with(&[("crates/x/CLAUDE.md", "")]);
        let full = tmp.path().join("crates/x/CLAUDE.md");
        std::fs::remove_file(&full).unwrap();
        std::fs::write(&full, "# Rules\n").unwrap();
        plain.files[0].is_symlink = false;
        assert_eq!(rules(&plain), ["guidance-pair"]);
    }

    #[test]
    fn every_agents_md_has_claude_md() {
        let (_t, repo) = repo_with(&[("crates/x/AGENTS.md", &l1_body())]);
        assert_eq!(rules(&repo), ["guidance-pair"]);
    }

    #[test]
    fn l1_headings_in_order() {
        let headings = |hs: &[&str]| {
            hs.iter()
                .fold(String::new(), |acc, h| acc + "## " + h + "\n")
        };
        let level2 = level2_headings(&headings(&L1_HEADINGS));
        assert_eq!(level2, L1_HEADINGS);

        let missing = headings(&["Purpose", "Owns", "Invariants", "Dependencies"]);
        let reordered = headings(&[
            "Owns",
            "Purpose",
            "Invariants",
            "Dependencies",
            "How to test",
        ]);
        for bad in [missing, reordered] {
            let (_t, repo) = repo_with(&[("lean/AGENTS.md", &bad), ("lean/CLAUDE.md", "")]);
            assert_eq!(rules(&repo), ["guidance-headings"]);
        }
        let (_t, ok) = repo_with(&[("lean/AGENTS.md", &l1_body()), ("lean/CLAUDE.md", "")]);
        assert!(rules(&ok).is_empty());
    }

    #[test]
    fn headings_ignore_code_fences_and_other_levels() {
        let md = "# T\n## A\n```\n## B\n```\n### C\n## D\n";
        assert_eq!(level2_headings(md), ["A", "D"]);
    }

    #[test]
    fn bare_check_label_counts_as_missing() {
        let md = "## Hard rules\n\n- Rule. Check:\n- Rule. Check:   \n- Rule. Check: `x`\n";
        assert_eq!(hard_rules_without_check(md), [3, 4]);
    }

    #[test]
    fn hard_rule_without_check_warns() {
        let md = "## Hard rules\n\n- Good. Check: `x`.\n- Bad rule.\n1. Numbered bad.\n\n## Next\n\n- Not a rule.\n";
        assert_eq!(hard_rules_without_check(md), [4, 5]);
        let (_t, repo) = repo_with(&[("AGENTS.md", md), ("CLAUDE.md", "")]);
        let got = check(&repo).unwrap();
        assert_eq!(got.len(), 2);
        assert!(got.iter().all(|v| v.severity == Severity::Warning));
        assert!(got.iter().all(|v| !v.severity.fails_run()));
    }
}
