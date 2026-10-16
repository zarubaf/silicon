// SPDX-License-Identifier: Apache-2.0
//! The rule `adr-frozen`: an ADR whose status was `accepted` at the merge base with `origin/main`
//! changes only in its `- Status:` line (ADR 0001). A new ADR is free. The check skips when the
//! clone has no `origin/main`, because it has no base to compare with.

use std::path::{Path, PathBuf};

use anyhow::Result;

use crate::repo::{Repo, git};
use crate::violation::{Severity, Violation};

const ADR_DIR: &str = "doc/adr";
const BASE_REF: &str = "origin/main";
const STATUS_PREFIX: &str = "- Status:";

/// The status text of an ADR, or `None` when the ADR has no status line.
fn status(text: &str) -> Option<&str> {
    text.lines()
        .find_map(|l| l.strip_prefix(STATUS_PREFIX))
        .map(str::trim)
}

/// The text without its status line, so that two texts compare equal outside it.
fn without_status(text: &str) -> String {
    text.lines()
        .filter(|l| !l.starts_with(STATUS_PREFIX))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The problem with the change from `base` to `now` of one ADR, or `None` when the change is free.
/// `now` is `None` for a deleted ADR.
pub fn problem(base: &str, now: Option<&str>) -> Option<String> {
    if !status(base).is_some_and(|s| s.starts_with("accepted")) {
        return None;
    }
    let Some(now) = now else {
        return Some("an accepted ADR is deleted; supersede it with a new ADR".to_owned());
    };
    if without_status(base) != without_status(now) {
        return Some(
            "an accepted ADR changes outside its status line; write a new ADR that supersedes it \
             and change only the status line of this one"
                .to_owned(),
        );
    }
    match status(now) {
        Some(s) if s.starts_with("accepted") || s.starts_with("superseded by") => None,
        _ => Some(
            "the status of an accepted ADR can become only `accepted, partly superseded by ADR \
             NNNN` or `superseded by ADR NNNN`"
                .to_owned(),
        ),
    }
}

fn merge_base(root: &Path) -> Option<String> {
    git(root, &["rev-parse", "--verify", "--quiet", BASE_REF]).ok()?;
    let out = git(root, &["merge-base", "HEAD", BASE_REF]).ok()?;
    Some(String::from_utf8(out).ok()?.trim().to_owned())
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let Some(base) = merge_base(&repo.root) else {
        return Ok(Vec::new());
    };
    let listing = git(
        &repo.root,
        &["ls-tree", "-r", "--name-only", &base, "--", ADR_DIR],
    )?;
    let mut out = Vec::new();
    for name in String::from_utf8(listing)?.lines() {
        let path = PathBuf::from(name);
        if path.extension().is_none_or(|e| e != "md") {
            continue;
        }
        let old = String::from_utf8(git(&repo.root, &["show", &format!("{base}:{name}")])?)?;
        let now = repo.read(&path).ok();
        if let Some(message) = problem(&old, now.as_deref()) {
            out.push(Violation {
                path,
                line: None,
                rule: "adr-frozen",
                severity: Severity::Error,
                message,
            });
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testgit::{init, run};

    const ACCEPTED: &str =
        "# 1. T\n\n- Status: accepted\n- Date: 2026-10-08\n\n## Decision\n\nA.\n";

    #[test]
    fn body_edit_fails() {
        let now = ACCEPTED.replace("A.", "B.");
        assert!(problem(ACCEPTED, Some(&now)).is_some());
    }

    #[test]
    fn status_edit_passes() {
        let now = ACCEPTED.replace("accepted", "accepted, partly superseded by ADR 0002");
        assert_eq!(problem(ACCEPTED, Some(&now)), None);
        let now = ACCEPTED.replace("accepted", "superseded by ADR 0002");
        assert_eq!(problem(ACCEPTED, Some(&now)), None);
    }

    #[test]
    fn status_back_to_draft_fails() {
        let now = ACCEPTED.replace("accepted", "proposed");
        assert!(problem(ACCEPTED, Some(&now)).is_some());
    }

    #[test]
    fn deletion_fails() {
        assert!(problem(ACCEPTED, None).is_some());
    }

    #[test]
    fn proposed_adr_is_free() {
        let base = ACCEPTED.replace("accepted", "proposed");
        assert_eq!(problem(&base, Some("anything")), None);
    }

    #[test]
    fn new_adr_passes_and_edit_fails_in_a_repository() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path();
        init(dir);
        std::fs::create_dir_all(dir.join(ADR_DIR)).unwrap();
        std::fs::write(dir.join("doc/adr/0001-a.md"), ACCEPTED).unwrap();
        run(dir, &["add", "."]);
        run(dir, &["commit", "--quiet", "-m", "x"]);
        run(dir, &["update-ref", "refs/remotes/origin/main", "HEAD"]);
        std::fs::write(dir.join("doc/adr/0002-b.md"), ACCEPTED).unwrap();
        run(dir, &["add", "."]);
        let repo = Repo::discover_in(dir).unwrap();
        assert!(check(&repo).unwrap().is_empty());
        std::fs::write(dir.join("doc/adr/0001-a.md"), ACCEPTED.replace("A.", "B.")).unwrap();
        let found = check(&repo).unwrap();
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].rule, "adr-frozen");
    }
}
