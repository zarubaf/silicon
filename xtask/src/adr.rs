// SPDX-License-Identifier: Apache-2.0
//! The rule `adr-frozen`: an ADR whose status was `accepted` at the merge base with `origin/main`
//! changes only in its `- Status:` line (ADR 0001). A new ADR is free. On `origin/main` itself the
//! base is the previous commit. A clone without `origin/main` skips the check, and a CI run (the
//! variable `CI`) fails.

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

/// What the check compares with.
enum Base {
    Commit(String),
    /// There is no earlier commit to compare with.
    Skip,
    /// `origin/main` or the merge base is missing.
    Missing,
}

/// The merge base with `origin/main`. On `origin/main` itself the base is the previous commit, so
/// that the run on `main` catches a direct edit.
fn base_commit(root: &Path) -> Base {
    let rev = |args: &[&str]| -> Option<String> {
        let out = git(root, args).ok()?;
        Some(String::from_utf8(out).ok()?.trim().to_owned())
    };
    let Some(merge_base) = rev(&["merge-base", "HEAD", BASE_REF]) else {
        return Base::Missing;
    };
    if rev(&["rev-parse", "HEAD"]).as_deref() != Some(merge_base.as_str()) {
        return Base::Commit(merge_base);
    }
    match rev(&["rev-parse", "--verify", "--quiet", "HEAD~1"]) {
        Some(parent) => Base::Commit(parent),
        None => Base::Skip,
    }
}

/// The check. `ci` is true on a CI run, where a missing base is a failure and not a skip.
pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    check_with(repo, std::env::var_os("CI").is_some())
}

fn check_with(repo: &Repo, ci: bool) -> Result<Vec<Violation>> {
    let base = match base_commit(&repo.root) {
        Base::Commit(base) => base,
        Base::Missing if ci => {
            return Ok(vec![Violation {
                path: PathBuf::from(ADR_DIR),
                line: None,
                rule: "adr-frozen",
                severity: Severity::Error,
                message: format!(
                    "`{BASE_REF}` or the merge base is missing, so the check cannot compare the ADRs;                      fetch the full history (`fetch-depth: 0`) and `{BASE_REF}`"
                ),
            }]);
        }
        Base::Skip | Base::Missing => return Ok(Vec::new()),
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
        run(dir, &["commit", "--quiet", "-m", "new"]);
        let repo = Repo::discover_in(dir).unwrap();
        assert!(check_with(&repo, true).unwrap().is_empty());
        std::fs::write(dir.join("doc/adr/0001-a.md"), ACCEPTED.replace("A.", "B.")).unwrap();
        let found = check_with(&repo, true).unwrap();
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].rule, "adr-frozen");
    }

    fn repository() -> tempfile::TempDir {
        let tmp = tempfile::tempdir().unwrap();
        init(tmp.path());
        std::fs::create_dir_all(tmp.path().join(ADR_DIR)).unwrap();
        std::fs::write(tmp.path().join("doc/adr/0001-a.md"), ACCEPTED).unwrap();
        run(tmp.path(), &["add", "."]);
        run(tmp.path(), &["commit", "--quiet", "-m", "x"]);
        tmp
    }

    #[test]
    fn missing_base_skips_locally_and_fails_in_ci() {
        let tmp = repository();
        let repo = Repo::discover_in(tmp.path()).unwrap();
        assert!(check_with(&repo, false).unwrap().is_empty());
        let found = check_with(&repo, true).unwrap();
        assert_eq!(found.len(), 1, "{found:?}");
        assert!(found[0].message.contains("fetch-depth"));
    }

    #[test]
    fn edit_on_main_is_caught_against_the_previous_commit() {
        let tmp = repository();
        let dir = tmp.path();
        std::fs::write(dir.join("doc/adr/0001-a.md"), ACCEPTED.replace("A.", "B.")).unwrap();
        run(dir, &["commit", "--quiet", "-am", "edit"]);
        run(dir, &["update-ref", "refs/remotes/origin/main", "HEAD"]);
        let repo = Repo::discover_in(dir).unwrap();
        let found = check_with(&repo, true).unwrap();
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].rule, "adr-frozen");
    }

    #[test]
    fn clean_main_passes() {
        let tmp = repository();
        let dir = tmp.path();
        std::fs::write(dir.join("doc/adr/0002-b.md"), ACCEPTED).unwrap();
        run(dir, &["add", "."]);
        run(dir, &["commit", "--quiet", "-m", "new"]);
        run(dir, &["update-ref", "refs/remotes/origin/main", "HEAD"]);
        let repo = Repo::discover_in(dir).unwrap();
        assert!(check_with(&repo, true).unwrap().is_empty());
    }
}
