// SPDX-License-Identifier: Apache-2.0
//! `review-scope`: the changed files of a branch that touch an architecture path.

use std::path::Path;

use anyhow::{Context, Result};

use super::paths;
use crate::repo::git;

/// The architecture paths in the list at `base`, at the fork point, and at `HEAD`. The union
/// stops a branch from dropping a path to escape its own review. Edits that
/// are not committed do not count.
fn patterns_of_both(root: &Path, base: &str) -> Result<Vec<paths::Pattern>> {
    let fork = String::from_utf8(git(root, &["merge-base", base, "HEAD"])?)?;
    let mut patterns = Vec::new();
    for rev in [base, fork.trim(), "HEAD"] {
        let object = format!("{rev}:doc/architecture.md");
        let text = String::from_utf8(git(root, &["show", &object])?)
            .context("doc/architecture.md is not UTF-8")?;
        let list = paths::parse(&text)
            .with_context(|| format!("reading the architecture paths at {rev}"))?;
        for pattern in list {
            if !patterns.contains(&pattern) {
                patterns.push(pattern);
            }
        }
    }
    Ok(patterns)
}

/// The changed files of `HEAD` since its merge base with `base` that match
/// an architecture path, sorted. Renames count as a delete and an add, so
/// a move out of an architecture path still shows.
pub fn changed_architecture_files(root: &Path, base: &str) -> Result<Vec<String>> {
    let patterns = patterns_of_both(root, base)?;
    let range = format!("{base}...HEAD");
    let diff = git(root, &["diff", "--name-only", "--no-renames", "-z", &range])?;
    let mut files: Vec<String> = String::from_utf8(diff)
        .context("git printed a path that is not UTF-8")?
        .split('\0')
        .filter(|path| !path.is_empty() && patterns.iter().any(|p| p.matches(path)))
        .map(str::to_owned)
        .collect();
    files.sort();
    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testgit::run as git;

    const DOC: &str = "## Architecture review\n\nThese are the architecture paths.\n\n- `Cargo.toml` and `doc/adr/`\n";

    fn repo() -> tempfile::TempDir {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path();
        crate::testgit::init(dir);
        write(dir, "doc/architecture.md", DOC);
        write(dir, "Cargo.toml", "a");
        commit(dir, "base");
        git(dir, &["switch", "--quiet", "-c", "topic"]);
        tmp
    }

    fn write(dir: &Path, path: &str, text: &str) {
        let full = dir.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    }

    fn commit(dir: &Path, message: &str) {
        git(dir, &["add", "."]);
        git(dir, &["commit", "--quiet", "-m", message]);
    }

    #[test]
    fn lists_only_architecture_files_of_the_branch() {
        let tmp = repo();
        let dir = tmp.path();
        write(dir, "Cargo.toml", "b");
        write(dir, "doc/adr/0001.md", "x");
        write(dir, "src/lib.rs", "x");
        commit(dir, "change");
        assert_eq!(
            changed_architecture_files(dir, "main").unwrap(),
            ["Cargo.toml", "doc/adr/0001.md"]
        );
    }

    #[test]
    fn empty_when_no_architecture_path_changed() {
        let tmp = repo();
        write(tmp.path(), "src/lib.rs", "x");
        commit(tmp.path(), "change");
        assert!(
            changed_architecture_files(tmp.path(), "main")
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn ignores_changes_that_main_made_after_the_fork() {
        let tmp = repo();
        let dir = tmp.path();
        write(dir, "src/lib.rs", "x");
        commit(dir, "topic");
        git(dir, &["switch", "--quiet", "main"]);
        write(dir, "Cargo.toml", "main moved");
        commit(dir, "main");
        git(dir, &["switch", "--quiet", "topic"]);
        assert!(changed_architecture_files(dir, "main").unwrap().is_empty());
    }

    #[test]
    fn a_move_out_of_an_architecture_path_shows() {
        let tmp = repo();
        let dir = tmp.path();
        git(dir, &["mv", "Cargo.toml", "moved.toml"]);
        commit(dir, "move");
        assert_eq!(
            changed_architecture_files(dir, "main").unwrap(),
            ["Cargo.toml"]
        );
    }

    #[test]
    fn unknown_base_is_an_error() {
        let tmp = repo();
        assert!(changed_architecture_files(tmp.path(), "nope").is_err());
    }

    #[test]
    fn missing_section_is_an_error_with_context() {
        let tmp = repo();
        write(tmp.path(), "doc/architecture.md", "# T\n");
        commit(tmp.path(), "break the list");
        let message = format!(
            "{:#}",
            changed_architecture_files(tmp.path(), "main").unwrap_err()
        );
        assert!(message.contains("architecture paths"), "{message}");
    }

    #[test]
    fn removing_a_path_from_the_list_does_not_hide_its_change() {
        let tmp = repo();
        let dir = tmp.path();
        write(
            dir,
            "doc/architecture.md",
            &DOC.replace("`Cargo.toml` and ", ""),
        );
        write(dir, "Cargo.toml", "b");
        commit(dir, "drop the path and change the file");
        assert_eq!(
            changed_architecture_files(dir, "main").unwrap(),
            ["Cargo.toml"]
        );
    }

    #[test]
    fn uncommitted_list_edits_do_not_count() {
        let tmp = repo();
        let dir = tmp.path();
        write(dir, "src/lib.rs", "x");
        commit(dir, "change");
        write(dir, "doc/architecture.md", "broken");
        assert!(changed_architecture_files(dir, "main").unwrap().is_empty());
    }

    #[test]
    fn a_path_that_main_adds_after_the_fork_counts() {
        let tmp = repo();
        let dir = tmp.path();
        write(dir, "extra.txt", "a");
        commit(dir, "topic changes the later path");
        git(dir, &["switch", "--quiet", "main"]);
        write(dir, "doc/architecture.md", &format!("{DOC}- `extra.txt`\n"));
        commit(dir, "main protects extra.txt");
        git(dir, &["switch", "--quiet", "topic"]);
        assert_eq!(
            changed_architecture_files(dir, "main").unwrap(),
            ["extra.txt"]
        );
    }
}
