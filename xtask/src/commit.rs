//! Commit conventions and the "refactor first, then change behavior" rule.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

const TYPES: &[&str] = &[
    "feat", "fix", "refactor", "perf", "test", "docs", "build", "ci", "chore", "style", "revert",
];
const FIXED_SCOPES: &[&str] = &["lean", "doc", "adr", "ci", "xtask", "design"];
const MAX_SUBJECT: usize = 72;
const FORBIDDEN_TRAILER_VALUES: &[&str] = &[
    "claude",
    "codex",
    "gpt",
    "noreply@anthropic.com",
    "noreply@openai.com",
];

/// Scopes a commit may name: workspace members plus the fixed list.
pub fn allowed_scopes() -> Result<Vec<String>> {
    let metadata = cargo_metadata::MetadataCommand::new()
        .no_deps()
        .exec()
        .context("reading cargo metadata")?;
    let mut scopes: Vec<String> = metadata
        .workspace_packages()
        .iter()
        .map(|p| p.name.to_string())
        .collect();
    scopes.extend(FIXED_SCOPES.iter().map(|s| (*s).to_owned()));
    Ok(scopes)
}

/// Parses `type(scope)!: text`. Returns `None` when the subject is malformed,
/// else the scope, which is empty when the subject names none.
fn parse_subject(subject: &str) -> Option<&str> {
    let (head, text) = subject.split_once(": ")?;
    if text.trim().is_empty() {
        return None;
    }
    let head = head.strip_suffix('!').unwrap_or(head);
    let (kind, scope) = match head.split_once('(') {
        Some((kind, rest)) => (kind, rest.strip_suffix(')').filter(|s| !s.is_empty())?),
        None => (head, ""),
    };
    if !TYPES.contains(&kind) || scope.contains(['(', ')']) {
        return None;
    }
    Some(scope)
}

/// True when `word` occurs in `text` with no alphanumeric neighbor.
fn contains_word(text: &str, word: &str) -> bool {
    text.match_indices(word).any(|(i, _)| {
        let before = text[..i].chars().next_back();
        let after = text[i + word.len()..].chars().next();
        !before.is_some_and(char::is_alphanumeric) && !after.is_some_and(char::is_alphanumeric)
    })
}

/// Checks a commit message. Returns one problem string per violation.
pub fn check_message(msg: &str, scopes: &[String]) -> Vec<String> {
    let mut problems = Vec::new();
    let subject = msg.lines().next().unwrap_or("");
    match parse_subject(subject) {
        None => problems.push(format!(
            "[commit-subject] not a Conventional Commit `type(scope): subject`: {subject:?}"
        )),
        Some(scope) if !scope.is_empty() && !scopes.iter().any(|s| s == scope) => {
            problems.push(format!("[commit-scope] unknown scope `{scope}`"));
        }
        Some(_) => {}
    }
    let length = subject.chars().count();
    if length > MAX_SUBJECT {
        problems.push(format!(
            "[commit-length] subject has {length} characters; the limit is {MAX_SUBJECT}"
        ));
    }
    for line in msg.lines() {
        let lower = line.to_lowercase();
        if let Some(value) = lower.strip_prefix("co-authored-by:")
            && FORBIDDEN_TRAILER_VALUES
                .iter()
                .any(|f| contains_word(value, f))
        {
            problems.push(format!(
                "[commit-attribution] agent attribution trailer: {line:?}"
            ));
        }
        if lower
            .trim_start_matches(|c: char| !c.is_alphanumeric())
            .starts_with("generated with")
        {
            problems.push(format!(
                "[commit-attribution] generated-with line: {line:?}"
            ));
        }
    }
    problems
}

/// True for test expectation files: snapshots and corpus `expected` files.
pub fn is_expectation(path: &Path) -> bool {
    let parts: Vec<_> = path.iter().map(|p| p.to_string_lossy()).collect();
    if parts.iter().any(|p| p == "snapshots") {
        return true;
    }
    // `tests/corpus/**/expected/**`: `expected` is a directory below the corpus.
    let Some(start) = parts
        .windows(2)
        .position(|w| w[0] == "tests" && w[1] == "corpus")
    else {
        return false;
    };
    let dirs = parts
        .get(start + 2..parts.len().saturating_sub(1))
        .unwrap_or(&[]);
    dirs.iter().any(|p| p == "expected")
}

fn is_test_code(path: &Path) -> bool {
    path.iter().any(|p| p == "tests")
}

/// Checks the files a commit changes against its type.
pub fn check_paths(commit_type: &str, paths: &[PathBuf]) -> Vec<String> {
    let mut problems = Vec::new();
    let has_expectation = paths.iter().any(|p| is_expectation(p));
    if commit_type == "refactor" && has_expectation {
        problems.push(
            "[commit-refactor-expectations] a refactor commit must not change test expectations"
                .to_owned(),
        );
    }
    let has_lean = paths.iter().any(|p| p.starts_with("lean"));
    let has_crates = paths.iter().any(|p| p.starts_with("crates"));
    if has_lean && has_crates {
        problems.push(
            "[commit-spec-impl] a commit must not change `lean/` and `crates/` together".to_owned(),
        );
    }
    let has_other = paths.iter().any(|p| !is_expectation(p) && !is_test_code(p));
    if has_expectation && has_other {
        problems.push("[commit-expectations-code] a commit must not change test expectations and non-test code".to_owned());
    }
    problems
}

fn commit_type(msg: &str) -> &str {
    let subject = msg.lines().next().unwrap_or("");
    let end = subject
        .find(|c: char| !c.is_ascii_lowercase())
        .unwrap_or(subject.len());
    &subject[..end]
}

/// Checks one message file, for the `commit-msg` hook. Returns the problems.
pub fn check_message_file(file: &Path) -> Result<Vec<String>> {
    let msg =
        std::fs::read_to_string(file).with_context(|| format!("reading {}", file.display()))?;
    Ok(check_message(&strip_comments(&msg), &allowed_scopes()?))
}

/// Drops git comment lines and everything after the scissors line.
fn strip_comments(raw: &str) -> String {
    raw.lines()
        .take_while(|l| !l.starts_with("# ------------------------ >8"))
        .filter(|l| !l.starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The git revision range that `commit-check` covers for `base`.
/// An empty base or GitHub's all-zeros SHA (a new branch) selects the whole history up to `HEAD`.
pub fn range_for_base(base: &str) -> String {
    let base = base.trim();
    if base.is_empty() || base.bytes().all(|b| b == b'0') {
        "HEAD".to_string()
    } else {
        format!("{base}..HEAD")
    }
}

/// Checks every non-merge commit in `range`. Returns `sha: problem` lines.
pub fn check_range(dir: &Path, range: &str, scopes: &[String]) -> Result<Vec<String>> {
    let shas = git(dir, &["log", "--no-merges", "--format=%H", "-z", range])?;
    let mut problems = Vec::new();
    for sha in shas.split('\0').filter(|s| !s.is_empty()) {
        let msg = git(dir, &["log", "-1", "--format=%B", sha])?;
        let names = git(
            dir,
            &[
                "diff-tree",
                "--root",
                "--no-commit-id",
                "--name-only",
                "-r",
                "-z",
                sha,
            ],
        )?;
        let paths: Vec<PathBuf> = names
            .split('\0')
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();
        let mut found = check_message(&msg, scopes);
        found.extend(check_paths(commit_type(&msg), &paths));
        let short = &sha[..sha.len().min(7)];
        problems.extend(found.into_iter().map(|p| format!("{short}: {p}")));
    }
    Ok(problems)
}

fn git(dir: &Path, args: &[&str]) -> Result<String> {
    let out = crate::gitcmd::git()
        .args(args)
        .current_dir(dir)
        .output()
        .context("running git")?;
    if !out.status.success() {
        bail!(
            "git {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(String::from_utf8(out.stdout)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scopes() -> Vec<String> {
        ["xtask", "lean"].map(String::from).to_vec()
    }

    fn paths(list: &[&str]) -> Vec<PathBuf> {
        list.iter().map(PathBuf::from).collect()
    }

    #[test]
    fn accepts_conventional_subjects() {
        assert!(check_message("feat(xtask): add x", &scopes()).is_empty());
        assert!(check_message("feat!: x", &scopes()).is_empty());
    }

    fn fired(problems: &[String], rule: &str) -> bool {
        problems.iter().any(|p| p.starts_with(&format!("[{rule}]")))
    }

    #[test]
    fn regenerated_with_is_not_attribution() {
        let msg = "test: x\n\nSnapshots regenerated with insta";
        assert!(check_message(msg, &scopes()).is_empty());
    }

    #[test]
    fn emoji_generated_with_is_attribution() {
        let msg =
            "feat: x\n\n\u{1F916} Generated with [Claude Code](https://claude.com/claude-code)";
        assert!(fired(&check_message(msg, &scopes()), "commit-attribution"));
    }

    #[test]
    fn trailer_matching_uses_whole_words() {
        for bad in [
            "co-authored-by: claude <x@y>",
            "Co-Authored-By: Codex <c@x>",
            "Co-Authored-By: Bot <noreply@openai.com>",
            "Co-Authored-By: GPT-5 <x@y>",
        ] {
            let msg = format!("feat: x\n\n{bad}");
            assert!(
                fired(&check_message(&msg, &scopes()), "commit-attribution"),
                "{bad}"
            );
        }
        let ok = "feat: x\n\nCo-Authored-By: Egypt Smith <e@x>";
        assert!(check_message(ok, &scopes()).is_empty());
    }

    #[test]
    fn breaking_marker_with_scope_passes() {
        assert!(check_message("feat(xtask)!: x", &scopes()).is_empty());
    }

    #[test]
    fn default_revert_subject_fails_closed() {
        let problems = check_message("Revert \"feat(x): y\"", &scopes());
        assert!(fired(&problems, "commit-subject"));
    }

    #[test]
    fn scissors_line_ends_the_message() {
        let raw = "feat: x\n# comment\n# ------------------------ >8 ------------------------\nGenerated with diff";
        assert_eq!(strip_comments(raw), "feat: x");
    }

    #[test]
    fn expected_must_be_below_the_corpus() {
        assert!(!is_expectation(Path::new("expected/tests/corpus/b/o.v")));
        assert!(!is_expectation(Path::new(
            "crates/a/tests/corpus/b/expected"
        )));
        assert!(!is_expectation(Path::new("crates/a/tests/corpus/expected")));
    }

    #[test]
    fn rejects_non_conventional_subject() {
        assert!(fired(&check_message("Add x", &scopes()), "commit-subject"));
    }

    #[test]
    fn rejects_unknown_scope() {
        assert!(fired(
            &check_message("feat(unknown): x", &scopes()),
            "commit-scope"
        ));
    }

    #[test]
    fn rejects_long_subject() {
        let ok = format!("feat: {}", "a".repeat(72 - 6));
        let long = format!("feat: {}", "a".repeat(72 - 5));
        assert!(check_message(&ok, &scopes()).is_empty());
        assert_eq!(long.chars().count(), 73);
        assert!(fired(&check_message(&long, &scopes()), "commit-length"));
    }

    #[test]
    fn rejects_agent_attribution() {
        let claude = "feat: x\n\nCo-Authored-By: Claude <noreply@anthropic.com>";
        assert!(fired(
            &check_message(claude, &scopes()),
            "commit-attribution"
        ));
        let generated = "feat: x\n\nGenerated with a tool";
        assert!(fired(
            &check_message(generated, &scopes()),
            "commit-attribution"
        ));
    }

    #[test]
    fn allows_human_co_author() {
        let msg = "feat: x\n\nCo-Authored-By: Ada <ada@x>";
        assert!(check_message(msg, &scopes()).is_empty());
    }

    #[test]
    fn recognizes_expectations() {
        assert!(is_expectation(Path::new("crates/a/snapshots/x.snap")));
        assert!(is_expectation(Path::new(
            "crates/a/tests/corpus/b/expected/o.v"
        )));
        assert!(!is_expectation(Path::new("crates/a/src/lib.rs")));
        assert!(!is_expectation(Path::new(
            "crates/a/tests/corpus/b/input.si"
        )));
    }

    #[test]
    fn refactor_must_not_change_expectations() {
        let p = paths(&["crates/a/snapshots/x.snap"]);
        assert!(fired(
            &check_paths("refactor", &p),
            "commit-refactor-expectations"
        ));
    }

    #[test]
    fn lean_and_crates_do_not_mix() {
        let p = paths(&["lean/A.lean", "crates/a/src/lib.rs"]);
        assert!(fired(&check_paths("feat", &p), "commit-spec-impl"));
    }

    #[test]
    fn test_commit_may_change_expectations_alone() {
        let p = paths(&["crates/a/snapshots/x.snap"]);
        assert!(check_paths("test", &p).is_empty());
    }

    #[test]
    fn expectations_and_code_do_not_mix() {
        let p = paths(&["crates/a/snapshots/x.snap", "crates/a/src/lib.rs"]);
        assert!(fired(&check_paths("feat", &p), "commit-expectations-code"));
    }

    use crate::testgit::run;

    fn init(dir: &Path) {
        run(dir, &["init", "--quiet"]);
        run(dir, &["config", "user.email", "t@example.com"]);
        run(dir, &["config", "user.name", "t"]);
        run(dir, &["config", "commit.gpgsign", "false"]);
    }

    fn commit(dir: &Path, file: &str, msg: &str) {
        std::fs::write(dir.join(file), msg).unwrap();
        run(dir, &["add", "."]);
        run(dir, &["commit", "--quiet", "-m", msg]);
    }

    #[test]
    fn range_includes_root_commit() {
        let tmp = tempfile::tempdir().unwrap();
        init(tmp.path());
        commit(tmp.path(), "a", "bad root");
        let problems = check_range(tmp.path(), "HEAD", &scopes()).unwrap();
        assert_eq!(problems.len(), 1, "{problems:?}");
    }

    #[test]
    fn merge_commits_skipped() {
        let tmp = tempfile::tempdir().unwrap();
        let d = tmp.path();
        init(d);
        commit(d, "a", "feat: a");
        run(d, &["checkout", "--quiet", "-b", "side"]);
        commit(d, "b", "feat: b");
        run(d, &["checkout", "--quiet", "-"]);
        commit(d, "c", "feat: c");
        run(
            d,
            &["merge", "--quiet", "--no-ff", "-m", "Merge side", "side"],
        );
        assert!(check_range(d, "HEAD", &scopes()).unwrap().is_empty());
    }

    #[test]
    fn range_for_base_selects_history() {
        assert_eq!(range_for_base("main"), "main..HEAD");
        assert_eq!(range_for_base(""), "HEAD");
        assert_eq!(range_for_base(&"0".repeat(40)), "HEAD");
    }

    #[test]
    fn zero_base_checks_root_and_normal_base_checks_tail() {
        let tmp = tempfile::tempdir().unwrap();
        let d = tmp.path();
        init(d);
        commit(d, "a", "bad root");
        commit(d, "b", "feat: b");
        let zeros = range_for_base(&"0".repeat(40));
        assert_eq!(check_range(d, &zeros, &scopes()).unwrap().len(), 1);
        let tail = range_for_base("HEAD~1");
        assert!(check_range(d, &tail, &scopes()).unwrap().is_empty());
    }

    #[test]
    fn empty_range_passes() {
        let tmp = tempfile::tempdir().unwrap();
        init(tmp.path());
        commit(tmp.path(), "a", "feat: a");
        assert!(
            check_range(tmp.path(), "HEAD..HEAD", &scopes())
                .unwrap()
                .is_empty()
        );
    }
}
