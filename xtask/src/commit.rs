//! Commit conventions and the "refactor first, then change behavior" rule.

use std::path::{Path, PathBuf};
use std::process::Command;

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

/// Checks a commit message. Returns one problem string per violation.
pub fn check_message(msg: &str, scopes: &[String]) -> Vec<String> {
    let mut problems = Vec::new();
    let subject = msg.lines().next().unwrap_or("");
    match parse_subject(subject) {
        None => problems.push(format!(
            "subject is not a Conventional Commit `type(scope): subject`: {subject:?}"
        )),
        Some(scope) if !scope.is_empty() && !scopes.iter().any(|s| s == scope) => {
            problems.push(format!("unknown scope `{scope}`"));
        }
        Some(_) => {}
    }
    let length = subject.chars().count();
    if length > MAX_SUBJECT {
        problems.push(format!(
            "subject has {length} characters; the limit is {MAX_SUBJECT}"
        ));
    }
    for line in msg.lines() {
        let lower = line.to_lowercase();
        if let Some(value) = lower.strip_prefix("co-authored-by:")
            && FORBIDDEN_TRAILER_VALUES.iter().any(|f| value.contains(f))
        {
            problems.push(format!("agent attribution trailer: {line:?}"));
        }
        if lower.contains("generated with") {
            problems.push(format!("generated-with line: {line:?}"));
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
    parts
        .windows(3)
        .any(|w| w[0] == "tests" && w[1] == "corpus")
        && parts.iter().any(|p| p == "expected")
}

fn is_test_code(path: &Path) -> bool {
    path.iter().any(|p| p == "tests")
}

/// Checks the files a commit changes against its type.
pub fn check_paths(commit_type: &str, paths: &[PathBuf]) -> Vec<String> {
    let mut problems = Vec::new();
    let has_expectation = paths.iter().any(|p| is_expectation(p));
    if commit_type == "refactor" && has_expectation {
        problems.push("a refactor commit must not change test expectations".to_owned());
    }
    let has_lean = paths.iter().any(|p| p.starts_with("lean"));
    let has_crates = paths.iter().any(|p| p.starts_with("crates"));
    if has_lean && has_crates {
        problems.push("a commit must not change `lean/` and `crates/` together".to_owned());
    }
    let has_other = paths.iter().any(|p| !is_expectation(p) && !is_test_code(p));
    if has_expectation && has_other {
        problems.push("a commit must not change test expectations and non-test code".to_owned());
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
    let msg: String = msg
        .lines()
        .filter(|l| !l.starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n");
    Ok(check_message(&msg, &allowed_scopes()?))
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
    let out = Command::new("git")
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

    #[test]
    fn rejects_non_conventional_subject() {
        assert!(!check_message("Add x", &scopes()).is_empty());
    }

    #[test]
    fn rejects_unknown_scope() {
        assert!(!check_message("feat(unknown): x", &scopes()).is_empty());
    }

    #[test]
    fn rejects_long_subject() {
        let ok = format!("feat: {}", "a".repeat(72 - 6));
        let long = format!("feat: {}", "a".repeat(72 - 5));
        assert!(check_message(&ok, &scopes()).is_empty());
        assert_eq!(long.chars().count(), 73);
        assert!(!check_message(&long, &scopes()).is_empty());
    }

    #[test]
    fn rejects_agent_attribution() {
        let claude = "feat: x\n\nCo-Authored-By: Claude <noreply@anthropic.com>";
        assert!(!check_message(claude, &scopes()).is_empty());
        let generated = "feat: x\n\nGenerated with a tool";
        assert!(!check_message(generated, &scopes()).is_empty());
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
        assert!(!check_paths("refactor", &p).is_empty());
    }

    #[test]
    fn lean_and_crates_do_not_mix() {
        let p = paths(&["lean/A.lean", "crates/a/src/lib.rs"]);
        assert!(!check_paths("feat", &p).is_empty());
    }

    #[test]
    fn test_commit_may_change_expectations_alone() {
        let p = paths(&["crates/a/snapshots/x.snap"]);
        assert!(check_paths("test", &p).is_empty());
    }

    #[test]
    fn expectations_and_code_do_not_mix() {
        let p = paths(&["crates/a/snapshots/x.snap", "crates/a/src/lib.rs"]);
        assert!(!check_paths("feat", &p).is_empty());
    }

    fn run(dir: &Path, args: &[&str]) {
        git(dir, args).unwrap();
    }

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
