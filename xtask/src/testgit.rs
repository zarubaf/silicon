//! Git helpers for tests. A hook or a temporary index leaves `GIT_*`
//! variables in the environment, and git would then act on that
//! repository instead of the test repository. Every test git call goes
//! through here so it never sees them.

use std::path::Path;
use std::process::Command;

/// A `git` command for `dir` with every inherited `GIT_*` variable removed.
fn command(dir: &Path, args: &[&str]) -> Command {
    let mut cmd = Command::new("git");
    cmd.args(args).current_dir(dir);
    for (name, _) in std::env::vars_os() {
        if name.to_string_lossy().starts_with("GIT_") {
            cmd.env_remove(name);
        }
    }
    cmd
}

/// Run git in `dir` and panic when it fails.
pub fn run(dir: &Path, args: &[&str]) {
    let status = command(dir, args).status().unwrap();
    assert!(status.success(), "git {args:?} failed");
}

/// Run git in `dir` and return its trimmed stdout.
pub fn output(dir: &Path, args: &[&str]) -> String {
    let out = command(dir, args).output().unwrap();
    assert!(out.status.success(), "git {args:?} failed");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    const TARGET: &str = "XTASK_TESTGIT_TARGET";

    /// Runs only as the child of `helpers_ignore_the_git_environment`,
    /// where `GIT_DIR` and `GIT_INDEX_FILE` point at the decoy.
    #[test]
    #[ignore = "runs only as the child of the regression test"]
    fn child_uses_helpers() {
        let Some(target) = std::env::var_os(TARGET) else {
            return;
        };
        let dir = Path::new(&target);
        run(dir, &["init", "--quiet"]);
        run(dir, &["config", "user.email", "t@example.com"]);
        run(dir, &["config", "user.name", "t"]);
        run(dir, &["config", "commit.gpgsign", "false"]);
        std::fs::write(dir.join("f"), "x").unwrap();
        run(dir, &["add", "."]);
        run(dir, &["commit", "--quiet", "-m", "x"]);
    }

    #[test]
    fn helpers_ignore_the_git_environment() {
        let decoy = tempfile::tempdir().unwrap();
        let target = tempfile::tempdir().unwrap();
        run(decoy.path(), &["init", "--quiet"]);
        let git_dir = decoy.path().join(".git");
        let snapshot = || {
            (
                std::fs::read(git_dir.join("config")).unwrap(),
                std::fs::read(git_dir.join("HEAD")).unwrap(),
            )
        };
        let before = snapshot();

        let status = Command::new(std::env::current_exe().unwrap())
            .args([
                "--ignored",
                "--exact",
                "testgit::tests::child_uses_helpers",
                "--test-threads=1",
            ])
            .env("GIT_DIR", &git_dir)
            .env("GIT_INDEX_FILE", git_dir.join("index"))
            .env(TARGET, target.path())
            .status()
            .unwrap();

        assert!(status.success());
        assert_eq!(before, snapshot(), "decoy repository was modified");
        assert!(!git_dir.join("index").exists());
        assert_eq!(output(target.path(), &["log", "-1", "--format=%s"]), "x");
    }
}
