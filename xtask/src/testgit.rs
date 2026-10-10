//! Git helpers for tests. They build on `gitcmd::git`, which drops the
//! `GIT_*` variables in test builds.

use std::path::Path;
use std::process::Command;

fn command(dir: &Path, args: &[&str]) -> Command {
    let mut cmd = crate::gitcmd::git();
    cmd.args(args).current_dir(dir);
    cmd
}

/// Run git in `dir` and panic when it fails.
pub fn run(dir: &Path, args: &[&str]) {
    let status = command(dir, args).status().unwrap();
    assert!(status.success(), "git {args:?} failed");
}

/// Make `dir` a repository on `main` with a committer and no signing.
pub fn init(dir: &Path) {
    run(dir, &["init", "--quiet", "-b", "main"]);
    run(dir, &["config", "user.email", "t@example.com"]);
    run(dir, &["config", "user.name", "t"]);
    run(dir, &["config", "commit.gpgsign", "false"]);
    run(dir, &["config", "tag.gpgsign", "false"]);
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
        let target = std::env::var_os(TARGET).expect("run by the regression test only");
        let dir = Path::new(&target);
        run(dir, &["init", "--quiet"]);
        run(dir, &["config", "user.email", "t@example.com"]);
        run(dir, &["config", "user.name", "t"]);
        run(dir, &["config", "commit.gpgsign", "false"]);
        std::fs::write(dir.join("f"), "x").unwrap();
        run(dir, &["add", "."]);
        run(dir, &["commit", "--quiet", "-m", "x"]);

        let repo = crate::repo::Repo::discover_in(dir).unwrap();
        assert_eq!(repo.files.len(), 1);
        let problems = crate::commit::check_range(dir, "HEAD", &["xtask".to_string()]).unwrap();
        assert_eq!(problems.len(), 1, "{problems:?}");
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
