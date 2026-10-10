use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

/// A file in the git index. `path` is relative to the repository root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrackedFile {
    pub path: PathBuf,
    pub is_symlink: bool,
    pub is_executable: bool,
}

/// The tracked files of a repository. Every check reads from this.
#[derive(Debug)]
pub struct Repo {
    pub root: PathBuf,
    pub files: Vec<TrackedFile>,
}

impl Repo {
    /// Discovers the repository that contains the current directory.
    pub fn discover() -> Result<Self> {
        Self::discover_in(Path::new("."))
    }

    pub fn discover_in(dir: &Path) -> Result<Self> {
        let root = git(dir, &["rev-parse", "--show-toplevel"])?;
        let root = PathBuf::from(String::from_utf8(root)?.trim_end());
        let index = git(&root, &["ls-files", "-s", "-z"])?;
        let mut files = Vec::new();
        for entry in index.split(|b| *b == 0).filter(|e| !e.is_empty()) {
            let entry = std::str::from_utf8(entry)?;
            let (meta, path) = entry
                .split_once('\t')
                .with_context(|| format!("malformed ls-files entry: {entry:?}"))?;
            files.push(TrackedFile {
                path: PathBuf::from(path),
                is_symlink: meta.starts_with("120000 "),
                is_executable: meta.starts_with("100755 "),
            });
        }
        Ok(Self::from_parts(root, files))
    }

    pub fn from_parts(root: PathBuf, files: Vec<TrackedFile>) -> Self {
        Self { root, files }
    }

    pub fn read(&self, rel: &Path) -> Result<String> {
        let path = self.root.join(rel);
        std::fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))
    }
}

/// Runs git in `dir` and returns its stdout. A nonzero exit is an error that carries stderr.
pub fn git(dir: &Path, args: &[&str]) -> Result<Vec<u8>> {
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
    Ok(out.stdout)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testgit::{init, run as git};

    #[test]
    fn discovers_paths_with_spaces() {
        let tmp = tempfile::tempdir().unwrap();
        init(tmp.path());
        std::fs::write(tmp.path().join("a b.md"), "x").unwrap();
        git(tmp.path(), &["add", "."]);
        git(tmp.path(), &["commit", "--quiet", "-m", "x"]);
        let repo = Repo::discover_in(tmp.path()).unwrap();
        assert!(
            repo.files
                .iter()
                .any(|f| f.path == std::path::Path::new("a b.md"))
        );
    }

    #[test]
    fn marks_symlinks_from_index_mode() {
        let tmp = tempfile::tempdir().unwrap();
        init(tmp.path());
        std::fs::write(tmp.path().join("t.md"), "x").unwrap();
        std::os::unix::fs::symlink("t.md", tmp.path().join("l.md")).unwrap();
        git(tmp.path(), &["add", "."]);
        git(tmp.path(), &["commit", "--quiet", "-m", "x"]);
        let repo = Repo::discover_in(tmp.path()).unwrap();
        let link = repo
            .files
            .iter()
            .find(|f| f.path == std::path::Path::new("l.md"))
            .unwrap();
        let plain = repo
            .files
            .iter()
            .find(|f| f.path == std::path::Path::new("t.md"))
            .unwrap();
        assert!(link.is_symlink);
        assert!(!plain.is_symlink);
    }

    #[test]
    fn marks_executables_from_index_mode() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = tempfile::tempdir().unwrap();
        init(tmp.path());
        std::fs::write(tmp.path().join("run"), "x").unwrap();
        std::fs::set_permissions(
            tmp.path().join("run"),
            std::fs::Permissions::from_mode(0o755),
        )
        .unwrap();
        std::fs::write(tmp.path().join("t.md"), "x").unwrap();
        git(tmp.path(), &["add", "."]);
        git(tmp.path(), &["commit", "--quiet", "-m", "x"]);
        let repo = Repo::discover_in(tmp.path()).unwrap();
        let mode = |p: &str| {
            repo.files
                .iter()
                .find(|f| f.path == std::path::Path::new(p))
                .unwrap()
                .is_executable
        };
        assert!(mode("run"));
        assert!(!mode("t.md"));
    }
}
