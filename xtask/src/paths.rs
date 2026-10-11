//! Where the test data lives. Each reader asks here, so one move of a
//! directory touches one file. The new location wins when both exist.

use std::path::PathBuf;

use crate::repo::Repo;

/// The new path if it exists in the checkout, else the old one. Paths are
/// relative to the repository root.
fn prefer(repo: &Repo, new: &str, old: &str) -> PathBuf {
    if repo.root.join(new).exists() {
        PathBuf::from(new)
    } else {
        PathBuf::from(old)
    }
}

/// The directory of the designs that LEC and the differential tests share.
pub fn corpus_dir(repo: &Repo) -> PathBuf {
    prefer(repo, "tests/core/corpus", "tests/corpus")
}

/// The inventory of the LEC checks.
pub fn lec_inventory(repo: &Repo) -> PathBuf {
    prefer(repo, "tests/inventory/lec.txt", "tests/lec-checks.txt")
}

/// The inventory of the differential checks.
pub fn diff_inventory(repo: &Repo) -> PathBuf {
    prefer(repo, "tests/inventory/diff.txt", "tests/diff-checks.txt")
}

/// The repository that holds this source tree. Tests read the checked-in
/// data through it at run time.
#[cfg(test)]
pub fn this_repo() -> Repo {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    Repo::from_parts(root, Vec::new())
}

/// The text of the corpus design `name` of this source tree.
#[cfg(test)]
pub fn corpus_file(name: &str) -> String {
    let repo = this_repo();
    repo.read(&corpus_dir(&repo).join(name)).unwrap()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    fn temp_repo(dirs: &[&str]) -> (tempfile::TempDir, Repo) {
        let dir = tempfile::tempdir().unwrap();
        for d in dirs {
            fs::create_dir_all(dir.path().join(d)).unwrap();
        }
        let repo = Repo::from_parts(dir.path().to_path_buf(), Vec::new());
        (dir, repo)
    }

    fn touch(repo: &Repo, rel: &str) {
        fs::create_dir_all(repo.root.join(rel).parent().unwrap()).unwrap();
        fs::write(repo.root.join(rel), "").unwrap();
    }

    #[test]
    fn the_new_corpus_wins() {
        let (_d, repo) = temp_repo(&["tests/core/corpus", "tests/corpus"]);
        assert_eq!(corpus_dir(&repo), PathBuf::from("tests/core/corpus"));
    }

    #[test]
    fn the_old_corpus_is_the_fallback() {
        let (_d, repo) = temp_repo(&["tests/corpus"]);
        assert_eq!(corpus_dir(&repo), PathBuf::from("tests/corpus"));
    }

    #[test]
    fn the_new_inventories_win() {
        let (_d, repo) = temp_repo(&[]);
        for f in [
            "tests/inventory/lec.txt",
            "tests/inventory/diff.txt",
            "tests/lec-checks.txt",
            "tests/diff-checks.txt",
        ] {
            touch(&repo, f);
        }
        assert_eq!(
            lec_inventory(&repo),
            PathBuf::from("tests/inventory/lec.txt")
        );
        assert_eq!(
            diff_inventory(&repo),
            PathBuf::from("tests/inventory/diff.txt")
        );
    }

    #[test]
    fn the_old_inventories_are_the_fallback() {
        let (_d, repo) = temp_repo(&[]);
        touch(&repo, "tests/lec-checks.txt");
        touch(&repo, "tests/diff-checks.txt");
        assert_eq!(lec_inventory(&repo), PathBuf::from("tests/lec-checks.txt"));
        assert_eq!(
            diff_inventory(&repo),
            PathBuf::from("tests/diff-checks.txt")
        );
    }
}
