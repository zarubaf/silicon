// SPDX-License-Identifier: Apache-2.0
//! Where the test data lives. Each reader asks here, so one move of a
//! directory touches one file.

use std::path::PathBuf;

#[cfg(test)]
use crate::repo::Repo;

/// The directory of the designs that LEC and the differential tests share.
pub fn corpus_dir() -> PathBuf {
    PathBuf::from("tests/core/corpus")
}

/// The directory of the source designs that LEC and the differential tests
/// share. Each check reads the elaboration of its `// TOP` line.
pub fn source_corpus_dir() -> PathBuf {
    PathBuf::from("tests/source/corpus")
}

/// The inventory of the LEC checks.
pub fn lec_inventory() -> PathBuf {
    PathBuf::from("tests/inventory/lec.txt")
}

/// The inventory of the differential checks.
pub fn diff_inventory() -> PathBuf {
    PathBuf::from("tests/inventory/diff.txt")
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
    repo.read(&corpus_dir().join(name)).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_paths_exist_in_this_tree() {
        let repo = this_repo();
        for p in [
            corpus_dir(),
            source_corpus_dir(),
            lec_inventory(),
            diff_inventory(),
        ] {
            assert!(repo.root.join(&p).exists(), "{}", p.display());
        }
    }
}
