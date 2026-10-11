//! Where the suites live, and the table of suites.

use std::path::Path;

/// The directory of the workspace, as a path that starts at this crate.
const WORKSPACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

/// The `(tree, suite)` pairs that the `driver` test target runs.
#[must_use]
pub fn suites() -> &'static [(&'static str, &'static str)] {
    &[
        ("core", "check"),
        ("core", "run"),
        ("core", "lower"),
        ("core", "corpus"),
        ("source", "parse"),
    ]
}

/// The absolute path of the folder of the suite `suite` in the tree `tree`.
#[must_use]
pub fn root(tree: &str, suite: &str) -> String {
    Path::new(WORKSPACE)
        .join("tests")
        .join(tree)
        .join(suite)
        .to_string_lossy()
        .into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn extension(tree: &str) -> &'static str {
        if tree == "source" { "si" } else { "sil" }
    }

    #[test]
    fn each_suite_root_has_files() {
        for (tree, suite) in suites() {
            let dir = root(tree, suite);
            let found = walk(Path::new(&dir), extension(tree));
            assert!(found, "no `.{}` file in {dir}", extension(tree));
        }
    }

    fn walk(dir: &Path, extension: &str) -> bool {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return false;
        };
        entries.flatten().any(|entry| {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, extension)
            } else {
                path.extension().is_some_and(|e| e == extension)
            }
        })
    }

    #[test]
    fn root_has_no_old_path() {
        assert!(root("core", "check").ends_with("tests/core/check"));
        assert!(root("source", "parse").ends_with("tests/source/parse"));
        for old in ["check", "run", "lower", "corpus"] {
            let dir = Path::new(WORKSPACE).join("tests").join(old);
            assert!(!dir.exists(), "{}", dir.display());
        }
    }
}
