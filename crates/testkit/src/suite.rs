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

/// The folder of a suite under `base`: `tests/<tree>/<suite>` if it exists,
/// else the old path. Only the tree `core` has an old path, `tests/<suite>`.
fn resolve(base: &Path, tree: &str, suite: &str) -> String {
    let new = base.join("tests").join(tree).join(suite);
    let path = if new.is_dir() || tree != "core" {
        new
    } else {
        base.join("tests").join(suite)
    };
    path.to_string_lossy().into_owned()
}

/// The absolute path of the folder of the suite `suite` in the tree `tree`.
#[must_use]
pub fn root(tree: &str, suite: &str) -> String {
    resolve(Path::new(WORKSPACE), tree, suite)
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
    fn root_prefers_the_new_path() {
        let base = std::env::temp_dir().join(format!("testkit-root-{}", std::process::id()));
        std::fs::create_dir_all(base.join("tests/core/check")).unwrap();
        std::fs::create_dir_all(base.join("tests/check")).unwrap();
        let got = resolve(&base, "core", "check");
        std::fs::remove_dir_all(&base).unwrap();
        assert!(got.ends_with("tests/core/check"), "{got}");
    }

    #[test]
    fn root_falls_back_to_the_old_path() {
        let base = std::env::temp_dir().join(format!("testkit-old-{}", std::process::id()));
        assert!(resolve(&base, "core", "run").ends_with("tests/run"));
        assert!(resolve(&base, "source", "parse").ends_with("tests/source/parse"));
    }
}
