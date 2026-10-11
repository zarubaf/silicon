//! Where the suites live.

use std::path::Path;

/// The directory of the workspace, as a path that starts at this crate.
const WORKSPACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

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
