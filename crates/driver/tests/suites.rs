// SPDX-License-Identifier: Apache-2.0
//! The file suites of `tests/` (spec section 9). The crate `testkit` holds the
//! runners. Each module name gives the prefix of the test names, for example
//! `core::check::<file>`, and `cargo xtask lean-check` selects tests by it.

use std::path::Path;

/// The `silicon` binary of this crate.
fn silicon() -> &'static Path {
    Path::new(env!("CARGO_BIN_EXE_silicon"))
}

mod core {
    use std::path::Path;

    use super::silicon;

    pub fn check(file: &Path) -> datatest_stable::Result<()> {
        testkit::core::check(silicon(), file)
    }

    pub fn run(file: &Path) -> datatest_stable::Result<()> {
        testkit::core::run(silicon(), file)
    }

    pub fn lower(file: &Path) -> datatest_stable::Result<()> {
        testkit::core::lower(silicon(), file)
    }

    pub fn corpus(file: &Path) -> datatest_stable::Result<()> {
        testkit::core::corpus(silicon(), file)
    }
}

mod source {
    use std::path::Path;

    use super::silicon;

    pub fn parse(file: &Path) -> datatest_stable::Result<()> {
        testkit::source::parse(silicon(), file)
    }
}

datatest_stable::harness! {
    { test = core::check, root = testkit::root("core", "check"), pattern = r"\.sil$" },
    { test = core::run, root = testkit::root("core", "run"), pattern = r"\.sil$" },
    { test = core::lower, root = testkit::root("core", "lower"), pattern = r"\.sil$" },
    { test = core::corpus, root = testkit::root("core", "corpus"), pattern = r"\.sil$" },
    { test = source::parse, root = testkit::root("source", "parse"), pattern = r"\.si$" },
}
