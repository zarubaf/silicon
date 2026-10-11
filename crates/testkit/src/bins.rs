//! The binaries that the suites run.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The variable that tells `silicon` where the Lean checker is.
pub const CHECK_VARIABLE: &str = "SILICON_CHECK";

/// The variable that names the binary under test.
const BIN_VARIABLE: &str = "SILICON_BIN";

/// The checker that Lake builds: `SILICON_CHECK` if it is set, else the
/// executable in the Lean package. `just check` builds it.
#[must_use]
pub fn silicon_check() -> PathBuf {
    std::env::var_os(CHECK_VARIABLE).map_or_else(
        || {
            PathBuf::from(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../lean/.lake/build/bin/silicon-check"
            ))
        },
        PathBuf::from,
    )
}

/// A command that runs `silicon` with the checker of [`silicon_check`].
#[must_use]
pub fn silicon(silicon: &Path) -> Command {
    let mut command = Command::new(silicon);
    command.env(CHECK_VARIABLE, silicon_check());
    command
}

/// The binary that the shared suites test: `SILICON_BIN` if it is set, else
/// `default`. `cargo xtask lean-check` sets `SILICON_BIN` to the absolute
/// path of `silicon-check`. A relative path fails, because the tests run in
/// another folder. A `SILICON_BIN` left in the shell also changes the binary
/// of `just test`.
#[must_use]
pub fn under_test(default: &Path) -> PathBuf {
    std::env::var_os(BIN_VARIABLE).map_or_else(|| default.to_path_buf(), PathBuf::from)
}
