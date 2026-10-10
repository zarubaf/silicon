//! The Lean checker that `silicon lower` and `silicon verilog` run first.

use std::path::PathBuf;
use std::process::Command;

/// The variable that names the checker for the `silicon` binary.
pub const VARIABLE: &str = "SILICON_CHECK";

/// The checker that Lake builds (the same rule as the unit tests of
/// `src/validate.rs` and `BINARY` in `xtask/src/lean_check.rs`): `SILICON_CHECK` if it is set, else the
/// executable in the Lean package. `just check` builds it.
pub fn path() -> PathBuf {
    std::env::var_os(VARIABLE).map_or_else(
        || {
            PathBuf::from(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../lean/.lake/build/bin/silicon-check"
            ))
        },
        PathBuf::from,
    )
}

/// A `silicon` command that validates with the real checker.
pub fn silicon() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_silicon"));
    command.env(VARIABLE, path());
    command
}
