//! The one place that builds a `git` command.
//!
//! Production commands inherit the environment: inside a hook, `GIT_DIR`
//! names the repository to inspect. Test builds drop every `GIT_*`
//! variable instead, so a test never reaches the repository of the caller.

use std::process::Command;

#[cfg(test)]
fn scrubbed(mut cmd: Command) -> Command {
    for (name, _) in std::env::vars_os() {
        if name.to_string_lossy().starts_with("GIT_") {
            cmd.env_remove(name);
        }
    }
    cmd
}

pub fn git() -> Command {
    let cmd = Command::new("git");
    #[cfg(test)]
    let cmd = scrubbed(cmd);
    cmd
}
