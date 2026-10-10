//! The names that the lowering and the oracles make for MLIR (spec section
//! 3.4). A backend name is a kind and its arguments, joined by `$$`. No core
//! name contains `$$`, so no backend name equals a core name. Each name has
//! one builder here, so a change of the form touches one file.

/// Joins a kind and its arguments.
fn backend(kind: &str, args: &[&str]) -> String {
    std::iter::once(kind)
        .chain(args.iter().copied())
        .collect::<Vec<_>>()
        .join("$$")
}

/// The name of the register of the core register `name`.
#[must_use]
pub fn register(name: &str) -> String {
    backend("reg", &[name])
}

/// The name of the register of a memory model (spec section 7.3).
#[must_use]
pub fn memory_register() -> String {
    backend("reg", &["mem"])
}

/// The name of the stand-in register of the port `port` of the black box
/// `black_box` (spec section 8.1).
#[must_use]
pub fn stand_in_register(black_box: &str, port: &str) -> String {
    backend("reg", &[black_box, port])
}

/// The name of the memory module of `config`.
pub(crate) fn memory_module(config: &crate::MemConfig) -> String {
    let configuration = format!(
        "{}x{}_r{}w{}",
        config.depth, config.width, config.reads, config.writes
    );
    backend("mem", &[&configuration])
}

/// True if `name` is a memory module and not a user module or extern.
#[must_use]
pub fn is_memory_module(name: &str) -> bool {
    name.starts_with("mem$$")
}

/// The name of the LEC wrapper of the top module `top` (spec section 8.1).
#[must_use]
pub fn lec_wrapper(top: &str) -> String {
    backend("lec", &[top])
}

/// The name of the `arcilator` testbench of the top module `top` (spec
/// section 8.2).
#[must_use]
pub fn diff_entry(top: &str) -> String {
    backend("diff", &[top])
}
