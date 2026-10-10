//! The names that the lowering and the oracles make for MLIR (spec section
//! 3.4). Each name has one builder here, so a change of the form touches one
//! file.

/// The prefix of the name of a memory module.
const MEMORY_MODULE_PREFIX: &str = "silicon_mem_";

/// The name of the register of a memory model (spec section 7.3).
pub const MEMORY_REGISTER: &str = "silicon_reg_mem";

/// The name of the register of the core register `name`.
#[must_use]
pub fn register(name: &str) -> String {
    format!("silicon_reg_{name}")
}

/// The name of the memory module of `config`.
pub(crate) fn memory_module(config: &crate::MemConfig) -> String {
    format!(
        "{MEMORY_MODULE_PREFIX}{}x{}_r{}w{}",
        config.depth, config.width, config.reads, config.writes
    )
}

/// True if `name` is a memory module and not a user module or extern.
#[must_use]
pub fn is_memory_module(name: &str) -> bool {
    name.starts_with(MEMORY_MODULE_PREFIX)
}
