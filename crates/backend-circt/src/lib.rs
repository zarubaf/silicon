//! Lowers the typed core IR to MLIR text in the CIRCT dialects `hw`, `comb`,
//! and `seq` (spec section 7.3).

mod lower;
mod mlir;

use std::collections::BTreeSet;

use core_ir::typed::{Design, address_width};

use crate::mlir::{Dir, Pin, Ty};

/// The configuration `(D, W, R, P)` of a memory module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemConfig {
    /// The number of words `D`.
    pub depth: u32,
    /// The data width `W`.
    pub width: u32,
    /// The number of read ports `R`.
    pub reads: usize,
    /// The number of write ports `P`.
    pub writes: usize,
}

impl MemConfig {
    /// The name `silicon_mem_<D>x<W>_r<R>w<P>`.
    #[must_use]
    pub fn module_name(&self) -> String {
        format!(
            "silicon_mem_{}x{}_r{}w{}",
            self.depth, self.width, self.reads, self.writes
        )
    }

    /// The ports of the memory module, in the order of spec section 7.3.
    fn pins(&self) -> Vec<Pin> {
        let addr = Ty::Int(address_width(self.depth));
        let data = Ty::Int(self.width);
        let pin = |dir, name: String, ty| Pin { dir, name, ty };
        let mut pins = vec![pin(Dir::In, "clk".to_owned(), Ty::Clock)];
        for n in 0..self.reads {
            pins.push(pin(Dir::In, format!("r{n}_addr"), addr));
            pins.push(pin(Dir::Out, format!("r{n}_data"), data));
        }
        for n in 0..self.writes {
            pins.push(pin(Dir::In, format!("w{n}_addr"), addr));
            pins.push(pin(Dir::In, format!("w{n}_data"), data));
            pins.push(pin(Dir::In, format!("w{n}_en"), Ty::Int(1)));
        }
        pins
    }
}

/// True if each address of a memory of `depth` words is in range: the depth
/// is a power of two, so an access needs no guard.
fn full_range(depth: u32) -> bool {
    u64::from(depth) == 1u64 << address_width(depth)
}

/// The MLIR text of each module of `design`, and the memory configurations.
fn modules(design: &Design) -> (String, BTreeSet<MemConfig>) {
    let mut text = String::new();
    let mut configs = BTreeSet::new();
    for module in &design.modules {
        let (module, used) = lower::module(design, module);
        text.push_str(&module);
        configs.extend(used);
    }
    (text, configs)
}

/// The MLIR text of `design`: one `hw.module` for each module, and one
/// `hw.module.extern` for each extern and each memory configuration.
///
/// `design` comes from the checker. The lowering relies on its invariants:
/// each typed index is in its table, and a module that uses a clock has one.
#[must_use]
pub fn lower(design: &Design) -> String {
    let (mut text, configs) = modules(design);
    text.push_str(&lower::externs(design));
    for config in configs {
        text.push_str(&mlir::extern_module(&config.module_name(), &config.pins()));
    }
    text
}

/// The memory configurations of a checked design, sorted, each once.
#[must_use]
pub fn memory_configs(design: &Design) -> Vec<MemConfig> {
    modules(design).1.into_iter().collect()
}
