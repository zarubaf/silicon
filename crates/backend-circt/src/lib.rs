// SPDX-License-Identifier: Apache-2.0
//! Lowers the typed core IR to MLIR text in the CIRCT dialects `hw`, `comb`,
//! and `seq` (spec section 7.3), emits the memory models, and exports Verilog
//! through CIRCT.

mod lower;
mod mlir;
mod models;
pub mod names;
mod verilog;

use std::collections::BTreeSet;

use core_ir::typed::{Design, address_width};

use crate::mlir::{Dir, Pin, Ty};
pub use crate::models::memory_model;
pub use crate::verilog::{ToolError, verilog};

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
    /// The name of the memory module (spec section 3.4).
    #[must_use]
    pub fn module_name(&self) -> String {
        names::memory_module(self)
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

/// The MLIR text of each module of `design`, and the memory configurations.
fn modules(design: &Design) -> (String, BTreeSet<MemConfig>) {
    let mut text = String::new();
    let mut configs = BTreeSet::new();
    for module in design.modules() {
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
