//! The memory model of each memory configuration: the simulation model for
//! users and the module that the LEC of spec section 8.1 puts in place of the
//! extern.
//!
//! The model holds one word for each address, `2^A` words for the address
//! width `A`, in one `seq.compreg` of type `!hw.array<2^A x iW>` with the
//! name `MEMORY_REGISTER`. A read port gives the word of the current state
//! with `hw.array_get`, so the read is combinational. The write ports apply
//! to the old state in index order with `hw.array_inject`, so a higher port
//! overwrites a lower port at the same address.
//!
//! The model has no guard. The guarded parent gives it only addresses below
//! the depth `D` or the enable 0, and for those inputs it follows spec
//! section 5.2. An address at `D` or above reads or writes its own word,
//! which no address in range reaches. Thus a parent without a guard changes
//! an output or the next state, and the LEC finds it. Each address is in the
//! range of the array, so no tool gives an access a free result.

use core_ir::typed::address_width;

use crate::MemConfig;
use crate::mlir::{self, Ty};
use crate::names::MEMORY_REGISTER as REG;

/// The MLIR text of the memory model of `config`: an `hw.module` with the
/// name and the ports of the extern of spec section 7.3.
#[must_use]
pub fn memory_model(config: &MemConfig) -> String {
    let width = config.width;
    let addr = address_width(config.depth);
    let array = format!("!hw.array<{}xi{width}>", 1u64 << addr);
    let mut ops = Vec::new();
    let mut outputs = Vec::new();
    for n in 0..config.reads {
        ops.push(format!(
            "%r{n}_data = hw.array_get %{REG}[%r{n}_addr] : {array}, i{addr}"
        ));
        outputs.push(format!("%r{n}_data"));
    }
    let mut state = format!("%{REG}");
    for n in 0..config.writes {
        ops.push(format!(
            "%w{n}_set = hw.array_inject {state}[%w{n}_addr], %w{n}_data : {array}, i{addr}"
        ));
        ops.push(format!(
            "%w{n}_next = comb.mux %w{n}_en, %w{n}_set, {state} : {array}"
        ));
        state = format!("%w{n}_next");
    }
    ops.push(format!("%{REG} = seq.compreg {state}, %clk : {array}"));
    let body: String = ops.iter().flat_map(|op| ["  ", op, "\n"]).collect();
    let outputs: Vec<(String, Ty)> = outputs
        .into_iter()
        .map(|value| (value, Ty::Int(width)))
        .collect();
    mlir::module(&config.module_name(), &config.pins(), &body, &outputs)
}
