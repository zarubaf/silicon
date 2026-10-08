//! The memory model of each memory configuration: the simulation model for
//! users and the module that the LEC of spec section 8.1 puts in place of the
//! extern.
//!
//! The model holds the words in one `seq.compreg` of type `!hw.array<DxiW>`
//! with the name `silicon_reg_mem`. A read port gives the word of the current
//! state with `hw.array_get`, so the read is combinational. The write ports
//! apply to the old state in index order with `hw.array_inject`, so a higher
//! port overwrites a lower port at the same address.
//!
//! The guarded parent gives the model only addresses in range or the enable
//! 0. For each other input, the model still follows spec section 5.2: a read
//! out of range gives 0, and a write out of range does nothing. `circt-lec`
//! gives `hw.array_get` and `hw.array_inject` out of range a free result, and
//! a free array would replace each word. A depth that is a power of two has
//! no address out of range, so its model has no such guard.

use core_ir::typed::address_width;

use crate::{MemConfig, full_range, mlir};

/// The MLIR text of the memory model of `config`: an `hw.module` with the
/// name and the ports of the extern of spec section 7.3.
#[must_use]
pub fn memory_model(config: &MemConfig) -> String {
    let (depth, width) = (config.depth, config.width);
    let addr = address_width(depth);
    let array = format!("!hw.array<{depth}xi{width}>");
    let guarded = !full_range(depth);
    let mut ops = Vec::new();
    // Emits the guard `%<port>_ok` of the address of `port`, if one is needed.
    let guard = |ops: &mut Vec<String>, port: &str| {
        guarded.then(|| {
            ops.push(format!(
                "%{port}_ok = comb.icmp ult %{port}_addr, %depth : i{addr}"
            ));
            format!("%{port}_ok")
        })
    };
    if guarded {
        ops.push(format!("%depth = hw.constant {depth} : i{addr}"));
        ops.push(format!("%zero = hw.constant 0 : i{width}"));
    }
    let mut outputs = Vec::new();
    for n in 0..config.reads {
        let port = format!("r{n}");
        let get = format!("hw.array_get %silicon_reg_mem[%{port}_addr] : {array}, i{addr}");
        if let Some(ok) = guard(&mut ops, &port) {
            ops.push(format!("%{port}_word = {get}"));
            ops.push(format!(
                "%{port}_data = comb.mux {ok}, %{port}_word, %zero : i{width}"
            ));
        } else {
            ops.push(format!("%{port}_data = {get}"));
        }
        outputs.push(format!("%{port}_data"));
    }
    let mut state = "%silicon_reg_mem".to_owned();
    for n in 0..config.writes {
        let port = format!("w{n}");
        ops.push(format!(
            "%{port}_set = hw.array_inject {state}[%{port}_addr], %{port}_data : {array}, i{addr}"
        ));
        let en = if let Some(ok) = guard(&mut ops, &port) {
            ops.push(format!("%{port}_on = comb.and %{port}_en, {ok} : i1"));
            format!("%{port}_on")
        } else {
            format!("%{port}_en")
        };
        ops.push(format!(
            "%{port}_next = comb.mux {en}, %{port}_set, {state} : {array}"
        ));
        state = format!("%{port}_next");
    }
    ops.push(format!(
        "%silicon_reg_mem = seq.compreg {state}, %clk : {array}"
    ));
    if outputs.is_empty() {
        ops.push("hw.output".to_owned());
    } else {
        let types = vec![format!("i{width}"); outputs.len()];
        ops.push(format!(
            "hw.output {} : {}",
            outputs.join(", "),
            types.join(", ")
        ));
    }
    let mut text = format!(
        "hw.module @{}{} {{\n",
        config.module_name(),
        mlir::signature(&config.pins())
    );
    for op in ops {
        text.push_str("  ");
        text.push_str(&op);
        text.push('\n');
    }
    text.push_str("}\n");
    text
}
