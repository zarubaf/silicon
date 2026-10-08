# Backend CIRCT

## Purpose

The `backend-circt` crate lowers a checked core IR design to MLIR text in the CIRCT dialects `hw`, `comb`, and `seq`. It also makes one memory model for each memory configuration, and it exports Verilog through CIRCT. Section 7.3 of the core IR design gives the rules. A Lean reference lowering emits MLIR for the same designs, and LEC compares the two. Thus the names, the port order, and the memory interfaces must follow the spec exactly.

## Owns

This crate owns the MLIR text of a design and the memory models. It also owns the names and the port lists of the memory modules. It writes text only. It does not link the MLIR C API. It runs `firtool` as a process for the Verilog.

## Invariants

- Each lowered design parses with `circt-opt`. Check: `cargo nextest run -p backend-circt`.
- A module keeps the port order of its source. The clock port has the type `!seq.clock`. Check: `cargo nextest run -p backend-circt`.
- A register has the MLIR name `silicon_reg_<name>`. Check: `cargo nextest run -p backend-circt`.
- A memory is an instance of `silicon_mem_<D>x<W>_r<R>w<P>`, with the ports of spec section 7.3. The read ports follow the order of the `read` forms in the canonical text. Check: `cargo nextest run -p backend-circt`.
- The guards for an access out of range stay in the parent module. Check: `cargo nextest run -p backend-circt`.
- A memory model is one `seq.compreg` with the name `silicon_reg_mem` and one word for each address. A read is combinational, and a higher write port wins. The model has no guard. Check: `cargo nextest run -p backend-circt`.
- The Verilog has no random initialization. A missing CIRCT tool is an error that names the tool. Check: `cargo nextest run -p backend-circt`.
- A shift amount of the width or more gives 0, or the sign fill for `shrs`. CIRCT 1.160 gives `comb` shifts this meaning, so the lowering adds no guard. Check: `cargo nextest run -p backend-circt`.
- The code has no `unwrap`, no `expect`, and no panic on user input. The input is a checked design, and its invariants are preconditions. Check: `just clippy`.

## Dependencies

This crate depends on `core-ir`. In the pipeline, it comes after `core-ir` and before `driver`. The Verilog needs `firtool` on the `PATH`. The tests run `circt-opt` and `circt-lec` from the development shell, and `circt-lec` needs the Z3 library in `SILICON_Z3_LIB`.

## How to test

Run `cargo nextest run -p backend-circt` in the development shell, then `just check` from the repository root.
