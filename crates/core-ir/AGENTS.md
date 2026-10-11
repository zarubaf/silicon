# Core IR

## Purpose

The `core-ir` crate is the Rust implementation of the core IR. It is the first stage of the compiler pipeline.

## Owns

This crate owns the bit-vector values and their comb operations. It also owns the diagnostics, the AST, the `.sil` parser and printer, the checker, the typed design, and the inference of the port dependencies. It owns the interpreter and the format of the input and output vectors too. The cargo feature `gen` adds the random generator of well-formed designs. `gen::Config` selects the forms. `Config::source()` is the configuration for designs that have a source form. `gen::lines` makes the input lines of a top module, and `gen::resets` makes the reset values of a run. A reset is likely in the first cycle and rare after it, so the state of a design lives for several cycles. The source generator of `syntax` reuses `gen::resets`.

## Invariants

- A `Bits` value has a width of at least 1, and its value fits the width. Check: `cargo nextest run -p core-ir`.
- The operations match section 4.1 of the Lean spec. Check: `cargo nextest run -p core-ir`.
- Each design from `gen` passes the checker. Check: `cargo nextest run -p core-ir --all-features`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. A documented internal precondition, such as a typed index into its table, can panic. Check: `just clippy`.

## Dependencies

This crate has no dependency on another crate of the workspace. It uses `num-bigint` for wide values. The feature `gen` and the tests use `proptest`.

## How to test

Run `cargo nextest run -p core-ir --all-features`, then `just check` from the repository root.
