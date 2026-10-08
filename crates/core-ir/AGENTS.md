# Core IR

## Purpose

The `core-ir` crate is the Rust implementation of the core IR. It is the first stage of the compiler pipeline.

## Owns

This crate owns the bit-vector values and their comb operations. It also owns the diagnostics, the AST, the `.sil` parser and printer, the checker, the typed design, and the inference of the port dependencies. The interpreter follows in this crate.

## Invariants

- A `Bits` value has a width of at least 1, and its value fits the width. Check: `cargo nextest run -p core-ir`.
- The operations match section 4.1 of the Lean spec. Check: `cargo nextest run -p core-ir`.
- Non-test code has no `unwrap`, no `expect`, and no panic. Check: `just clippy`.

## Dependencies

This crate has no dependency on another crate of the workspace. It uses `num-bigint` for wide values.

## How to test

Run `cargo nextest run -p core-ir`, then `just check` from the repository root.
