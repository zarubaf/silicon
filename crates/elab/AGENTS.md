# Elab

## Purpose

The `elab` crate is the elaborator of the Rust front end. It is layer 6 of the pipeline, after `typeck`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.4, 4.5, and 5.

## Owns

This crate owns the static values with their canonical serialization and their recursive size, and SHA-256 for the digest names. It also owns the static evaluator with the fuel, the nesting depth, the cost model, and the table of constants. The Lean modules `Source.Value`, `Source.Sha256`, and `Source.Eval` are the normative definitions. The instantiations and the lowering come in later parts of #72.

The elaborator core keeps to the Rust subset of design section 4.5: plain owned data, `match`, `Vec`, `Box`, and no `Rc`, no `unsafe`, and no trait object. The module `int` holds the static integer behind a small interface, and only this module computes with `num-bigint`. A finite value uses the bit vector of `core-ir`, as the core semantics does.

## Invariants

- The serialization of a value equals the bytes of `Value.serialize` in Lean. The recursive size equals `Value.size`. Check: `cargo nextest run -p elab`.
- The digest equals the test vectors of FIPS 180-4. Check: `cargo nextest run -p elab`.
- The evaluator charges each unit of `Source.Eval` in the same order and at the same node. The charge comes before the work, and each operation keeps its work and its memory in its charge. Thus the value, the used fuel, and the code and the position of the first error equal those of Lean. Check: `cargo nextest run -p elab` and the comparison with `silicon-check eval`.
- An error message prints at most 256 bits of an integer and 64 characters of a string. Check: `cargo nextest run -p elab`.
- The evaluator recurses, so it runs through `parse::on_stack`. Each thread runs a group of nesting levels with a stack for the height of the AST, so any nesting depth is safe. A result that refers to a local or a constant copies nothing until a copy pays for it. Check: `cargo nextest run -p elab`.
- The crate uses no `HashMap` and no `HashSet`. Check: `just clippy`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate reads a `Resolved` that passed `typeck`. It uses `resolve` for the targets of names, `parse` for the AST and the front-end thread, and `core-ir` for the operations on finite values. The tests use `typeck`. The `driver` calls it.

## How to test

Run `cargo nextest run -p elab`, then `just check` from the repository root.
