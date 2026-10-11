# Elab

## Purpose

The `elab` crate is the elaborator of the Rust front end. It is layer 6 of the pipeline, after `typeck`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.4, 4.5, and 5.

## Owns

This crate owns the static values with their canonical serialization and their recursive size, and SHA-256 for the digest names. It also owns the evaluator with the fuel, the nesting depth, the cost model, the table of constants, and the hardware values. It owns the table of instantiations with the checks for each instantiation, the core names, and the emitted module names. It owns the lowering to core IR, the port layout, and the port schema of the source vectors. The Lean modules `Source.Value`, `Source.Sha256`, `Source.Eval`, `Source.Elab`, `Source.Names`, `Source.Layout`, `Source.Flatten`, and `Source.Vectors` are the normative definitions.

A hardware value is a node in one arena, so a new node shares its operand trees. A structural path is a node in a second arena, and a user field holds the symbol of its name. Thus a new node or a new name costs constant work and no copy.

The elaborator core keeps to the Rust subset of design section 4.5: plain owned data, `match`, `Vec`, `Box`, and no `Rc`, no `unsafe`, and no trait object. The module `int` holds the static integer behind a small interface, and only this module computes with `num-bigint`. A finite value uses the bit vector of `core-ir`, as the core semantics does.

## Invariants

- The serialization of a value equals the bytes of `Value.serialize` in Lean. The recursive size equals `Value.size`. Check: `cargo nextest run -p elab`.
- The digest equals the test vectors of FIPS 180-4. Check: `cargo nextest run -p elab`.
- The evaluator charges each unit of `Source.Eval` in the same order and at the same node. The charge comes before the work, and each operation keeps its work and its memory in its charge. Thus the value, the used fuel, and the code and the position of the first error equal those of Lean. Check: `cargo nextest run -p elab` and the comparison with `silicon-check eval`.
- The elaboration charges each unit of `Source.Elab` in the same order and at the same node. The units of each instantiation, the emitted names, and the code and the position of the first error equal those of Lean `Elab.elaborate`. Check: `cargo nextest run -p elab` and the comparison with `silicon-check cost`.
- `decode(encode(p)) == Some(p)` for each valid name `p`, and each encoded name is a legal core name. Check: `cargo nextest run -p elab`.
- An error message prints at most 256 bits of an integer and 64 characters of a string. Check: `cargo nextest run -p elab`.
- The evaluator recurses, so it runs through `parse::NestedStack`, and it only finds the heights of the AST. A call, a constant, and an instantiation each start a nesting level. Each thread runs a group of nesting levels, so any nesting depth is safe. A design and an error hold no recursive value, so they drop safely on any stack. A result that refers to a local or a constant copies nothing until a copy pays for it. Check: `cargo nextest run -p elab`.
- The crate uses no `HashMap` and no `HashSet`. Check: `just clippy`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate reads a `Resolved` that passed `typeck`. It uses `resolve` for the targets of names, and `parse` for the AST and the front-end thread. It uses `core-ir` for the operations on finite values and the keywords of core names. The tests use `typeck` and `proptest`. The `driver` calls it.

## How to test

Run `cargo nextest run -p elab`, then `just check` from the repository root.
