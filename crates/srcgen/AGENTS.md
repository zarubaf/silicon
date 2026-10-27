# Srcgen

## Purpose

The `srcgen` crate is the source generator of `cargo xtask diff-si`. It is a dev-only crate. No shipped binary depends on it. It comes after `syntax` and before `parse` in the layer order, so it cannot use the code of the stages that it tests. See [ADR 0018](../../doc/adr/0018-source-generator-crate.md) and [the front end design](../../doc/design/2026-10-09-frontend.md), section 11.4.

## Owns

This crate owns the lift of a core design to a source program, and the map from core vectors to source vectors. The lift groups adjacent ports, registers, and `let` values into a tuple, an array, or a record. It makes a source memory from the core block of a registered read. The vector map lists the leaves in the port layout, not in byte order.

It also owns the typed form of a generated program, its printer, and its static evaluator. The builder makes random typed programs and their input lines from tapes, one tape for each family of forms. The `twin` writes out each comptime construct. `mutate` changes one site and predicts the first error code where the pass order makes it certain.

A `let` that holds a type or a `PortInfo` list is a `Stmt::TypeLet`. `eval` and the twin ignore it, so no opaque type token exists. ADR 0032 allows one, and the code does not need it. The forms of each slice and the test floors are in the `//!` docs of `src/lib.rs`.

The evaluator models only the programs that the builder makes. It never works on source text, and it does not resolve names or check types. It can reject a program that the language accepts. It must never give a value that differs from the language. A need outside these limits needs a new ADR.

## Invariants

- Only `[dev-dependencies]` and `xtask` name this crate. Check: `cargo xtask check` (rule `workspace-dev-only`).
- This crate does not depend on `parse`, `resolve`, `typeck`, or `elab`. Check: `cargo xtask check` (rule `workspace-layers`).
- Each design of `Config::source()` lifts to a program that lexes with no error. A core memory lifts only with the exact block of section 7.6, else `Unsupported::Memory`. Check: `cargo nextest run -p srcgen`.
- The builder of `typed()` gives no fault on the tested tapes. Each program, twin, and mutant lexes with no error, and each form occurs at its floor in 256 programs (`//!` of `src/lib.rs`). Check: `cargo nextest run -p srcgen`.
- A program with no form of a later tape (`@field`, query, record, port, handle) has the text that it had before the form. A draw stays on its tape. Check: `cargo nextest run -p srcgen`.
- The builder calls no function that runs a `diagnostic` in a width, a `const`, a struct argument, a parameter type, or a hardware arm. A type expression that reads a mutable root is not reused after a write. Check: `cargo nextest run -p srcgen`.
- The records of `Program::records()` follow the contexts of the builder, with no second identity rule (ADR 0018). The emitted names follow section 7.1. Check: `cargo nextest run -p srcgen`.
- Each twin has no comptime construct, no `match`, no `@`, and no static name. Each register, wire, output, and child input has one `:=`, and each memory has one `read_port` and one `write_port`. Check: `cargo nextest run -p srcgen`.
- A prediction holds only at a site that always runs, else it is `None`. A fixed set of 256 programs has at least 5 predictions of each kind that predicts. Check: `cargo nextest run -p srcgen`.
- A plan draws each public name once, within the caps of the builder (`RES_HELPERS`, `HANDLE_STMTS`, 24 resources and 24 ports in a program). Check: `cargo nextest run -p srcgen`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `syntax` for the lexer, `core-ir` with its feature `gen`, `num-bigint`, `sha2`, and `proptest`. Its only normal user is `xtask`.

## How to test

Run `cargo nextest run -p srcgen`, then `just check` from the repository root.
