# Srcgen

## Purpose

The `srcgen` crate is the source generator of `cargo xtask diff-si`. It is a dev-only crate. No shipped binary depends on it. It comes after `syntax` and before `parse` in the layer order, so it cannot use the code of the stages that it tests. See [ADR 0018](../../doc/adr/0018-source-generator-crate.md) and [the front end design](../../doc/design/2026-10-09-frontend.md), section 11.4.

## Owns

This crate owns the lift of a core design to a source program, and the map from core vectors to source vectors. The lift makes aggregate ports from a shape tape: it groups adjacent ports into a tuple, an array, or a record. An array has the type of its widest member, and the lift resizes a narrower leaf. It makes a source memory from the core block of a registered read. The vector map lists the leaves in the port layout, not in byte order. It also owns the typed form of a generated program, its printer, and its static evaluator. Its builder makes random typed programs and their input lines. The programs hold the forms of slice 2: static containers, records, strings, lists, `mut` formals, function values, and `diagnostic` statements. The builder also predicts the record of each `diagnostic` from the contexts of its modules, and `Program::records()` gives the tails. The twin of a typed program writes out each comptime construct of the program. A mutation of a typed program changes one site, and it predicts the first error code where the pass order makes that code certain. Its kinds reach `S002`, `S003`, `S007`, `S008`, `S016`, and `S018`.

The static evaluator models only the programs that the builder makes. It works on the typed program, never on source text or on a syntax tree. It can reject a program that the language accepts, but it must never give a value that differs from the language. It does not resolve names, check types, compute `cost`, or lower to core IR. A need outside these limits needs a new ADR.

## Invariants

- Only `[dev-dependencies]` and `xtask` name this crate. Check: `cargo xtask check` (rule `workspace-dev-only`).
- This crate does not depend on `parse`, `resolve`, `typeck`, or `elab`. Check: `cargo xtask check` (rule `workspace-layers`).
- Each design of `Config::source()` lifts to a program that lexes with no error, with any shape tape. Check: `cargo nextest run -p srcgen`.
- A core memory lifts only if it has the exact block of section 7.6. Any other shape is `Unsupported::Memory`. Check: `cargo nextest run -p srcgen`.
- Each memory and each aggregate kind occurs in at least 10% of 256 lifted designs. Check: `cargo nextest run -p srcgen`.
- The builder of `typed()` gives no fault on the tested tapes. Each program lexes with no error, and each form of slice 2 occurs in at least 10% of 256 programs. Check: `cargo nextest run -p srcgen`.
- The builder calls no function that runs a `diagnostic` in a width, a `const`, a struct argument, a parameter type, or a hardware arm. Check: `cargo nextest run -p srcgen`.
- A type expression that reads a mutable root is not reused after a write to the root. Check: `cargo nextest run -p srcgen`.
- The records of `Program::records()` come from the contexts of the builder, with no second identity rule (ADR 0018). Check: `cargo nextest run -p srcgen`.
- Each twin of a `typed()` program lexes with no error, and it has no comptime construct and no static name. Check: `cargo nextest run -p srcgen`.
- Each mutant differs from its program and lexes with no error token. A prediction holds on the slice-2 forms, or it is `None`. Check: `cargo nextest run -p srcgen`.
- A prediction of `ValueWindow` or of the four `S016` kinds holds only at a site that always runs. A condition of an arm is a port, a register, or the negation of one. Else the prediction is `None`. Check: `cargo nextest run -p srcgen`.
- A fixed set of 256 programs has at least 5 predictions of `S008` and 5 of `S016`. Check: `cargo nextest run -p srcgen`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `syntax` for the lexer, `core-ir` with its feature `gen`, `num-bigint`, and `proptest`. Its only normal user is `xtask`.

## How to test

Run `cargo nextest run -p srcgen`, then `just check` from the repository root.
