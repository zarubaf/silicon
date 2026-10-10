# Parse

## Purpose

The `parse` crate is the parser of the Rust front end. It is layer 3 of the pipeline, after `syntax`. See [the front end design](../../doc/design/2026-10-09-frontend.md), section 4.4.

## Owns

This crate owns the grammar of the current slice, the error recovery, and the typed AST. The parser builds the lossless `rowan` tree from the tokens of `syntax`. Then it lowers an error-free tree into the AST. Errors are data: each has a code, a line, and a column, and the parser never prints. The AST dump is not here yet. It waits for the dump format of Lean.

## Invariants

- The AST mirrors `Silicon.Source.Syntax` in Lean: the same types, the same constructors, and the same field order. A column counts Unicode characters. Check: `cargo nextest run -p parse`.
- The text of the tree equals the input, and `parse` never panics, for every string. Check: `cargo nextest run -p parse`.
- The first error in position order is the normative error. It is `S001` or `S004` with the position rules of design section 6.2. Later errors have no oracle. Check: `cargo nextest run -p parse`.
- Syntax of a later slice gives `S004`, never `S001`. An expression or a type has a height of at most 64, and blocks nest at most 64 deep. Check: `cargo nextest run -p parse`.
- The AST exists only when the text has no error. Check: `cargo nextest run -p parse`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `syntax` for the tokens and the node kinds, and `rowan` for the tree. The tests use `proptest`. The later crate `resolve` reads the AST.

## How to test

Run `cargo nextest run -p parse`, then `just check` from the repository root.
