# Parse

## Purpose

The `parse` crate is the parser of the Rust front end. It is layer 3 of the pipeline, after `syntax`. See [the front end design](../../doc/design/2026-10-09-frontend.md), section 4.4.

## Owns

This crate owns the grammar of the current slice, the error recovery, and the typed AST. The parser builds the lossless `rowan` tree from the tokens of `syntax`. Then it lowers an error-free tree into the AST. Errors are data: each has a code, a line, and a column, and the parser never prints. The parser and the free of the tree run on a thread with a stack for the depth. The function `dump` prints the AST in the bytes of `Print.dump` in Lean. It recurses, so it needs a stack for the syntax depth.

## Invariants

- The AST mirrors `Silicon.Source.Syntax` in Lean: the same types, the same constructors, and the same field order. A column counts Unicode characters. Check: `cargo nextest run -p parse`.
- The text of the tree equals the input, and `parse` never panics, for every string. Check: `cargo nextest run -p parse`.
- The first error in position order is the normative error. It is `S001` or `S004` with the position rules of design section 6.2. Later errors have no oracle. Check: `cargo nextest run -p parse`.
- Syntax of a later slice gives `S004`, never `S001`. An expression or a type has a height of at most the syntax depth, and blocks nest at most that deep. The error is at the first token of the outermost expression or type, or at the `{` of the block. The parser stops when its nesting is above the depth, so its recursion is bounded. The default is 4096, and a deeper input is `S001`, never a stack overflow. Check: `cargo nextest run -p parse`.
- The AST exists only when the text has no error. Check: `cargo nextest run -p parse`.
- `dump` gives the bytes of Lean `Print.dump` for each AST. Check: `cargo nextest run -p parse` and the comparison with `silicon-check parse`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `syntax` for the tokens and the node kinds, and `rowan` for the tree. The tests use `proptest`. The later crate `resolve` reads the AST.

## How to test

Run `cargo nextest run -p parse`, then `just check` from the repository root.
