# Syntax

## Purpose

The `syntax` crate is the lexer and the lossless syntax tree of the Rust front end. It is layer 2 of the pipeline, after `core-ir`. See [the front end design](../../doc/design/2026-10-09-frontend.md), section 4.4.

## Owns

This crate owns the kinds of tokens and nodes, the `rowan` language of Silicon, and the lexer. The lexer reports each lexical error as data with the code `S001` and a byte offset. It never prints. It takes the syntax depth, and the first bracket above that depth is an error token. Later steps add the typed AST wrappers, the source printer, and the generator `gen`.

## Invariants

- The texts of the tokens, joined, equal the input for every string. Check: `cargo nextest run -p syntax`.
- The lexer does not panic on any input. An invalid character, an unterminated string, or an unterminated comment gives an error token. Check: `cargo nextest run -p syntax`.
- Operators use longest match, so `>>` is one token. Check: `cargo nextest run -p syntax`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `rowan` for the tree. The tests use `proptest`. Its other users are later front-end crates.

## How to test

Run `cargo nextest run -p syntax`, then `just check` from the repository root.
