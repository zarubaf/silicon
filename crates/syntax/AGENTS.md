# Syntax

## Purpose

The `syntax` crate is the lexer and the lossless syntax tree of the Rust front end. It is layer 2 of the pipeline, after `core-ir`. See [the front end design](../../doc/design/2026-10-09-frontend.md), section 4.4.

## Owns

This crate owns the kinds of tokens and nodes, the `rowan` language of Silicon, and the lexer. The lexer reports each lexical error as data with the code `S001` and a byte offset. It never prints. It takes the syntax depth, and the first bracket above that depth is an error token. The feature `gen` adds the lift of a core design to a source program, and the map from core vectors to source vectors. It also adds the typed form of a generated program, its printer, and its static evaluator. Its builder makes random typed programs and their input lines. The twin of a typed program writes out each comptime construct of the program. Later steps add the typed AST wrappers of the syntax tree and its source printer.

## Invariants

- The texts of the tokens, joined, equal the input for every string. Check: `cargo nextest run -p syntax`.
- The lexer does not panic on any input. An invalid character, an unterminated string, or an unterminated comment gives an error token. Check: `cargo nextest run -p syntax`.
- Operators use longest match, so `>>` is one token. Check: `cargo nextest run -p syntax`.
- Each design of `Config::source()` lifts to a program that lexes with no error, or `lift` returns `Unsupported`. Check: `cargo nextest run -p syntax --all-features`.
- The builder of `typed()` gives no fault on the tested tapes. Each program lexes with no error, and its forms cover slice 1. Check: `cargo nextest run -p syntax --all-features`.
- Each twin of a `typed()` program lexes with no error, and it has no comptime construct and no static name. Check: `cargo nextest run -p syntax --all-features`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `rowan` for the tree. The tests use `proptest`. Its other users are later front-end crates. The feature `gen` uses `core-ir` with its feature `gen`, `num-bigint`, and `proptest`.

## How to test

Run `cargo nextest run -p syntax --all-features`, then `just check` from the repository root.
