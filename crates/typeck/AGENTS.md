# Typeck

## Purpose

The `typeck` crate is the generic pre-check of the Rust front end. It is layer 5 of the pipeline, after `resolve`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.2 and 6.

## Owns

This crate owns pass 4 with `S005`, `S006`, and `S007`. These checks need no static value. They run on each item, also on an item that no instantiation uses. They run on both branches of a `comptime if`. Errors are data: each has a code, a line, and a column, and the check never prints. One walk finds all errors and sorts them by position. The check gives the resolved AST unchanged. `S008` has no code, because slice 1 has no `mut` formal and no expression that mutates a root. The Lean module `Source.Check` lists the static positions. `check_expr` checks one expression in the file scope, such as the `EXPR` of `eval`, as a static position.

## Invariants

- `S005` is syntactic and is at the name. A static position names no port, register, wire, or instance. A `let` alias and a domain name are for `elab`. Check: `cargo nextest run -p typeck`.
- `S006` is at the statement. A module body has no `return`. A `comptime fn` has no port, register, wire, instance, or `:=`. Check: `cargo nextest run -p typeck`.
- `S007` is at the call, the index, the type name, or the `instance` statement. A call through a local or a constant is not checked. Check: `cargo nextest run -p typeck`.
- The first error by position equals the first error of Lean. Check: `cargo nextest run -p typeck`.
- The walk runs through `parse::on_stack` with the syntax depth of the parse. This crate does not size a stack. Check: `cargo nextest run -p typeck`.
- The crate uses no `HashMap` and no `HashSet`. Check: `just clippy`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `resolve` for the targets of names, and `parse` for the AST and the front-end thread. The later crate `elab` reads the checked AST.

## How to test

Run `cargo nextest run -p typeck`, then `just check` from the repository root.
