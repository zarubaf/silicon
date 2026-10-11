# Resolve

## Purpose

The `resolve` crate is the name resolver of the Rust front end. It is layer 4 of the pipeline, after `parse`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.1 and 6.

## Owns

This crate owns the item table, the scopes, the prelude of slice 1, and the resolved AST. A resolved AST owns the items and the syntax depth of its parse. It does not own the `Parse`. It also owns a map from the node id of each name node to its target. The parser gives the ids. Two nodes can have the same position, so the map does not use positions. A target is an index of a declaration, or a prelude name. It has no reference cycle. Errors are data: each has a code, a line, and a column, and the resolver never prints. One walk finds `S002` and `S003`. It reports the `S002` errors if there are any, and else the `S003` errors. Scope lookup uses one `BTreeMap` for each namespace, so a lookup does not depend on the nesting. `resolve_expr` resolves one expression in the file scope, such as the `EXPR` of `eval`. It is a different parse, so it has its own map of targets. It keeps the syntax depth of its own parse.

## Invariants

- A name is unique in its scope. A scope is the file, the parameters with the top statements of a body, or a block. A declaration can shadow an outer name and a prelude name. Check: `cargo nextest run -p resolve`.
- The position of `S002` is the name in the later declaration. Check: `cargo nextest run -p resolve`.
- Each name resolves. A type name is a prelude type, the module of an `instance` is a module item, and a name in an expression is not a module. A local is in scope after its statement. A module without a `domains` clause has the domain `clock`. Items have no order. Check: `cargo nextest run -p resolve`.
- The prelude has only the names of slice 1. A name of a later slice is `S003`. Check: `cargo nextest run -p resolve`.
- The errors of pass 2 come before the errors of pass 3. Each pass reports in position order. Check: `cargo nextest run -p resolve`.
- The walk runs through `parse::on_stack` with the syntax depth of the parse. This crate does not size a stack. The result is safe to drop on any stack, because it owns a plain AST with no `rowan` tree. Check: `cargo nextest run -p resolve`.
- The crate uses no `HashMap` and no `HashSet`. Output order comes from the position. Check: `just clippy`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `parse` for the AST, the positions, and the front-end thread. The later crate `typeck` reads the resolved AST.

## How to test

Run `cargo nextest run -p resolve`, then `just check` from the repository root.
