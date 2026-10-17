# Typeck

## Purpose

The `typeck` crate is the generic pre-check of the Rust front end. It is layer 5 of the pipeline, after `resolve`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.2 and 6.

## Owns

This crate owns pass 4 with `S005`, `S006`, `S007`, and `S008`. These checks need no static value. They run on each item, also on an item that no instantiation uses. They run on both branches of a `comptime if`. Errors are data: each has a code, a line, and a column, and the check never prints. One walk finds all errors and sorts them by position. The check gives the resolved AST unchanged. It also owns the receiver binding of a receiver call. It reads the modes of a prelude function from `resolve`. The Lean module `Source.Check` lists the static positions. `check_expr` checks one expression in the file scope, such as the `EXPR` of `eval`, as a static position.

## Invariants

- `S005` is syntactic and is at the name. A static position names no port, register, wire, memory, or instance. The depth `N` of `mem m: [T; N]` is a static position. The length `N` of `[T; N]` and each index are static positions. The first argument of `list`, and an argument at a `comptime` parameter, also of a receiver call, are static positions. The arguments of a struct constructor, of `data_bits`, and of `str` are not static positions. A `let` alias and a domain name are for `elab`. Check: `cargo nextest run -p typeck`.
- A receiver call binds its receiver to the parameter that `resolve` records: the first one without a written `comptime` mark, also in a `comptime fn`. A function without one is `S007` at the start of the call. Check: `cargo nextest run -p typeck`.
- `S008` follows section 9.1 of the design. A `mut` actual that is not a place, or whose root is not a `let mut` local or a `mut` formal, is `S008` at the start of the actual. So is a `mut` actual whose root is pending in its window. Each root has one counter of the open windows that hold it. Thus a `mut` actual reads and changes one counter, and it scans no window. Check: `cargo nextest run -p typeck`.
- At one position, the walk reports `S007`, then `S008`, then `S005`, as Lean `Check` does. Check: `cargo nextest run -p typeck`.
- `S006` is at the statement. A module body has no `return`. A `comptime fn` has no port, register, wire, memory, instance, or `:=`. It has no call of `read_port` or `write_port` either, also in the receiver form. The rule reads the resolved callee, never the name, so a user function with such a name has none. This `S006` is at the call, and it comes before an `S007` at that position. Check: `cargo nextest run -p typeck`.
- `S007` is at the call, the index, the type name, or the `instance` statement. A call through a local or a constant is not checked. A function type takes no index, in a type and in an expression: `(fn () -> UInt)[8]` is `S007` at the start of the index. A constructor call of a function type has no rule here. A struct takes one index argument for each parameter. Thus a struct with parameters and no index is `S007`, and so is an index on a `type` item. `elab` gives `S007` for an index on a local that holds a type. `read_port` takes three arguments and `write_port` four. `diagnostic` takes two, a message and a value. The prelude struct `ReadResponse` takes one index argument and two constructor arguments. The walk skips its item, because it has no source position. A constructor of a struct takes no argument, which is the zero `T()`, or one argument for each field. A variant constructor `E::V(args)` has one argument for each payload type of `V`, and a path `E::V` without a call has none: `S007` at the start of the path. An enum name takes no index, and a call `E(args)` of it is for `elab`. The tag value of a variant is a static position. The arguments of a variant constructor are not. Check: `cargo nextest run -p typeck`.
- `S007` is also at the start of a variant pattern whose binders and `_` do not match the payload values of its variant. The scrutinee and each arm value are static positions when the `match` is. A binder is a plain local: a static position can name it, and it is no mutable root. Check: `cargo nextest run -p typeck`.
- The first error by position equals the first error of Lean. Check: `cargo nextest run -p typeck`.
- The walk runs through `parse::on_stack` with the syntax depth of the parse. This crate does not size a stack. Check: `cargo nextest run -p typeck`.
- The crate uses no `HashMap` and no `HashSet`. Check: `just clippy`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `resolve` for the targets of names, and `parse` for the AST and the front-end thread. The later crate `elab` reads the checked AST.

## How to test

Run `cargo nextest run -p typeck`, then `just check` from the repository root.
