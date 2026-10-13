# Parse

## Purpose

The `parse` crate is the parser of the Rust front end. It is layer 3 of the pipeline, after `syntax`. See [the front end design](../../doc/design/2026-10-09-frontend.md), section 4.4.

## Owns

This crate owns the grammar of the current slice, the error recovery, and the typed AST. From phase 3 of slice 2, the grammar has the `struct` items, the `type` items and statements, and the array type expression `[T; N]`. From phase 4, it has the receiver call `x.m(args)` and the parameter modes, `comptime` and `mut`. From phase 5, it has the function type `fn (T, mut U) -> V`, in a type and as a unary operand in an expression. An expression and a type expression nest in each other, as in Lean `Syntax`. The parser builds the lossless `rowan` tree from the tokens of `syntax` with its own builder. The node cache of `rowan` takes time in the square of the depth. Then it lowers an error-free tree into the AST. Errors are data: each has a code, a line, and a column, and the parser never prints. The parser and `Parse::dump` run on a thread with a stack for the syntax depth. The tree and the AST free their nodes from a work list, with no recursion. If the machine cannot give the stack, the functions return an error value. Only this crate sizes a stack. `on_stack` sizes it for a pass over the AST, and `NestedStack` for a pass that nests. `Parse::dump` prints the AST in the bytes of `Print.dump` in Lean. `parse_expr` parses one expression of the command line, such as the `EXPR` of `eval`. Its positions are in the text of the expression.

## Invariants

- The AST mirrors `Silicon.Source.Syntax` in Lean: the same types, the same constructors, and the same field order. A column counts Unicode characters. Each name node, number literal, call, and receiver call also has a `NodeId`, which is not in Lean. The ids are unique in one parse and in source order. The dump does not print them. Check: `cargo nextest run -p parse`.
- The text of the tree equals the input, and `parse` never panics, for every string. Check: `cargo nextest run -p parse`.
- The first error in position order is the normative error. It is `S001` or `S004` with the position rules of design section 6.2. Later errors have no oracle. Check: `cargo nextest run -p parse`.
- Syntax of a later slice, or of a later phase of slice 2, gives `S004`, never `S001`. Brackets nest at most the syntax depth N, and the lexer marks the first bracket above it. After a parse with no other error, each outermost expression or type has a height of at most N. The error is at its first token. A parser builds a chain in a loop, so the bracket depth limits its recursion for any input. The default is 4096, the cap `MAX_SYNTAX_DEPTH` is 65536, and a deeper input is `S001`, never a stack overflow. Check: `cargo nextest run -p parse`.
- At `[`, the parser picks the array type expression when a `;` follows the first element at the depth of the bracket. It does not try again, so the parse stays linear. An element of `[T; N]` that is not a type, as the `0` of `[0; 4]`, is `S001` at its first token. Each parameter of a module and of a struct has `comptime`, else `S001`. A parameter of a `fn` has at most one mode: a second mark is `S001`. A parameter type of a function type has no `comptime` mark: `S001` at the mark. A chain of function types is read in a loop. A function type has the height 1 plus the largest height of its parts, and a `mut` mark adds none. Check: `cargo nextest run -p parse`.
- After a postfix operand, `.` with a name and `(` makes a receiver call. The node has the position of its receiver, and it is never a place. Thus `=` or `:=` after it is `S001`. Check: `cargo nextest run -p parse`.
- The body of a `fn` without `comptime` has no `input`, `output`, `reg`, `wire`, or `instance` statement: `S004` at its keyword. Check: `cargo nextest run -p parse`.
- The AST exists only when the text has no error. Check: `cargo nextest run -p parse`.
- `Parse::dump` gives the bytes of Lean `Print.dump` for each AST. Check: `cargo nextest run -p parse` and the comparison with `silicon-check parse`.
- A pass that recurses over the AST runs on the front-end thread, the thread with the stack for the depth. Everything the crate exposes is safe on any stack: `Parse` and the AST have no `Clone` and no `Debug`, and their `Drop` is iterative. Check: `cargo nextest run -p parse`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate uses `syntax` for the tokens and the node kinds, and `rowan` for the tree. The tests use `proptest`. The later crate `resolve` reads the AST.

## How to test

Run `cargo nextest run -p parse`, then `just check` from the repository root.
