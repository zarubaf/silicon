# Resolve

## Purpose

The `resolve` crate is the name resolver of the Rust front end. It is layer 4 of the pipeline, after `parse`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.1 and 6.

## Owns

This crate owns the item table, the scopes, the prelude, and the resolved AST. A resolved AST owns the items and the syntax depth of its parse. It does not own the `Parse`. It also owns a map from the node id of each name node to its target. The parser gives the ids. It also maps the node id of each call and each receiver call to its call site. It also records the parameter that the receiver of a receiver call binds to. Two nodes can have the same position, so the maps do not use positions. A target is an index of a declaration, or a prelude name. It has no reference cycle. Errors are data: each has a code, a line, and a column, and the resolver never prints. One walk finds `S002` and `S003`. It reports the `S002` errors if there are any, and else the `S003` errors. Scope lookup uses one `BTreeMap` for each namespace, so a lookup does not depend on the nesting. `resolve_expr` resolves one expression in the file scope, such as the `EXPR` of `eval`, and ranks the errors the same way. It is a different parse, so it has its own map of targets. It keeps the syntax depth of its own parse.

The module `prelude` owns the prelude names. It also owns the parameter modes of each prelude function, from the table in section 5.6 of the design. `typeck` and `elab` read the recorded receiver parameter, and `typeck` reads the modes for the static positions.

## Invariants

- A name is unique in its scope. A scope is the file, the parameters with the top statements of a body, or a block. A declaration can shadow an outer name and a prelude name. Check: `cargo nextest run -p resolve`.

- The position of `S002` is the name in the later declaration. Check: `cargo nextest run -p resolve`.

- Each name resolves. A type name is a prelude type, a `struct` item, a `type` item, an `enum` item, or a local, such as a `type` statement or a parameter of type `Type`. `elab` rejects a local that holds no type. The module of an `instance` is a module item, and a name in an expression is not a module, but the first argument of `Instance`. A local is in scope after its statement. A module without a `domains` clause has the domain `clock`. Items have no order. Check: `cargo nextest run -p resolve`.

- The parameters of a struct and its field types share one scope. A second field with one name is `S002`. A variant name is in no scope: a second variant of one enum with the name is `S002` at it. Check: `cargo nextest run -p resolve`.

- A variant path `X::Y`, also as the callee of a call, resolves `X` by the ordinary scoping, so a local or a parameter `X` shadows an enum item. When `X` is an enum item, `Y` names a variant, else `S003` at `Y`. Any other `X`, also a `type` alias of an enum, is `S003` at the start of the path. `Resolved::variant` gives the enum item and the variant index of a path, by the node id of its first name. A call of a path still takes a call site. The texts equal those of Lean. Check: `cargo nextest run -p resolve`.

- A `match` resolves its scrutinee, then its arms in source order. The path of a variant pattern resolves as a variant path in an expression. The binders of a pattern are locals in a new scope that holds only the value of their arm. So a binder shadows an outer name, and the path resolves before the binders. A second binder with one name in one pattern is `S002` at it. A binder `_` declares no name. A binder of a signature is not a parameter, so it does not make a `fn` generic. Check: `cargo nextest run -p resolve`.

- The prelude has the names of slice 1, `Unit` and `len` of the containers of slice 2, `Type` and `data_bits` of the types as values, and `String`, `List`, `list`, `push`, `pop`, and `str`. It also has the memory functions `read_port` and `write_port`, the function `diagnostic`, the handle type families `Reg`, `Wire`, `Input`, `Mem`, and `Instance`, the function `read`, and the prelude struct `ReadResponse`. A prelude name of a later slice is `S003`. `Domain` is `S003` with its own text, because it waits for more domains. The first argument of `Instance` resolves by the ordinary scoping to a module item. Another first argument is `S003` at its start, and this error replaces each `S003` in that argument, as Lean `indexArgs` does. Check: `cargo nextest run -p resolve`.

- A `fn` item is generic when it has a `comptime` parameter. It is also generic when a parameter type or its result type names one of its parameters, as Lean `generic` says. A name of an item in the signature does not make it generic. A function type resolves its parameter types and its result type as types, and it declares no name. A function name in an expression resolves to its item. Check: `cargo nextest run -p resolve`.

- The function name of a receiver call resolves in the item scope, then in the prelude, and never to a local. A name there that is not a function is `S003` at the name. Check: `cargo nextest run -p resolve`.

- The call site of a call or a receiver call is its number in the pre-order of its item body, from 0. Lean `Resolve` gives the same number. A node comes before its children, and the receiver comes before the arguments. Check: `cargo nextest run -p resolve` and the comparison with `silicon-check elab`.

- The errors of pass 2 come before the errors of pass 3. Each pass reports in position order. Check: `cargo nextest run -p resolve`.

- The walk runs through `parse::on_stack` with the syntax depth of the parse. This crate does not size a stack. The result is safe to drop on any stack, because it owns a plain AST with no `rowan` tree. Check: `cargo nextest run -p resolve`.

- The crate uses no `HashMap` and no `HashSet`. Output order comes from the position. Check: `just clippy`.

- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

- The prelude struct `ReadResponse` is one struct item after the user items, so the user items keep their indices. The resolver builds it already resolved: its names point to the prelude `Type` and `Bool` and to its own parameter, and never go through the item scope. Thus a user `struct Bool` or `type Type` does not change it. A user item `ReadResponse` shadows the name. `Resolved::is_prelude_item` tells it. It has no source position, so a pass that orders by position skips it. Check: `cargo nextest run -p resolve`.

## Dependencies

This crate uses `parse` for the AST, the positions, and the front-end thread. The later crate `typeck` reads the resolved AST.

## How to test

Run `cargo nextest run -p resolve`, then `just check` from the repository root.
