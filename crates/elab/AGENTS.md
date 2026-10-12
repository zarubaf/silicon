# Elab

## Purpose

The `elab` crate is the elaborator of the Rust front end. It is layer 6 of the pipeline, after `typeck`. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.4, 4.5, and 5.

## Owns

This crate owns the static values with their canonical serialization, their recursive size, and their depth. In slice 2, the static values include the containers `()`, tuples, arrays, records, and lists, the strings, and the types as values. It also owns SHA-256 for the digest names. It owns the evaluator with the fuel, the nesting depth, the cost model, the table of constants, and the hardware values. It owns the table of instantiations with the checks for each instantiation, the core names, and the emitted module names. It owns the lowering to core IR, the port layout, and the port schema of the source vectors. The Lean modules `Source.Value`, `Source.Sha256`, `Source.Eval`, `Source.Elab`, `Source.Names`, `Source.Layout`, `Source.Flatten`, and `Source.Vectors` are the normative definitions.

The scan keeps the values of the number literals and the symbols of the field names. Their keys are the node ids of the parser, not the positions, because two nodes can have the same position. The call site of a call frame comes from `resolve`.

A hardware value is a node in one arena, so a new node shares its operand trees. A structural path is a node in a second arena, and a user field holds the symbol of its name. Thus a new node or a new name costs constant work and no copy. A static type is an id in a third table, `Types`, with one id for each equal type. An id carries the size and the depth of its type. Thus a copy and an equality of types cost constant work. An array value and a record hold the id of their type. The module `types` holds this table, the type metadata of design section 5.4, and the table of struct specializations. A specialization is keyed by its struct item and its static arguments after their typed use. A struct type carries the metadata, so `T()` and `data_bits` never walk the field types. The module `serial` writes the canonical serialization, and `text` writes the bounded text of a type or a value in a message. Both walks keep their own stack. In the evaluator, `eval/types` evaluates the type expressions, the `type` aliases, and the specializations with their charges and `S019`. `eval/record` evaluates the constructors, the zero `T()`, the fields, and `data_bits`. `eval/call` evaluates the calls and the receiver calls, binds the parameters, and runs the write-backs of the `mut` formals. `eval/place` resolves the places of assignments and of `mut` actuals. `eval/string` evaluates the string index, `len`, and `str`. `eval/list` evaluates `list`, `push`, and `pop`. The module `counters` counts the work of the walks and the operations for each run, by its fuel budget, and only the tests compile it.

The elaborator core keeps to the Rust subset of design section 4.5: plain owned data, `match`, `Vec`, `Box`, and no `Rc`, no `unsafe`, and no trait object. The module `int` holds the static integer behind a small interface, and only this module computes with `num-bigint`. It also holds each conversion between an integer and a finite value. A finite value uses the bit vector of `core-ir`, as the core semantics does.

## Invariants

- The serialization of a value equals the bytes of `Value.serialize` in Lean. The recursive size equals `Value.size`, and the depth equals `Value.depth`. Check: `cargo nextest run -p elab`.
- The digest equals the test vectors of FIPS 180-4. Check: `cargo nextest run -p elab`.
- The evaluator charges each unit of `Source.Eval` in the same order and at the same node. The charge comes before the work, and each operation keeps its work and its memory in its charge. Thus the value, the used fuel, and the code and the position of the first error equal those of Lean. Check: `cargo nextest run -p elab` and the comparison with `silicon-check eval`.
- The elaboration charges each unit of `Source.Elab` in the same order and at the same node. The units of each instantiation, the emitted names, and the code and the position of the first error equal those of Lean `Elab.elaborate`. Check: `cargo nextest run -p elab` and the comparison with `silicon-check cost`.
- `decode(encode(p)) == Some(p)` for each valid name `p`, and each encoded name is a legal core name. Check: `cargo nextest run -p elab`.
- An error message prints at most 256 bits of an integer, 64 characters of a string, and 1024 bytes of the text of a type. Check: `cargo nextest run -p elab`.
- The evaluator recurses, so it runs through `parse::NestedStack`, and it only finds the heights of the AST. A call, a constant, and an instantiation each start a nesting level. Each thread runs a group of nesting levels, so any nesting depth is safe. A design and an error hold no recursive value, so they drop safely on any stack. No walk over a value or a type recurses, so a value of any depth is safe on any stack, also in the driver. A result that refers to a local or a constant copies nothing until a copy pays for it. An assignment to a place with an index copies only the containers on the path of the place. Check: `cargo nextest run -p elab`.
- `push`, `pop`, and a `mut` write-back change the live root in one walk down the path of the place. A `pop` of a held root walks the path twice, and the charge of the root pays for the second walk. They copy no list and no root. A string operation charges the size of the string before it scans, and `s = s + t` makes one new string. Check: `cargo nextest run -p elab`.
- A result keeps the value that its expression read. A result that refers to a local waits in the store while a later operand, argument, or index evaluates. A waiting reference to a static value holds its local (design section 5.4). A mutation of a held local first charges the size of the local, then copies each waiting reference to it. Each copy is at most that size, and one expression of the source holds the waiting references. Check: `cargo nextest run -p elab` and the comparison with `silicon-check eval`.
- A `mut` actual binds its formal only at the type of its place, with no typed use. The write-backs run after the result binds, in the order of the parameters, at the position of the call. Each checks `S016`, then the depth of the root, then charges, then writes. Check: `cargo nextest run -p elab` and the comparison with `silicon-check run`.
- The crate uses no `HashMap` and no `HashSet`. Check: `just clippy`.
- Non-test code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate reads a `Resolved` that passed `typeck`. It uses `resolve` for the targets of names, and `parse` for the AST and the front-end thread. It uses `core-ir` for the operations on finite values and the keywords of core names. The tests use `typeck` and `proptest`. The `driver` calls it.

## How to test

Run `cargo nextest run -p elab`, then `just check` from the repository root.
