# Lean

## Purpose

The Lean model is the normative spec for Silicon.

## Owns

This directory owns two models. Dispatch Lean work to a fresh Opus subagent.

- `Silicon/Core/` holds the core IR semantics.
- `Silicon/Source/` holds the reference front end: the lexer, the parser, the printer, the resolver, the generic pre-check, the evaluator, the elaborator, and the lowering. `Source/Test/` holds its `#guard` tests. Its spec is [the front-end spec](../doc/design/2026-10-09-frontend.md).

The front end holds a hardware aggregate (spec sections 5.1, 5.4, and 7.4) in these forms:

- `Eval.Agg` is a tree of `static`, `hw`, `ref`, `array`, `tuple`, and `record` parts. Each container `Node` stores its type, its size, its depth, and its count of hardware leaves. Thus no charge walks the tree. A container without a hardware leaf stays a static `Value`.
- A `ref` is lazy. A read of an aggregate port, register, wire, or child output gives a `ref` with no charge. A static selection gives a sub-reference in one step (`Base.sub`). `normalize` makes a part without a hardware leaf a static value, and it charges the zero size first.
- `Base.out` holds the fields of a child output part in reverse order, so a step adds a field in constant work. `Base.op` puts them in order once.
- `Agg.change` refreshes the stored numbers of each node on the path of a list part in one step. The caller charges the part counts before the change.
- `==`, `!=`, and a hardware `if` walk both operands by leaf. A static pair compares as a static equality. In an `if`, a static pair with different sides, or with equal sides without the joined type, is `S011` (F19), also at a scalar root.
- A binding with a hardware leaf takes one version, and each hardware leaf gets one `Let`.
- `Op.share k` marks the condition of an aggregate `if` with two or more `mux` nodes. It has no charge. `Flatten` binds it to a temporary at its first lowering in the module.
- `Layout.foldLeaves` streams the leaves of a port in packing order. No other module expands a port. `Flatten` charges each leaf before it makes the leaf, and `Vectors` gives each leaf one schema entry.
- `Flatten` lowers the left spine of a chain of binary nodes in a loop. Thus the `==` chain of a large aggregate does not grow the stack.
- The Lean walks over an aggregate recurse on its structure. The depth of the value bounds them.

## Invariants

- Do not use `sorry`. Check: `cargo xtask check` (rule `lean-sorry`).
- Add no new `axiom`. Check: `cargo xtask check` (rule `lean-axiom`, with `allowlist.toml`).
- Use `native_decide` only in files listed in `allowlist.toml`. Check: `cargo xtask check` (rule `lean-native-decide`).
- Use at most 100 characters per line, no tabs, and no trailing spaces. Check: `cargo xtask check` (rule `lean-style`).
- Put each Lean source in `Silicon.lean` or under `Silicon/`. Lake builds only these files. Check: `cargo xtask check` (rule `lean-layout`).
- Treat build warnings as errors. Check: `lake -d lean build --wfail`.

## Dependencies

Lean has no dependencies on `crates/`.

## How to test

Run `just check` from the repository root.

Run `lake -d lean exe silicon-check check FILE` to check a design. Run `silicon-check parse`, `eval`, `cost`, `elab`, or `validate` for the front end.
