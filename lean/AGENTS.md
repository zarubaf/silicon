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
- `Op.share k` marks the condition of an aggregate `if` with two or more `mux` nodes, and the operand of a hardware unpack. It charges the size of its operand once, when it is made. In a value, it has the size of a core name of its type. `Flatten` binds it to a temporary at its first lowering in the module.
- `Layout.foldLeaves` streams the leaves of a port in packing order. No other module expands a port. An enum has the leaves `tag` and `payload`, and `Design.fields` gives the named parts of a struct and an enum. `Flatten` charges each leaf before it makes the leaf, and `Vectors` gives each leaf one schema entry.
- `Flatten` lowers the left spine of a chain of binary nodes in a loop. `lowerPack` and `memData` build their `concat` chains in a loop, and `lowerMatch` builds the `or` chains of a hardware `match` in a loop. They bind a temporary at the height 64. Thus the `==` chain of a large aggregate, a wide pack, and a `match` with many arms do not grow the stack.
- `lowerMatch` lowers a `onehot` node in the order of section 7.4: the selects, then the values, then the `replicate`, `and`, and `or` nodes. `rest` is an `or` chain inside an `xor` with `(const 1 1)`. Each mark binds at its first lowering in the module.
- The Lean walks over an aggregate recurse on its structure. The depth of the value bounds them.

A memory (spec section 6.2 and section 7.6) uses these parts:

- `Handle.mem` is the handle of a `mem` statement. `Eval.Mem` in `Naming.mems` holds its path, depth, word type, first read request, first write request, and first second call (`dup`). `Body.mems` gives them to `Flatten`.
- A word reference is `Base.word mem off` or `Op.word mem off`. The `off` is the bit offset in the word. A step with `Base.sub` adds `Ty.offset`, the sum of the earlier widths. Both hold a path id, never a path copy.
- `Eval.portCall` runs a port call in this order: the copies, the memory check, `S016` in a guard, and the typed uses. Then it records the request. A read then charges the struct use of `ReadResponse[T]`, its depth, and its zero size. The response is lazy: `data` is the word at the offset 0, and `valid` is `m$0rvalid`. A second call charges the same and keeps `S018` for the end of the body.
- `Flatten.lowerMem` lowers each memory as one block, in the order of section 7.6. The write chain is a fold over `Layout.foldLeaves`. It binds a temporary at the height 64. Each core node charges before it exists, at the position of the `mem` statement. A word leaf is an `extract` of `m$0rdata`.
- The prelude item `ReadResponse` is `Resolve.response`. It has the `prelude` flag, and it comes after the user items, so no user number changes. `Eval.atUse` moves each error of its specialization to the use position.

The evaluator holds the innermost guard of section 9.4 in `Ctx.guard : Option Guard`. A guard has a kind, `arm` or `structural`, and the nesting depth at its start. A hardware `if` sets an `arm` guard for its arms. `structural` sets a `structural` guard in these contexts. They are each type expression, each form that makes a type, and the first use of a constant. They are also each struct use, and the word type and depth of a `mem` statement. The innermost guard wins. A `push`, a `pop`, or a write-back of a binding of the depth of the guard is `S016` (`mutation`), and so is a graph effect (`portCall`). A call nests deeper, so a helper can change its own locals. `Guard.change` and `Guard.effect` give the texts, and the Rust front end prints them exactly.

`diagnostic(message, value)` (spec sections 5.4, 6.2, and 8.2) adds one `Record` (a line of text) to `St.records`. `Eval.diagnose` runs after the copy charge: the guard, the message, the measure charge (`Val.measureCharge`), the byte charge, and then the record. The text comes from the pure `render` functions (`Ty.render`, `Agg.render`, `Handle.render`). They never call `normalize`, and a `ref` renders from its type. `Ctx.inst` holds the emitted name, and `Ctx.calls` holds the frames. A frame push is O(1), and the byte charge pays for the frames. `fail` is the only error: it builds a `Stop { err, records }` from `St.records`, so an error keeps the records. `Eval.observeRun`, `Eval.observeExpr`, and `Elab.observe` return the records with both outcomes. `Eval.run`, `Eval.evalExpr`, and `Elab.elaborate` are their projections.

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

Run `lake -d lean exe silicon-check check FILE` to check a design. Run `silicon-check parse`, `eval`, `cost`, `elab`, `observe`, or `validate` for the front end. `observe` prints the records, then the first error.
