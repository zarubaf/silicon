# Lean

## Purpose

The Lean model is the normative spec for Silicon.

## Owns

This directory owns two models. Dispatch Lean work to a fresh Opus subagent.

- `Silicon/Core/` holds the core IR semantics.
- `Silicon/Source/` holds the reference front end: the lexer, the parser, the printer, the resolver, the generic pre-check, the evaluator, the elaborator, and the lowering. The evaluator holds the one statement walk: `Eval.stmt` charges a statement, and a module statement then runs in `Eval.hwStmt`, which can instantiate a child (`Eval.instantiate`). `Eval/Inst.lean` holds the parts of an instantiation that need no evaluation. `Elab` holds the top selection and the design. `Source/Test/` holds its `#guard` tests. Its spec is [the front-end spec](../doc/design/2026-10-09-frontend.md).

The front end holds a hardware aggregate (spec sections 5.1, 5.4, and 7.4) in these forms:

- `Eval.Agg` is a tree of `static`, `hw`, `ref`, `handle`, `array`, `tuple`, `record`, and `list` parts. Each container `Node` stores its type, its size, its depth, and its count of hardware leaves. Thus no charge walks the tree. A container without a hardware leaf stays a static `Value`, unless its type has the handle flag (`Meta.handles`). The flag, not the value, decides what is static, so an empty `list(Reg[T])` is a `list` node.
- A `ref` is lazy. A read of an aggregate port, register, wire, or child output checks the depth of its zero (`readRef`), then gives a `ref` with no charge. A static selection gives a sub-reference in one step (`Base.sub`). `normalize` makes a part without a hardware leaf a static value, and it charges the zero size first.
- `Base.out` holds the fields of a child output part in reverse order, so a step adds a field in constant work. `Base.op` puts them in order once.
- `Agg.change` refreshes the stored numbers of each node on the path of a list part in one step. The caller charges the part counts before the change. A `push` onto a `list` node refreshes it by a delta.
- `==`, `!=`, and a hardware `if` walk both operands by leaf. A static pair compares as a static equality. In an `if`, a static pair with different sides, or with equal sides without the joined type, is `S011` (F19), also at a scalar root.
- A binding with a hardware leaf takes one version, and each hardware leaf gets one `Let`.
- `Op.share k` marks the condition of an aggregate `if` with two or more `mux` nodes, and the operand of a hardware unpack. It charges the size of its operand once, when it is made. In a value, it has the size of a core name of its type. `Flatten` binds it to a temporary at its first lowering in the module.
- `Layout.foldLeaves` streams the leaves of a port in packing order. No other module expands a port. An enum has the leaves `tag` and `payload`, and `Design.fields` gives the named parts of a struct and an enum. `Flatten` charges each leaf before it makes the leaf, and `Vectors` gives each leaf one schema entry.
- `Flatten` lowers the left spine of a chain of binary nodes in a loop. `lowerPack` and `memData` build their `concat` chains in a loop, and `lowerMatch` builds the `or` chains of a hardware `match` in a loop. They bind a temporary at the height 64. Thus the `==` chain of a large aggregate, a wide pack, and a `match` with many arms do not grow the stack.
- `lowerMatch` lowers a `onehot` node in the order of section 7.4: the selects, then the values, then the `replicate`, `and`, and `or` nodes. `rest` is an `or` chain inside an `xor` with `(const 1 1)`. Each mark binds at its first lowering in the module.
- The Lean walks over an aggregate recurse on its structure. The depth of the value bounds them.

A memory (spec section 6.2 and section 7.6) uses these parts:

- `Handle.mem` is the handle of a `mem` statement. `Eval.Mem` in `Naming.mems` holds its path, depth, word type, first read request, first write request, and the positions of the first calls. A second call records its `S018` data (`Breach`) in `Work.dup`, and the text renders once, for the error that wins. `Body.mems` gives them to `Flatten`.
- A word reference is `Base.word mem off` or `Op.word mem off`. The `off` is the bit offset in the word. A step with `Base.sub` adds `Ty.offset`, the sum of the earlier widths. Both hold a path id, never a path copy.
- `Eval.portCall` runs a port call in this order: the copies, the memory check, `S016` in a guard, and the typed uses. Then it records the request. A read then charges the struct use of `ReadResponse[T]`, its depth, and its zero size. The response is lazy: `data` is the word at the offset 0, and `valid` is `m$0rvalid`. A second call charges the same and keeps `S018` for the end of the body.
- `Flatten.lowerMem` lowers each memory as one block, in the order of section 7.6. The write chain is a fold over `Layout.foldLeaves`. It binds a temporary at the height 64. Each core node charges before it exists, at the position of the `mem` statement. A word leaf is an `extract` of `m$0rdata`.
- The prelude struct items come after the user items, so no user number changes. `Resolve.preludeStructs` builds them in the order of design section 5.6: `ReadResponse`, `FieldInfo`, `TypeInfo`, `VariantInfo`, `PortKey`, and `PortInfo`. Each has the `prelude` flag, and its field types never resolve in the user scope. `Eval.atUse` moves each error of their specialization to the use position.

The evaluator holds the innermost guard of section 9.4 in `Ctx.guard : Option Guard`. A guard has a kind and the nesting depth at its start. The kinds are `arm`, `structural`, and the structural kinds `key`, `index`, and `name` of a family key, a target index, and an `as` key. A hardware `if` sets an `arm` guard for its arms. `structural` sets a `structural` guard in these contexts. They are each type expression, each form that makes a type, and the first use of a constant. They are also each struct use, and the word type and depth of a `mem` statement. The innermost guard wins. A `push`, a `pop`, or a write-back of a binding of the depth of the guard is `S016` (`mutation`), and so is a graph effect (`portCall`). A call nests deeper, so a helper can change its own locals. `Guard.callee` holds the item of the outermost call under the guard, and `Ctx.mode` holds the `eval` command or the item of the outermost `comptime fn` of the call chain. A call sets each in O(1), and the name renders only in an error. A declaration or a `:=` checks the guard (`S016`), then the mode (`S011`), after its charge. `Guard.change` and `Guard.effect` give the texts, and the Rust front end prints them exactly.

`diagnostic(message, value)` (spec sections 5.4, 6.2, and 8.2) adds one `Record` (a line of text) to `St.records`. `Eval.diagnose` runs after the copy charge: the guard, the message, the measure charge (`Val.measureCharge`), the byte charge, and then the record. The text comes from the pure `render` functions (`Ty.render`, `Agg.render`, `Handle.render`). They never call `normalize`, and a `ref` renders from its type. `Ctx.inst` holds the emitted name, and `Ctx.calls` holds the frames. A frame push is O(1), and the byte charge pays for the frames. `fail` is the only error: it builds a `Stop { err, records }` from `St.records`, so an error keeps the records. `Eval.observeRun`, `Eval.observeExpr`, and `Elab.observe` return the records with both outcomes. `Eval.run`, `Eval.evalExpr`, and `Elab.elaborate` are their projections.

Handles (spec sections 5.1, 5.2, and 9.4): `typedUse` compares each handle leaf by its type. `data` charges the size, then reads each register leaf and wire leaf in packing order. A static position checks the value (`staticValue`), then the type (`staticHandle`). Both read only the flag and the kind. `Eval.targetPart` walks the steps of a `:=` target; the type of each base decides. `read(h)` (spec section 5.4) is `Eval.readOf`: the copy, then `S017` for a child input or `S010` with the fix `readHint`, then `readRef`. Its result refers to the resource (`Out.ref`), so `let x = read(r)` charges the zero size once, before the leaves bind. A result without a hardware leaf is a new static value, so its binding is no copy.

Port families (spec section 5.6): before the statements of a module body, the resolver gives each family one binder with the reference `Ref.family`. An entry has no frame slot. `Work.entries` holds its value by the symbol of the public name and the key, and a port has the identity `(symbol, key)` (`PortId`). `Work.publics` holds the form of each public name of the owner. `Syms.families` and the families of `Work.publics` give `Iface.families`, so a family of a child exists also without an entry. `Syms.table` and `St.names` give each text one symbol (`Eval.symbolOf`). `Elab.familyKey` does the type and range checks of each key. `familySel` selects an own entry, `childSel` an entry of a child, and `Elab.walkStep` an entry of a child in a `:=` target, with no second walk from the root. An error renders an entry as `x[k]` (`entryText`), and a binding copies no name. `Elab.publicOf` reads `Work.publics`, then the static `Syms.families` of `Work.owner`, so no instantiation copies the families. `Elab.keyed` runs the steps of an `as` key: the key value (`portKey`), the size charge of the name, and the name rule (`Lex.identifier`, `S022`). Then `Elab.port` or `Elab.entry` declares the port by its public name. A port of a helper belongs to the owner, and its binder takes a slot in the frame of the helper.

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

Run `just check` from the repository root. Run `lake -d lean exe silicon-check check FILE` to check a design. Run `silicon-check parse`, `eval`, `cost`, `elab`, `observe`, or `validate` for the front end. `observe` prints the records, then the first error.
