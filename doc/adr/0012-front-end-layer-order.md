# 12. The core IR is the first layer, and type checks split in two

- Status: accepted
- Date: 2026-10-09

## Context

[The architecture](../architecture.md) listed the crates in pipeline order, with `core-ir` after `elab`. A crate depends only on earlier layers. But `elab` produces core IR, so it must depend on `core-ir`. The list thus contradicted the layer rule. `Cargo.toml` already put `core-ir` first.

The list also put `typeck` before `elab`. A width such as `UInt[W + 1]` has no value before elaboration gives `W` a value. A full type check before elaboration is thus not possible. Zig checks a generic function only when code instantiates it, so an error in unused code stays hidden.

## Decision

- The layer order is `core-ir`, `syntax`, `parse`, `resolve`, `typeck`, `elab`, `backend-circt`, `driver`. `core-ir` holds the IR that each later stage uses.
- `typeck` does the generic pre-check. It needs no static values, and it runs on each item, also on an item that no instantiation uses.
- `elab` does the checks that need static values, once for each instantiation.

## Consequences

- `cargo xtask check` (rule `workspace-layers`) enforces the order without an exception.
- An error in unused generic code still shows, when the generic pre-check can find it.
- Width and type errors show only for code that an instantiation executes. The error names the instantiation path.
- A support crate takes a place in the order when it comes into existence: `diagnostics` before `syntax`, and `lsp` after `elab`.
