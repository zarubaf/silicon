# 19. An aggregate lowers to its leaves

- Status: accepted, partly superseded by ADR 0025
- Date: 2026-10-12

## Context

Slice 2 of the front end adds arrays, tuples, and records as hardware data ([front-end spec](../design/2026-10-09-frontend.md), section 12.3). The core IR has only one data type, `(bits N)`. Elaboration must thus map each aggregate to core values. Issue #149 compared three options:

- **Leaves.** Each leaf of an aggregate becomes one core value. Ports, registers, wires, and named bindings lower leaf by leaf. Only a memory word packs its leaves into one core value.
- **Packed.** Each aggregate becomes one core value of `data_bits(T)` bits. A selection is an `extract`, and a construction is a `concat`.
- **Mixed.** Leaves inside a module, and packed ports.

The packed form has these costs. Each selection emits a core node. A port has the width limit of 65536 bits. A cycle from one field of a wire to another field of the same wire becomes a false `E008`. A source vector must pack and unpack each port. LEC matches the registers by name, so a packed register hides the field that differs.

## Decision

- Elaboration lowers an aggregate to its leaves. A leaf of a hardware data type is a part of type `Bool`, `UInt[W]`, or `SInt[W]`. The types `Unit` and `[T; 0]` have no leaf. A leaf of a value that is a hardware value is a hardware leaf.
- Each leaf of a port, a register, a wire, a child port, or a named hardware binding is one core value.
- A static selection of a field or an element refers to a leaf or to a subtree. It emits no core node.
- Hardware `==`, `!=`, and `if` on an aggregate emit one core operation for each leaf.
- The leaves of one port follow the packing order of v0.1, section 2. Array index 0, tuple element 0, and the first record field come first, recursively.
- A memory word is the only packed form. Section 7.6 of the front-end spec packs and unpacks the leaves at the memory ports.
- One function owns the port layout in each front end: Lean `Source.Layout` and Rust `elab::layout`. It gives the order of the ports and the expansion of each port into its leaves.

## Consequences

- The evaluator keeps its tree of scalar hardware values. A container holds these trees.
- A core module of a design with aggregate ports has more ports than the source module.
- A source vector maps one leaf to one core port, so the port schema needs no packing.
- A leaf gets a core name with a new made field `<k>e` for an element (section 7.2 of the front-end spec). The theorem `names_injective` covers it.
- A cycle exists only through one leaf. Two leaves of one wire can depend on each other without a cycle.
- An RTL interface with packed ports can come later as a core-to-core pass. It does not change the meaning of a source design.
