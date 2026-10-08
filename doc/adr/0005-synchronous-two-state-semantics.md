# 5. Synchronous, 2-state semantics only

- Status: accepted
- Date: 2026-10-08

## Context

The semantics of a hardware description language can need an LRM of many hundred pages. Silicon wants a semantics that fits in a few pages.

## Decision

- The semantics is synchronous and 2-state. Registers are first-class primitives.
- The core IR contains registers, memories, pure combinational logic, and module instances. The semantics of a design is a Mealy machine.
- More than one clock is possible. A crossing between clock domains goes through an explicit CDC primitive. The type system rejects a crossing without synchronization.
- Black boxes with assumed contracts cover SRAM macros, PLLs, vendor IP, and clock gates.

## Consequences

- The semantics of each clock domain stays simple.
- The toolchain does not check 4-state logic, CDC, or timing. Existing dedicated tools cover them.
- Black boxes are on the trusted side of [the trust boundary](../trust.md).
- Reset semantics and the memory model are still open. See the open questions in [the architecture](../architecture.md).
