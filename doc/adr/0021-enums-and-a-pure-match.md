# 21. Enums with payloads and a pure exhaustive match

- Status: accepted, partly superseded by ADR 0027
- Date: 2026-10-13

## Context

A decoder, a state machine, and an opcode table are frequent in hardware. In v0.1, the only form for them is a chain of conditionals `if (c) { a } else { b }`. A chain is a priority mux, and it does not show that the cases are disjoint or complete.

The v0.1 spec has no enum and no `match`. It says that a tagged union is a record of explicitly encoded integers and data. Issue #194 asks for both features.

The hardware conditional is pure: each arm holds one expression, not statements. This rule keeps graph effects out of a mux. A new branch form must keep this rule.

## Decision

- An `enum` item declares a tag type, and an explicit tag value for each variant. Example: `enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }`.
- A variant can hold a payload of hardware data. A payload never holds a handle.
- An enum is hardware data. It lowers to a record of two fields: the tag and the payload. The payload field has the largest `data_bits` of the variants. A smaller payload fills the low bits, and the high bits are zero. This layout is visible at ports, so it is normative.
- `match (x) { pattern => expr, ... }` is a pure expression. Each arm holds one expression, as each arm of the conditional does. The effect rules of the hardware conditional apply unchanged.
- A pattern is a static integer, an enum variant with binders for its payload, or `_`.
- A `match` is always exhaustive. The arms cover each value, or a `_` arm covers the rest. Two arms that match the same value are an error. A `_` arm that matches no value is an error.
- Coverage counts each value of the tag type, not only the declared tags. A port, a memory, or `reinterpret` can give an enum value with an unused tag. For example, `Op` above can hold the tags 2 and 3. Thus a `match` on an enum with unused tags needs a `_` arm, and the `_` arm gives the value for each unused tag. An enum that declares each tag value needs no `_` arm, and a `_` arm there is an error. The result of a `match` is thus defined for each bit pattern, as the 2-state semantics require.
- A payload binder reads the low bits of the payload field that its variant uses. The high bits do not change the result.
- A hardware `match` lowers to a parallel mux, not to a priority chain. LEC proves the lowering.
- The features come in slice 3, before the handle features of that slice. `enum` and `match` become keywords in slice 3.

## Consequences

- This deviates from v0.1: the grammar gets two keywords and two forms. The front-end spec records the deviation in its decision table.
- Slice 2 does not change. Its parser accepts `enum` and `match` as identifiers.
- A program of slice 2 that uses `enum` or `match` as a name fails in slice 3.
- Slice 4 (`@typeInfo`, `@Struct`) describes enums from its start.
- The slice 3 spec update gives the grammar, the error codes, and the cost of a `match`. Its corpus tests a `match` on each unused tag of an input port, for example the tags 2 and 3 of `Op`.
- Block expressions and tail expressions stay out (#193). A `match` does not need them.
