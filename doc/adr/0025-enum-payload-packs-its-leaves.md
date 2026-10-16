# 25. An enum payload packs its leaves

- Status: accepted
- Date: 2026-10-17

## Context

[ADR 0019](0019-aggregates-lower-to-leaves.md) lowers an aggregate to its leaves. It says that a memory word is the only packed form.

[ADR 0021](0021-enums-and-a-pure-match.md) adds enums with payloads in slice 3. An enum lowers to a record of two fields: the tag and the payload. The variants of one enum have payloads of different types. The payload field thus has one width for all variants. A smaller payload fills the low bits, and the high bits are zero. This layout is visible at ports.

A payload with one core value for each leaf of each variant cannot have one fixed layout. The variants share the payload field, so the payload field must pack the leaves. Issue #268 asked the user, and the user accepted this form on 2026-10-17.

## Decision

- An enum payload is a second packed form, next to a memory word. This replaces the point "a memory word is the only packed form" of ADR 0019. The other points of ADR 0019 stay.
- An enum lowers to two leaves: `tag` of type `UInt[W]` first, then `payload` of type `UInt[P]`. `P` is the largest `data_bits` of the payloads of the variants. When `P` is 0, the payload leaf is empty.
- A variant with the payload types `A, B` packs the tuple `(A, B)` in packing order. The first leaf goes in the least significant bits, as in a memory word. The high bits of the payload are zero.
- A payload binder of a hardware `match` unpacks its leaves with `extract` at the offsets of packing order.
- `reinterpret` converts between an enum `E` and `UInt[data_bits(E)]`. The tag takes the low `W` bits, and the payload takes the next `P` bits.
- The payload width `P` has the limit of a memory word: at most 65536 bits (`S012`).

## Consequences

- The front-end spec records this in decision row F24. Section 7.4 gives the core rows of the pack and the unpack.
- A selection of a payload value costs core nodes: an `extract` for each leaf. A port of an enum type still has one core port for each of its two leaves.
- The tag and the payload get the user fields `tag` and `payload`, for example `op$tag`. `names_injective` needs no change.
- Source vectors and the port schema name the two leaves as `op.tag` and `op.payload`.
- LEC matches a register of an enum type by its two leaves. A difference inside the payload shows as a difference of the whole payload leaf.
