# 30. The keys of a query have their own effect texts

- Status: accepted
- Date: 2026-10-25

## Context

[ADR 0028](0028-builtins-are-a-closed-set-of-static-queries.md) says that the keys and the indices of a `@TypeOf` or `@ports` operand evaluate in a structural context. It also says that a graph effect or a mutation of an earlier binding there is `S016`, with the existing texts. The existing texts of a structural context say "a type or a constant". A key of a query is neither, so these texts do not tell the user where the effect is.

A family key, an index of a `:=` target, and an `as` key already have guard kinds of their own, with texts that name the context. Issue #344 asked which texts a key of a query gets (Q1). The user accepted the new guard kind on 2026-10-25.

## Decision

- A key of a query operand evaluates under the new guard kind `query`. This applies to each index, each key of `@field`, and each key of a family selection in the operand, at each depth.
- The kind `query` is a structural context. Only its texts are new: "Mutation in a query key" and "Graph effect in a query key". Each text names the builtin.
- This replaces the words "with the existing texts" of ADR 0028. The other points of ADR 0028 stay.

## Consequences

- An `S016` in a query tells the user which builtin holds the key, and how to move the effect out of the key.
- The rule of structural contexts stays one rule. A new kind adds two texts and no new check.
- The front-end spec records this in decision row F31 and in the messages of section 9.4.
