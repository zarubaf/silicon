# 29. Port families and public keys

- Status: accepted
- Date: 2026-10-19

## Context

Slice 4 of the front end adds port families, `as` keys, and ports in helpers, as in v0.1. An arbiter declares `input req[i]: T;` in a loop. A lane helper declares the ports of one lane, and a parameter gives their names. Up to slice 3, a port in a `fn` is `S004` (decision F29), because no source form can give a port a computed name.

The port names are the interface of a module. The schema, the source vectors, and the parent use them. Thus the rules must keep each public name unique and each core name injective.

Issue #333 asked four questions about them:

- **Q6.** Where is a family name visible?
- **Q7.** Which core name does a family entry get?
- **Q8.** Which public name does a port in a helper get?
- **Q9.** Which form does an `as` key have?

It also asked which code the name rule of a computed name gives (Q5). The user accepted the recommended option of each question on 2026-10-19.

## Decision

- `input req[i]: T;` and `output gnt[i]: T;` declare one whole port at the static key `i`. A family is a namespace of keys, not a value.
- A family name has module scope. The resolver collects each indexed declaration of the module body at each block depth. A second loop can thus read `req[i]` from the first loop.
- A family entry gets the new made field `<k>f` after its basename, for example `req$3f`.
- `input pin: T as key;` gives the port a public key. The key is a static `String` or a `PortKey`. The binder `pin` stays the name in the body. The parent and the schema use the key.
- A public name is an ASCII identifier that is not a Silicon keyword. A new code `S022` reports a name that breaks this rule.
- A `fn` without `comptime` can declare a port. The port keeps its binder or its key as its public name. The call frame does not change it. A second port with one public name is `S019`, and its text tells the user to add a key with `as`.

## Consequences

- An arbiter can declare its requests in one loop and read them in a second loop. With block scope, only the parent can read a family from a loop.
- The field `<k>f` is injective by construction. The element field `<k>e` needs a side condition in `names_injective`, and the integer field collides with a loop frame.
- A `PortKey` gives a family entry with a computed basename. A Rust attribute such as `#[name = key]` adds a syntax that no other item has.
- A helper that a design calls once needs no `as` key. A helper that a design calls twice needs a key from a parameter.
- Decision F29 closes. The front-end spec records these points in decision rows F34, F35, F36, and F37.
