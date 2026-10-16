# 26. A handle copies as an identity

- Status: accepted
- Date: 2026-10-17

## Context

Slice 3 of the front end adds handle types, handles in containers, resource-typed formals, and helpers that declare resources. A handle refers to a register, a wire, a memory, an instance, or a child input. Its identity is its structural path and its owner.

A handle can now go through a `let`, a container, a parameter, and a result. One resource can thus have more than one name. Each wire, register, output, and child input must have exactly one binding (`S018`). Issue #268 compared three options:

- **Copyable identity.** A handle copies freely, as in v0.1 and as a Rust `Copy` reference. `S018` counts the bindings of each resource through each alias.
- **Affine handle.** A `:=` uses up its handle, as a Rust move. A second use is an error at the use.
- **Pending window.** A child input handle has a window, as `S008` has for a `mut` actual.

`S018` already checks one binding for each resource at the end of the body of its instantiation. It reports the second binding with the first one. The second and the third option add a second rule for the same guarantee. The user accepted the first option on 2026-10-17.

## Decision

- A handle is a copyable identity. A copy of a handle refers to the same resource. A copy charges the size 1.
- `S018` counts each `:=` of a resource through any alias. An alias is a `let`, an element of a container, a parameter, a result, or a helper that declares the resource. Its message names the declaration and the positions of both bindings.
- A handle is not static, and it is not hardware data. A static position rejects a value that holds a handle (`S011`). A module argument, a `comptime` parameter, an argument of a `comptime fn`, and a `const` are static positions.
- A handle thus cannot reach another owner. The check of the owner in `S017` stays as a guard.

## Consequences

- No rule of use order or move exists. A helper can take a handle, and its caller can keep a copy.
- Two bindings of one resource through two aliases give `S018` at the end of the body of the instantiation. The error is at the second binding, and the message names both positions.
- The cost model needs no new charge for a copy of a handle.
- The front-end spec records this in decision row F28.
