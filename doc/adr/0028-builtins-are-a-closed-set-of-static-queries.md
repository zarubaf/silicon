# 28. The builtins are a closed set of static queries

- Status: accepted
- Date: 2026-10-19

## Context

Slice 4 of the front end adds the `@` builtins of v0.1: `@TypeOf`, `@typeInfo`, `@Struct`, `@field`, and `@ports`. A wrapper, a bus adapter, and a generic register file need them. They read the type of a binding, the metadata of a type, and the ports of a child. `@Struct` makes a record type, and `@field` selects a part by a computed key.

Issue #333 asked five questions about them:

- **Q1.** Which builtins exist, and with which names?
- **Q2.** Which effects can the keys and the arguments of a query have?
- **Q3.** Which stage rejects an operand of `@TypeOf` or `@ports` that is not a selection of a binding?
- **Q10.** How does a query pay for its result?
- **Q11.** What is the identity of a record type that `@Struct` makes?

The user accepted the recommended option of each question on 2026-10-19.

## Decision

- The builtins are the five of v0.1, with their v0.1 names. Each other `@` name is `S001`. A builtin is not a macro, and the source cannot add one.
- No builtin makes hardware, and no builtin instantiates a module. `@TypeOf` and `@ports` never read a register or a wire for their operand.
- The keys and the indices of a `@TypeOf` or `@ports` operand evaluate in a structural context. The arguments of `@typeInfo` and `@Struct` do too. A pure call is valid there. A graph effect or a mutation of an earlier binding is `S016`, with the existing texts.
- The parser reads the operand of `@TypeOf` and `@ports` as a place. Another form is `S001` at its first token.
- A query charges before its work. It charges 1 for each field, variant, or port that it walks, then the recursive size of its result. Each type carries the size of its term as a fifth metadata number, so no walk measures a type. Each call builds a new result.
- A record type of `@Struct` is structural. Its identity is the ordered list of names and normalized field types. Two equal lists give one type. A declared struct stays nominal.

## Consequences

- The grammar of v0.1 fixes the names. Rust has no `@` form, so it gives no better name.
- One rule of structural contexts covers each query, a family key, and an `as` key. A second rule for the same guarantee does not exist.
- The form of an operand is syntax, so pass 1 finds it. `S003` stays the rule of names.
- The cost model needs no table of query results. A loop that calls `@ports(u)` pays for each call.
- A helper can make one generated type from two places. An identity that depends on a source position does not exist, as decision F7 requires for names.
- The front-end spec records these points in decision rows F30, F31, F32, and F38.
