# 31. Builtin arguments have their own guard kind, and a builtin can be a type

- Status: accepted
- Date: 2026-10-25

## Context

[ADR 0028](0028-builtins-are-a-closed-set-of-static-queries.md) says that the arguments of `@typeInfo` and `@Struct` evaluate in a structural context. It says that a graph effect or a mutation of an earlier binding there is `S016`, with the existing texts. These texts say "a type or a constant", so they do not tell the user where the effect is. [ADR 0030](0030-query-keys-have-their-own-effect-texts.md) gave the keys of a query operand the guard kind `query`, with texts of their own. It did not cover the arguments.

Issue #345 asked three more questions:

- **G1.** Can a builtin stand in a type position, for example `let y: @TypeOf(x) = x;` or `type R = @Struct(fs);`? The grammar of v0.1 allows it. Until #345, it is `S004`.
- **G2.** Which `S016` texts does an argument of `@typeInfo` or `@Struct` get?
- **G3.** Is the argument of `@typeInfo` or `@Struct` a static position for `S005` in pass 4?

The user accepted the recommended option of each question on 2026-10-25.

## Decision

- **G1.** Each builtin can stand in a type position. There, the builtin evaluates as an expression in the structural context of the type. A value that is not a `Type` is `S010`.
- **G2.** The argument of `@typeInfo` and of `@Struct` evaluates under the new guard kind `arg`. The kind `arg` is a structural context. Only its texts are new: "Mutation in a builtin argument" and "Graph effect in a builtin argument". Each text names the builtin. This extends ADR 0030 from the keys of a query to the arguments of a builtin.
- **G3.** The argument of `@typeInfo` and of `@Struct` is not a static position in pass 4. Thus a register in the argument is the `S010` of pass 5, whose text tells the user to use `@TypeOf`. It is not `S005`. A key of a query operand inside the argument keeps its own rules.
- `@typeInfo` lands first, in the first pull request of #345. `@Struct` and the type position land in the second pull request. Until then, they stay `S004`.

## Consequences

- An `S016` in a builtin argument tells the user which builtin holds the argument, and how to move the effect out of it.
- The rule of structural contexts stays one rule. The new kind adds two texts and one check: a node of the argument with a hardware value is `S011` "Value not static" at that node. A place that is the whole argument reads no value, so it keeps the `S010` of G3. Each key in it gets the check. The first `S011` or `S016` in the order of evaluation comes before the `S010` of the argument.
- `@typeInfo(r)` of a register `r` gives a fix that names `@TypeOf`, not the general text of a static position.
- A type position takes the same builtins as an expression, so a user does not bind a type with `const` first. The proof of `parse_print` must cover a builtin in a type.
- The front-end spec records these points in decision row F31 and in sections 6.1, 6.2, 9.2, 9.3, and 9.4.
