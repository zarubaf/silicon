# 32. The source generator reflects only its drawn types

- Status: accepted
- Date: 2026-10-26

## Context

[ADR 0018](0018-source-generator-crate.md) limits the static evaluator of the source generator. Its last rule says:

<!-- vale off -->

> It does not resolve names, infer or check types, compute `cost` or fuel, make instantiation identities or emitted names, or lower to core IR.

<!-- vale on -->

Its rule for slice 2 lists the static values that the evaluator can model: aggregates, `List`, strings, and the width of `data_bits(T)`.

Issue #397 (part 2 of #348) adds the queries `@TypeOf`, `@typeInfo`, `@Struct`, and `@ports` to the typed mode. A query that maps a drawn type to a scalar, for example `.width`, `.length`, or `.kind`, is in the limits of ADR 0018, as `data_bits(T)` is. Three needs go past these limits:

- **Values that hold a type.** `let ps = @ports(u)`, `@field(ps[i], "ty")`, a `list` of `FieldInfo` with `push`, and `@Struct(@typeInfo(S).fields)` hold a `Type` in a static value. The evaluator has no such value.
- **The identity of `@Struct`.** Two equal lists of names and normalized field types give one generated record type (section 9.3 of the front-end spec, F38). This is a type equality.
- **The type of a value with no declared type.** `@TypeOf(x)` of a local without a declared type gives the type of its value (section 9.3).

These needs change the trust boundary of the oracle (`doc/trust.md`, row 55). The user accepted this ADR on 2026-10-26 (option A of the plan of #348).

## Decision

- The evaluator gets one opaque value: a type token. A token holds a type `STy` that the builder drew. The evaluator can store a token, copy it, and give it back. It does not look into a token.
- Each query result comes from the types that the builder drew for its own bindings, ports, resources, records, enums, and children. The generator has no function from an expression to a type. Thus it reflects only, and it infers no type.
- The identity of a `@Struct` type comes from the record of the builder draw. The builder knows which lists it drew, so it knows which lists are equal. The generator has no normalizer of types.
- The port layout of a child for `@ports` comes from the same plan function that gives `Program::ports()`. The generator has one rule for the port layout, not two.
- The twin writes each query as its static result, as section 11.4 of the front-end spec says. The twin has no `@` builtin and no type token.
- This ADR replaces two points of ADR 0018. The words "infer or check types" no longer forbid the reflection of a drawn type. The list of static values of the slice 2 rule gets the type token. The other rules of ADR 0018 stay, also its layer rule and its other limits.
- A need outside these limits needs a new ADR.

The reflection stays an oracle that is independent of both front ends:

- The generator does not use the code of `parse`, `resolve`, `typeck`, or `elab`. The rule `workspace-layers` keeps this.
- The builder chooses each type first, then writes the program from it. A front end reads the program and computes the type. Thus the two directions are different implementations.
- Both front ends and the generator come from one prose, section 9.3. A misreading of this prose can occur in all three. Known risks are the `width` of an enum and the `domain` of a combinational child.

The generator keeps these guards against a shared misreading:

- The unit tests of the reflection come from the text of section 9.3. Each case cites one sentence of it. They do not come from the run files that Lean makes, because such a file can hold the misreading of Lean.
- A test pairs `@TypeOf` in a type position with an output of `data_bits(@TypeOf(x))`. Thus a wrong type gives a wrong output, not only a wrong text.
- A failure of the typed mode goes to a human first. Nobody changes the generator to agree with the front ends before a person reads the prose.

## Consequences

- The typed mode can draw all five builtins, the type positions, and the forwarding wrappers of `@ports`.
- The generator gets a second rule for the 9.3 metadata of a type. A change of section 9.3 must change the generator too, or `just diff-si` fails.
- No generated record type is a module argument, and no `diagnostic` holds a type. These limits of section 11.4 stay.
- `doc/trust.md` row 55 names this ADR and the reflection in its oracle and its gap.
- Section 11.4 of the front-end spec gets a paragraph for slice 4b in pull request 2 of #348. It names this ADR.
