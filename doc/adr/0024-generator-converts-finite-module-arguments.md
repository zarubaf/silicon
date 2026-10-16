# 24. The source generator converts finite module arguments

- Status: accepted
- Date: 2026-10-16

## Context

[ADR 0023](0023-generator-predicts-observe-records.md) lets the generator predict the emitted name of the argument tuples that its builder emits. These are integers, Booleans, and function values. It says that no other identity belongs to the generator.

Issue #244 asks for module parameters of type `UInt[N]` and `SInt[N]`. Issue #188 decided that an argument converts to its parameter type first. Thus `C(1)` and `C(UInt[8](1))` give one identity and one emitted name. The generator cannot predict this without the conversion.

## Decision

- The generator converts each module argument of a finite type to its parameter type. It does this before it predicts an identity or an emitted name.
- The builder and the walk of the records use one equality of converted values. The generator adds no second identity rule.
- The emitted name of a finite value uses the token of its integer value, as section 7.1 of the front-end spec says.
- The conversion checks only that an integer fits the width. No other type check belongs to the generator.
- A need outside these limits needs a new ADR.

## Consequences

- The oracle of the `observe` records covers finite parameters and both spellings of an argument.
- A change of the conversion rule in section 5.3 or 7.1 must change the generator too, or `just diff-si` fails.
