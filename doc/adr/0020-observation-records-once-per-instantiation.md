# 20. Each instantiation gives its observation records once

- Status: accepted
- Date: 2026-10-12

## Context

The v0.1 builtin `diagnostic(message, value)` appends an observation record during elaboration. v0.1 section 9 asks that a record holds the instance path, so each occurrence of a module replays its records with its own context.

The front end elaborates each `InstantiationId` once ([front-end spec](../design/2026-10-09-frontend.md), section 5.3). A later `instance` statement with the same identity uses the result and charges only the statement. This rule keeps the cost of a shared hierarchy linear. For example, `M(d)` instantiates `M(d - 1)` twice, and `d = 30` gives 31 instantiations.

A replay for each `instance` statement gives 2^30 records for this design. The cost of a shared hierarchy then grows with the number of occurrences, not with the number of identities.

The records also need an output. The `elab` command prints the `.sil` text on stdout, and the harnesses compare this one output.

## Decision

- Each `InstantiationId` gives its records once, when it elaborates. A done instantiation does not replay its records.
- A record names the emitted module name of its instantiation, not an instance path.
- This deviates from v0.1 section 9. The decision row F15 of the front-end spec records the deviation.
- A new command `observe F.si --top T` in both front ends prints the records on stdout, one line for each record, in evaluation order.
- For a rejected design, `observe` prints the records before the first error, then the error line, and exits with code 1.

## Consequences

- The cost of the records stays in the cost model. A shared hierarchy stays linear.
- A user who needs the records of one occurrence finds the instance path from the emitted module name and the design.
- The outputs of `elab` and `build` do not change.
- The source suites compare the `observe` output of both front ends byte for byte. This is the done criterion of slice 2 for the records.
- `doc/trust.md` gets a row for `silicon-check observe`.
