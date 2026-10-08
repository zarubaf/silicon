# Style

This guide gives the writing rules for prose and the formatter for each file type. [The foundation spec](../design/2026-10-08-repo-foundation.md), sections 5.1 and 8, is the source.

## Prose

All prose in Markdown follows ASD-STE100 Simplified Technical English (STE). The output style [`.claude/output-styles/ste.md`](../../.claude/output-styles/ste.md) holds the full rules. `.claude/settings.json` makes it the project default. Agents thus write in this style without a reminder.

Code, commands, quotations, and exact strings are exempt. Text that must stay verbatim goes between `<!-- vale off -->` and `<!-- vale on -->`.

Use the terms of [`CONTEXT.md`](../../CONTEXT.md) with their exact meaning. Do not use a synonym from an `_Avoid_` line.

## Mechanical rules

`just prose` runs `cargo xtask prose`. It regenerates the vale vocabulary from `CONTEXT.md`, then runs `vale` and `lychee` over the tracked Markdown. `vale` checks these STE rules:

| Rule                          | vale rule                  | Level   |
| ----------------------------- | -------------------------- | ------- |
| At most 25 words per sentence | `Silicon.SentenceLength`   | Error   |
| No hedge stacking             | `Silicon.HedgeStacking`    | Error   |
| No ellipsis                   | `Silicon.NoEllipsis`       | Error   |
| Glossary vocabulary           | `Vale.Terms`, `Vale.Avoid` | Error   |
| Active voice                  | `Silicon.Passive`          | Warning |

`.vale.ini` sets `MinAlertLevel = warning`. Warnings show, but only errors fail the check. `Vale.Spelling` is off. `CONTEXT.md` is exempt from `Vale.Avoid`, because it names the rejected synonyms.

`lychee --offline` checks the internal links. A link to a missing file fails the check.

## Output-style rules

No check enforces these STE rules. They stay in the output style only:

- Use at most 3 nouns in a row.
- Put the main clause first.
- Use at most 20 words in an instruction.
- Write one instruction per sentence.
- Use simple tenses.
- Use an `-ing` word only as a noun or in a technical term.
- Use one term for one concept.
- Choose the plainest word.
- Define an uncommon term at its first use.
- Use at most 6 sentences in a paragraph.
- Use a vertical list for 3 or more items.

## Formatting

`just fmt` writes. `just check` verifies. The Nix flake pins every tool.

| Files             | Tool                                                                             | Configuration                                                       |
| ----------------- | -------------------------------------------------------------------------------- | ------------------------------------------------------------------- |
| Rust              | `rustfmt`                                                                        | Stable options only                                                 |
| Markdown          | `mdformat` with GFM, tables, and front-matter plugins                            | `wrap = "no"`                                                       |
| Prose in Markdown | `vale`                                                                           | Silicon STE style; vocabulary from `CONTEXT.md`; code blocks exempt |
| Lean              | Lean style linters, warnings as errors; `xtask` whitespace and line-length check | Lean 4 has no standard formatter. Adopt one when it exists.         |
| TOML              | `taplo fmt`                                                                      |                                                                     |
| Nix               | `nixfmt`                                                                         | RFC style                                                           |
| YAML              | `yamlfmt`                                                                        |                                                                     |
| `justfile`        | `just --fmt`                                                                     |                                                                     |
| All files         | `.editorconfig`                                                                  | LF, final newline, no trailing whitespace                           |

`mdformat` joins the lines of a paragraph into one line. Write each line with a separate meaning as a list item. Write metadata, for example the status and the date, as a list with two items.

Generated output, for example emitted Verilog in `out/`, is not formatted and not committed. Snapshot files are compiler output. Tests compare them byte for byte.
