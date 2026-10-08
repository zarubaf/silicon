# Repository Foundation

Status: proposed
Date: 2026-10-08

## 1. Purpose and scope

This spec defines the foundation of the Silicon repository.
It covers the layout, the agent guidance, the orchestration of agents, the task and commit lifecycle, formatting, quality gates, and clutter prevention.

The goal: a fresh agent can do a task with only the root `AGENTS.md`, the `AGENTS.md` of one area, and a task description.
Mechanical checks reject bad formatting, bad commits, broken layering, and unproven Lean before a human reads the change.

Out of scope:

- The Silicon language, the core IR, and their semantics. A separate spec defines them.
- The design of `silicon fmt`, `silicon lint`, and the Silicon LSP. This spec only reserves their place (section 10).
- Human approval gates. Agents have merge authority at the start. A later ADR adds human gates.

## 2. Meta-rule

Guidance is a contract. Tools enforce it.

Each hard rule in the guidance names the check that enforces it.
A rule without a check is advisory.
`xtask` warns about a hard rule without a named check.
Section 12 is the authoritative index of rules and checks.

## 3. Repository layout

```text
silicon/
├── AGENTS.md              # root contract
├── CLAUDE.md              # symlink to AGENTS.md
├── CONTEXT.md             # project vocabulary
├── README.md              # what Silicon is, `just` entry points
├── flake.nix  flake.lock  .envrc
├── justfile               # the only entry point
├── Cargo.toml  Cargo.lock
├── rustfmt.toml  clippy.toml  deny.toml  .config/nextest.toml
├── .mdformat.toml  .vale.ini  .vale/styles/Silicon/
├── taplo.toml  .yamlfmt   # TOML and YAML formatter config
├── .editorconfig  .gitignore  lefthook.yml
├── .cargo/config.toml     # `cargo xtask` alias
├── crates/                # one crate per pipeline stage, created on demand
├── xtask/                 # repository tooling in Rust
├── lean/                  # Lake project, the normative spec
├── doc/
│   ├── architecture.md
│   ├── adr/
│   ├── design/
│   └── guide/
├── tests/corpus/          # designs for validation and differential testing
├── .claude/
│   ├── settings.json
│   └── output-styles/ste.md
├── .codex/config.toml
└── .github/
    ├── workflows/ci.yml
    ├── ISSUE_TEMPLATE/task.yml
    └── pull_request_template.md
```

Rules:

1. The bootstrap creates no empty crates. A crate comes into existence with its first task.
2. `lean/` is at the top level. It is the normative spec, not a part of the compiler.
3. `xtask/` is a binary crate. `cargo xtask <command>` runs it through an alias in `.cargo/config.toml`. It holds every custom check. It never ships.
4. Shell scripts are banned. A `justfile` recipe calls one tool in one line. Logic goes into `xtask`.
5. `ci.yml` runs `just ci` and nothing else. Local runs and CI runs cannot drift apart.

The two existing notes change as follows:

- `doc/hdl-project-handoff.md`: its decisions become ADRs, and its architecture moves into `doc/architecture.md`. The note is then deleted.
- `doc/silicon-ecosystem-design.md`: it moves to `doc/design/2026-10-05-ecosystem.md`. Its invariants (section 11 of the note) become ADRs.

## 4. Guidance hierarchy

| Level | File | Loaded | Limit |
| --- | --- | --- | --- |
| L0 | `AGENTS.md` at the root | Always | 100 lines |
| L1 | `AGENTS.md` in a crate or in `lean/` | When an agent works in that directory | 60 lines |
| L2 | `doc/**` | On demand, through a link from L0 or L1 | None |

Each directory with an `AGENTS.md` also has `CLAUDE.md` as a symlink to it.
Claude Code and Codex thus read one source.

### 4.1 Root `AGENTS.md`

The root file has five parts:

1. The mission in two sentences.
2. The timeless constraints (section 4.3).
3. The hard rules, each with its check (section 12).
4. The workflow in five lines: issue, worktree, `just check`, commit, pull request.
5. A map from questions to `doc/` files.

### 4.2 L1 template

Each L1 file has these headings, in this order:

1. Purpose
2. Owns
3. Invariants
4. Dependencies (allowed and forbidden)
5. How to test

### 4.3 Timeless constraints

The root `AGENTS.md` keeps this text as the owner wrote it. Only the numbering is fixed.

> When two principles collide, pick the one that cuts future cost in THIS codebase.
> HARD RULE: refactor to the principle FIRST, then change behavior.
>
> 1. Separation of Concerns - one kind of work per part (UI / domain / persistence / infra). Root principle.
> 2. Encapsulation / Information Hiding - small stable contract; hide internals.
> 3. High Cohesion + Loose Coupling - change-together lives together; independents talk narrow.
> 4. DRY - one authoritative representation of each piece of *knowledge* (not every similar line). Avoid over-DRY.
> 5. KISS - simplest design that works; complexity is the long-term tax.
> 6. Single Responsibility - one reason to change.
> 7. Depend on Abstractions - policy doesn't depend on details; both depend on contracts.
> 8. YAGNI - no speculative features, frameworks, or "later" hooks.
> 9. Composition over Inheritance - assemble pieces; don't grow fragile hierarchies.
> 10. Open/Closed (with discipline) - extend at stable boundaries; only where change showed up twice.
> 11. Honorable: Law of Demeter • fail fast / illegal states unrepresentable • optimize for deletion.
> 12. Unix do-one-thing + compose.
>
> Treat as constraints. Violate slogans when judgment says so.

## 5. `doc/` content

| Path | Content |
| --- | --- |
| `doc/architecture.md` | The pipeline, the crates and their order, and the trust boundary: what is proven, what is validated, and what is trusted |
| `doc/adr/NNNN-title.md` | One decision each. Headings: Context, Decision, Consequences, Status. An accepted ADR does not change. A new ADR supersedes it. |
| `doc/design/YYYY-MM-DD-topic.md` | Specs that describe something that exists. A spec is deleted when its design is replaced. |
| `doc/guide/agents.md` | Orchestration rules and model choice (section 6) |
| `doc/guide/commits.md` | Commit and branch conventions (section 7) |
| `doc/guide/style.md` | ASD-STE100 writing rules and formatting for each file type (section 8) |
| `doc/guide/testing.md` | The test oracle for each layer |
| `CONTEXT.md` | The glossary. Each term has one definition and `_Avoid_` lines for rejected synonyms. |

The first ADRs come from the two existing notes:

1. Record decisions as ADRs.
2. Lean 4 is the normative spec. Rust is the compiler language.
3. Translation validation instead of a verified compiler.
4. CIRCT is a backend only. LEC closes the trust gap.
5. Synchronous, 2-state semantics only.
6. Lattice resolves packages. Silicon defines their meaning.
7. Mandatory uniquification of emitted names by package identity.
8. Nix flake pins the toolchain.
9. Agents merge after a review by a model from a different vendor.

`xtask` generates the vale vocabulary (accept and reject lists) from `CONTEXT.md`.
Each term thus has one authoritative definition.

### 5.1 Writing style

All prose in Markdown follows ASD-STE100 Simplified Technical English.
The output style `.claude/output-styles/ste.md` is the project default in `.claude/settings.json`.
Agents thus write in this style without a reminder.
`vale` checks the countable rules: sentence length, passive voice, `-ing` forms, noun clusters, and vocabulary.
Code, quotations, and exact strings are exempt.

## 6. Orchestration

The orchestrator is the main Claude Code session on Opus.
It reads issues, splits work, creates worktrees, dispatches subagents, reads their results, and merges.
It does not write product code.
It does not read large file dumps; a search goes to the built-in `Explore` subagent.

The workflow is the Superpowers workflow:

1. `brainstorming`
2. `writing-plans`
3. `subagent-driven-development` in a worktree
4. `finishing-a-development-branch`

The repository defines no custom agent roles at the start.
A role file in `.claude/agents/` comes into existence only when the same need shows up twice.

The repository adds three rules:

1. **Lean goes to Codex.** The orchestrator dispatches all Lean work to the `codex:codex-rescue` subagent with `--fresh`. Each task thus starts a new Codex thread. `.codex/config.toml` pins the Codex model. A change to Astra is a one-line change. Do not use `/codex:transfer` for delegation: it copies the full Claude session, with its chat history, into Codex.
2. **Cross-vendor review before merge.** A Codex adversarial review (`adversarial-review --base main`) must pass on a branch that Claude wrote. It challenges the design, the assumptions, and the tradeoffs. Superpowers' own review covers defects. An Opus review must pass on a branch that Codex wrote. The reviewer gets the diff and the spec, not the reasoning of the author.
3. **Superpowers paths are overridden.** Specs go to `doc/design/`. Plans go to `.scratch/` in the worktree.

Model choice is advisory: Opus for design, proofs, and hard bugs. Sonnet for implementation. Haiku for search.

A subagent gets the task, the root `AGENTS.md`, and the L1 file of its area. It gets no chat history.
A subagent returns a report of 20 lines or fewer: what changed, how it was verified, and open questions.

`.claude/settings.json` pins the plugins through `extraKnownMarketplaces` and `enabledPlugins`.
A fresh clone thus gets Superpowers and the Codex plugin.
The same file disables commit attribution.

## 7. Task and commit lifecycle

1. **Issue.** The issue template has three fields: Goal, Done criteria (mechanical), and Area.
2. **Worktree.** Claude Code creates it at `.claude/worktrees/<branch>`. The branch name is `<type>/<issue>-<slug>`, for example `feat/42-core-ir-memories`.
3. **Work.** Hand-off notes and plans go to `.scratch/`. Git ignores this directory, and it dies with the worktree.
4. **Pull request.** The pull request must pass `just ci` and the cross-vendor review. The merge queue rebase-merges it. History stays linear, and each commit stays separate.
5. **Cleanup.** The worktree and the branch are deleted.

Worktree hygiene:

- `xtask` gets file lists from `git ls-files`. Tools thus never read worktrees, `target/`, or `.lake/`.
- All worktrees share `sccache`. Each worktree has its own `target/`.
- `nix-direnv` caches the development shell.

Commits:

1. The format is Conventional Commits: `type(scope): subject`.
2. The scope is a crate name or one of `lean`, `doc`, `adr`, `ci`, `xtask`.
3. The subject is imperative and has 72 characters or fewer.
4. The body states why and what the change means. It does not list files.
5. One commit holds one logical change.
6. A breaking change uses `!` and a `BREAKING CHANGE:` footer.
7. No AI attribution: no `Co-Authored-By` trailer for an agent, no "Generated with" line.

`cargo xtask commit-check` runs in the `commit-msg` hook and in CI on each commit of a pull request.
It rejects:

1. A `refactor` commit that changes test expectations (`**/snapshots/**`, corpus expectations).
2. A commit that changes `lean/` and `crates/` together.
3. A commit that changes test expectations and non-test code together.
4. A subject that is not a Conventional Commit.
5. An attribution trailer.

`lefthook` runs the git hooks. Nix pins it. `lefthook.yml` calls `just` recipes only.

## 8. Formatting

`just fmt` writes. `just check` verifies. The Nix flake pins every tool.

| Files | Tool | Configuration |
| --- | --- | --- |
| Rust | `rustfmt` | Stable options only |
| Markdown | `mdformat` with GFM and tables plugins | `wrap = "no"` |
| Prose in Markdown | `vale` | Silicon STE style; vocabulary from `CONTEXT.md`; code blocks exempt |
| Lean | Lean style linters, warnings as errors; `xtask` whitespace and line-length check | Lean 4 has no standard formatter. Adopt one when it exists. |
| TOML | `taplo fmt` | |
| Nix | `nixfmt` | RFC style |
| YAML | `yamlfmt` | |
| `justfile` | `just --fmt` | |
| All files | `.editorconfig` | LF, final newline, no trailing whitespace |

Generated output, for example emitted Verilog in `out/`, is not formatted and not committed.
Snapshot files are compiler output. Tests compare them byte for byte.

## 9. Quality gates

`just ci` runs these gates.

Rust:

- `clippy -D warnings`. `[workspace.lints]` holds all lint levels: `pedantic`, and for library crates `unwrap_used`, `expect_used`, `todo`, `dbg_macro`, `print_stdout`.
- `unsafe_code = "forbid"` for the workspace.
- `dead_code` and `unused` at `deny`.
- `cargo-deny` for licenses, advisories, and duplicate crates.
- `cargo-machete` for unused dependencies.
- `cargo nextest` with failure-only output.
- `insta` snapshots with `INSTA_UPDATE=no` in CI.

Lean:

- `lake build` with warnings as errors.
- `xtask` bans `sorry`, new `axiom` declarations, and `native_decide` outside `lean/allowlist.toml`.

Docs:

- `mdformat --check`, `vale`, and `lychee --offline` for internal links.

Repository (`xtask`):

- Crate layering: a crate does not depend on a later pipeline stage.
- Each crate sets `lints.workspace = true`.
- Guidance limits (section 4).
- `AGENTS.md` and `CLAUDE.md` symlink pairs.
- Tree check (section 11).
- `commit-check` (section 7).

Fuzzing, translation validation, and LEC join `just ci` in build step 2, when their oracles exist.

## 10. Silicon tooling

This spec makes four commitments about the Silicon formatter, linter, and LSP:

1. The `syntax` crate uses a lossless syntax tree (`rowan`) from its first commit. A formatter and an LSP need it, and a later change means a rewrite.
2. The names `crates/fmt`, `crates/lint`, and `crates/lsp` are reserved. The language spec designs them.
3. When `silicon fmt` and `silicon lint` exist, Silicon source joins `just fmt` and `just check` through the `xtask` file list. `silicon fmt` formats the test corpus.
4. Silicon lints have names, documentation, and an edition, like `clippy` lints.

## 11. Clutter prevention

`cargo xtask tree-check` rejects:

1. A top-level entry that is not in the layout of section 3.
2. A file that matches `*.sh`, `*.log`, `*.orig`, `*.rej`, `*.bak`, `TODO.md`, `NOTES.md`, or a path under a `superpowers/` directory.
3. A `TODO` or `FIXME` comment without an issue reference in the form `TODO(#123): ...`.

Review rules (the cross-vendor reviewer enforces them):

- A comment explains why. It does not narrate history, for example "changed X to Y".
- No unused abstraction, no fallback layer, no code for later.

Agent context:

- `.claude/settings.json` denies reads of `target/`, `.lake/`, `out/`, `result*`, and `.claude/worktrees/`.
- `just` recipes use quiet flags. `nextest` shows failures only.

## 12. Enforcement index

| Rule | Check |
| --- | --- |
| Refactor first, then change behavior | `commit-check`: `refactor` commits do not change test expectations |
| Spec and implementation change in different commits | `commit-check`: no commit touches `lean/` and `crates/` |
| Test expectations change alone | `commit-check` |
| Conventional Commits, no attribution | `commit-check`, `commit-msg` hook |
| No shell scripts | `tree-check`; `xtask` rejects multi-line `justfile` recipes |
| No stray files | `tree-check` |
| `TODO` needs an issue | `tree-check` |
| Crate layering | `xtask` layering test |
| Workspace lints everywhere | `xtask` |
| Guidance limits and symlink pairs | `xtask` |
| Formatting | `just check` (section 8) |
| STE prose and vocabulary | `vale` |
| No unproven Lean | `lake build` and `xtask` Lean scan |
| Cross-vendor review | Pull request template checkbox and reviewer verdict; advisory until a GitHub check exists |
| Comment and abstraction hygiene | Reviewer; advisory |

## 13. Items to verify during implementation

1. Codex reads `.codex/config.toml` at project level. If it does not, the model pin moves to a single entry in `doc/guide/agents.md`.
2. Nix packages for CIRCT, Lean (through `elan` or a pinned toolchain), `vale`, and `mdformat` with its plugins. Write an overlay where a package is missing.
3. The coverage of STE rules by `vale`. Rules that `vale` cannot check stay in the output style only.
4. The orchestrator can start the adversarial review. The slash command sets `disable-model-invocation`, so the orchestrator calls `codex-companion.mjs adversarial-review` directly. Its path is in the versioned plugin cache. Find a stable way to call it, for example a `just review` recipe.
5. `.claude/settings.json` supports `extraKnownMarketplaces`, `enabledPlugins`, and the attribution setting at project level.
