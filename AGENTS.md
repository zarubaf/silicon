# Silicon

Silicon is a hardware description language with synchronous, 2-state semantics.
Lean 4 holds the normative spec, Rust holds the compiler, and translation validation closes the trust gap.

## Constraints

When two principles collide, pick the one that cuts future cost in THIS codebase.
HARD RULE: refactor to the principle FIRST, then change behavior.

1. Separation of Concerns - one kind of work per part (UI / domain / persistence / infra). Root principle.
2. Encapsulation / Information Hiding - small stable contract; hide internals.
3. High Cohesion + Loose Coupling - change-together lives together; independents talk narrow.
4. DRY - one authoritative representation of each piece of *knowledge* (not every similar line). Avoid over-DRY.
5. KISS - simplest design that works; complexity is the long-term tax.
6. Single Responsibility - one reason to change.
7. Depend on Abstractions - policy doesn't depend on details; both depend on contracts.
8. YAGNI - no speculative features, frameworks, or "later" hooks.
9. Composition over Inheritance - assemble pieces; don't grow fragile hierarchies.
10. Open/Closed (with discipline) - extend at stable boundaries; only where change showed up twice.
11. Honorable: Law of Demeter • fail fast / illegal states unrepresentable • optimize for deletion.
12. Unix do-one-thing + compose.

Treat as constraints. Violate slogans when judgment says so.

## Hard rules

Each rule names its check. A rule without a check is advisory.

- Refactor first, then change behavior. A `refactor` commit does not change test expectations. Check: `cargo xtask commit-check`.
- Spec and implementation change in different commits. No commit touches `lean/` and `crates/` together. Check: `cargo xtask commit-check`.
- Test expectations change alone, never with non-test code. Check: `cargo xtask commit-check`.
- Commits use Conventional Commits and carry no AI attribution. Check: `cargo xtask commit-check`.
- Write no shell scripts. A `justfile` recipe runs one command. Check: `cargo xtask check` (rules `tree-banned`, `tree-justfile`).
- Add no stray files or top-level entries. Check: `cargo xtask check` (rules `tree-root`, `tree-banned`).
- Every task marker needs an issue reference, for example `TODO(#123)`. Check: `cargo xtask check` (rule `tree-todo`).
- Keep the guidance limits: 100 lines at the root, 60 lines per L1 file. Pair each `AGENTS.md` with a `CLAUDE.md` symlink. Check: `cargo xtask check` (rules `guidance-limit`, `guidance-pair`, `guidance-headings`).
- Format all files with the pinned tools. Check: `just check`.
- Write Markdown prose in ASD-STE100. Check: `vale`.
- Leave no unproven Lean: no `sorry`, no new `axiom`, no `native_decide` outside the allowlist. Check: `lake build` and the xtask Lean scan.

## Workflow

1. Issue: state the goal, the mechanical done criteria, and the area.
2. Worktree: work on `<type>/<issue>-<slug>` in `.claude/worktrees/`. Put notes and plans in `.scratch/`.
3. Verify: run `just check` before each commit. Run `just ci` before the pull request.
4. Commit: one logical change per commit, in the format `type(scope): subject`.
5. Pull request: it must pass `just ci` and the cross-vendor review. Then rebase-merge.

- Lean work goes to the `codex:codex-rescue` subagent with `--fresh`.
- Cross-vendor review is advisory until a GitHub check exists. Run it with `just review`. A Codex review covers Claude branches. An Opus review covers Codex branches.
- A comment explains why. It never narrates history. Add no unused abstraction and no fallback layer.
- A subagent gets the task, this file, and the L1 file of its area. It returns a report of 20 lines or fewer.

## Where to read

| Question | Read |
| --- | --- |
| What is the pipeline, and what is trusted? | `doc/architecture.md` |
| Why did we decide this? | `doc/adr/` |
| How does this part work? | `doc/design/` |
| How do I orchestrate agents? Which model? | `doc/guide/agents.md` |
| How do I write commits and branches? | `doc/guide/commits.md` |
| How do I write prose and format files? | `doc/guide/style.md` |
| What is the test oracle for a layer? | `doc/guide/testing.md` |
| What does a term mean? | `CONTEXT.md` |
