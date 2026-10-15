# Silicon

Silicon is a hardware description language with synchronous, 2-state semantics. Lean 4 holds the normative spec, Rust holds the compiler, and translation validation closes the trust gap.

## Constraints

<!-- vale off -->

When two principles collide, pick the one that cuts future cost in THIS codebase. HARD RULE: refactor to the principle FIRST, then change behavior.

01. Separation of Concerns - one kind of work per part (UI / domain / persistence / infra). Root principle.
02. Encapsulation / Information Hiding - small stable contract; hide internals.
03. High Cohesion + Loose Coupling - change-together lives together; independents talk narrow.
04. DRY - one authoritative representation of each piece of *knowledge* (not every similar line). Avoid over-DRY.
05. KISS - simplest design that works; complexity is the long-term tax.
06. Single Responsibility - one reason to change.
07. Depend on Abstractions - policy doesn't depend on details; both depend on contracts.
08. YAGNI - no speculative features, frameworks, or "later" hooks.
09. Composition over Inheritance - assemble pieces; don't grow fragile hierarchies.
10. Open/Closed (with discipline) - extend at stable boundaries; only where change showed up twice.
11. Honorable: Law of Demeter • fail fast / illegal states unrepresentable • optimize for deletion.
12. Unix do-one-thing + compose.

Treat as constraints. Violate slogans when judgment says so.

<!-- vale on -->

## Hard rules

Each rule is one list line. It ends with `Check:` and the check. A rule without a check is advisory.

- Refactor first, then change behavior. A `refactor` commit does not change test expectations. Check: `cargo xtask commit-check`.
- Spec and implementation change in different commits. No commit touches `lean/` and `crates/` together. Check: `cargo xtask commit-check`.
- Test expectations change alone, never with non-test code. Check: `cargo xtask commit-check`.
- Commits use Conventional Commits and carry no AI attribution. Check: `cargo xtask commit-check`.
- Write no shell scripts. A `justfile` recipe runs one command. Check: `cargo xtask check` (rules `tree-banned`, `tree-justfile`).
- Add no stray files or top-level entries. Check: `cargo xtask check` (rules `tree-root`, `tree-banned`).
- Every `TODO` or `FIXME` needs an issue reference, for example `TODO(#123)`. Check: `cargo xtask check` (rule `tree-todo`).
- Start each Rust and Lean source file with the SPDX line `Apache-2.0`. Check: `cargo xtask check` (rule `tree-spdx`).
- Keep the guidance limits: 100 lines at the root, 60 lines per L1 file. Pair each `AGENTS.md` with a `CLAUDE.md` symlink. Check: `cargo xtask check` (rules `guidance-limit`, `guidance-pair`, `guidance-headings`).
- A new crate joins `[workspace] members` and `[workspace.metadata.layers] order`. Check: `cargo xtask check` (rules `workspace-member`, `workspace-layers`).
- A crate depends only on earlier pipeline stages. Check: `cargo xtask check` (rule `workspace-layers`).
- Every crate sets `[lints] workspace = true`. Check: `cargo xtask check` (rule `workspace-lints`).
- A crate of `[workspace.metadata.layers] dev-only` is never a normal or build dependency. Only `xtask` and `[dev-dependencies]` name it. Check: `cargo xtask check` (rule `workspace-dev-only`).
- Keep the non-test code of `elab` in the Rust subset of design section 4.5 of the front end: no `Cell`, `RefCell`, `OnceCell`, `LazyCell`, `UnsafeCell`, `Rc`, `Arc`, `Weak`, `Mutex`, `RwLock`, `OnceLock`, `LazyLock`, an `Atomic` type, `thread_local!`, `std::thread`, `dyn`, `unsafe`, `static mut`, `HashMap`, `HashSet`, or `FnMut`. Check: `cargo xtask check` (rule `elab-subset`).
- Format all files with the pinned tools. Check: `just check`.
- Write Markdown prose in ASD-STE100. Check: `vale`.
- Keep the error codes of the spec, Lean, and Rust equal. The Rust front end can lack the codes of later slices that `LATER` in `xtask/src/arch.rs` lists. Check: `cargo xtask check` (rule `arch-codes`).
- Name each workspace crate and each `silicon-check` command in backticks in the Part column of a row of `doc/trust.md`. The crate `xtask` is exempt. Check: `cargo xtask check` (rule `arch-trust`).
- Cover each Lean module under `lean/Silicon/Core/` and `lean/Silicon/Source/` by an architecture path in `doc/architecture.md`, or list it as non-normative in `xtask/src/arch.rs`. Check: `cargo xtask check` (rule `arch-paths`).
- Keep proof modules out of the imports of `silicon-check`. Check: `cargo xtask check` (rule `lean-exe-imports`).
- Keep the front end out of the imports of the Lean core: no `Core` module imports a `Source` module. Check: `cargo xtask check` (rule `lean-core-imports`).
- Leave no unproven Lean: no `sorry`, no new `axiom`, no `native_decide` outside the allowlist. Check: `lake build` and the xtask Lean scan.

## Workflow

1. Issue: state the goal, the mechanical done criteria, and the area. GitHub tracks all work: put each issue in a milestone, give it `C-` and `A-` labels, and split a large outcome into sub-issues.
2. Worktree: work on `<type>/<issue>-<slug>` in `.claude/worktrees/`. `.scratch/` holds only temporary notes and plans, never the status of the work.
3. Verify: run `just check` before each commit. Run `just ci` before the pull request.
4. Commit: one logical change per commit, in the format `type(scope): subject`.
5. Pull request: it must pass `just ci`. The workflow also requires the cross-vendor review. Then rebase-merge.

- Lean work goes to a fresh Opus subagent, one bounded task at a time.
- No check enforces the cross-vendor review yet. Run it with `just review`. A Codex review covers Claude branches. An Opus review covers Codex branches.
- Run an architecture review on each pull request that touches an architecture path, after 15 merges or one week, and at each milestone. Use `just review-scope`, `just review-due`, and `just arch-summary`. See ADR 0013.
- A comment explains why. It never narrates history. Add no unused abstraction and no fallback layer.
- A subagent gets the task, this file, and the L1 file of its area. It returns a report of 20 lines or fewer.

## Where to read

| Question                                  | Read                   |
| ----------------------------------------- | ---------------------- |
| What is the pipeline?                     | `doc/architecture.md`  |
| What is proven, validated, or trusted?    | `doc/trust.md`         |
| Why did we decide this?                   | `doc/adr/`             |
| How does this part work?                  | `doc/design/`          |
| How do I orchestrate agents? Which model? | `doc/guide/agents.md`  |
| How do I write commits and branches?      | `doc/guide/commits.md` |
| How do I write prose and format files?    | `doc/guide/style.md`   |
| What is the test oracle for a layer?      | `doc/guide/testing.md` |
| What does a term mean?                    | `CONTEXT.md`           |
