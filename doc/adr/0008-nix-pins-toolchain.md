# 8. A Nix flake pins the toolchain

- Status: accepted
- Date: 2026-10-08

## Context

Silicon uses Rust, Lean, CIRCT, Verilator, Yosys, and many formatters and linters. Local runs, CI runs, and agent runs must use the same tool versions. The initial design notes (not in the repository) name a Nix flake or a devcontainer.

## Decision

- A Nix flake pins every tool. `flake.lock` records the exact inputs.
- `nix-direnv` loads and caches the development shell through `.envrc`.
- Each tool runs inside the development shell.
- The project uses no Bazel for now. Revisit this choice only if builds stay slow with caching.

## Consequences

- `just ci` gives the same result locally and in CI.
- A fresh clone needs Nix and `direnv allow`.
- An agent sandbox must inherit the development shell. [The agents guide](../guide/agents.md) gives the rules for Codex.
- The flake does not pin CIRCT, Verilator, and Yosys yet. No task uses them yet.
