# 7. Mandatory uniquification of emitted names by package identity

- Status: accepted
- Date: 2026-10-08

## Context

A design can use two versions of one package. For example, a DMA uses `axi@1.8` and a GPU uses `axi@2.3`. HDL tools have one global namespace for module names. Different package labels alone do not keep the two versions apart. [The ecosystem design](../design/2026-10-05-ecosystem.md), section 5, gives the full rules.

## Decision

Silicon does a mandatory uniquification step. It puts the package and version identity, or a deterministic identity from a SHA digest, into each emitted module name.

The recommended default is a readable package and version prefix, and a suffix from a SHA-256 identity digest. This default is not a part of the decision.

The ecosystem design raises these invariants (section 11, items 2 to 4):

1. Different package versions keep different identities through the full pipeline.
2. Shared HDL namespaces get deterministic, collision-checked emitted names.
3. RTL, formal artifacts, and debug tools share an explicit name map.

## Consequences

- The same identity gives the same emitted name on each machine and with each build backend.
- Uniquification rewrites resolved symbols or the IR. A text search and replace is not sufficient.
- Constraints, waveform tools, testbenches, and hierarchical references use the name map.
- Uniquification does not make two versions compatible. An incompatible interface still needs an adapter or a diagnostic.
- The exact grammar of the emitted name and the digest length are still open.
