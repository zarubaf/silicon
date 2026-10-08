# Silicon Ecosystem Design

- Status: proposed architecture
- Date: 2026-10-05

## 1. Purpose

This document defines a modular ecosystem for Silicon. The ecosystem supports these properties:

- Reusable, versioned hardware packages.
- Incremental compilation.
- Reproducible builds.
- Lean proofs.
- Controlled evolution of the language.

Bazel is one possible build backend. It is not necessary.

The core split of responsibility is:

> Lattice resolves package identities. Silicon defines their meaning. A build backend executes the required actions. Lean checks formal claims over explicitly identified semantics.

This document records architecture decisions and proposed contracts. The manifest syntax, the artifact formats, the CLI commands, and the emitted names below are examples. A statement is a requirement only when the text says so.

## 2. Goals and boundaries

Goals:

- Keep package resolution, language semantics, build execution, and proof checks separate.
- Support more than one version of the same package and module in one design.
- Require deterministic module uniquification when the compiler lowers modules into a shared HDL namespace.
- Make compiler incrementality useful with a native builder and with external build systems.
- Tie proofs to exact semantic inputs and package dependencies.
- Let each package adopt a new language edition independently.
- Make breaking changes explicit, migratable, and verifiable.

The first version of the ecosystem does not need these items:

- A general-purpose replacement for Bazel.
- A universal simulator abstraction.
- An automatic proof of each compiler transformation.

## 3. Components and ownership

| Component            | Owns                                                                                                                              | Consumes or exposes                                                                                                   |
| -------------------- | --------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------- |
| Silicon              | Syntax, types, elaboration, language semantics, diagnostics, incremental queries, compiler artifacts, migration edits             | Consumes explicit dependency interfaces and identities. Exposes interfaces, semantic IR, RTL, source maps, name maps. |
| Lattice              | Package manifests, dependency constraints, resolution, lockfiles, workspaces, registry metadata, publication, workspace migration | Produces an exact resolved package graph                                                                              |
| Build planning layer | Targets for any backend, actions, artifacts, toolchain requirements, dependency edges                                             | Combines package metadata, compiler contracts, and tool integration rules                                             |
| Build backend        | Materialization, action execution, scheduling, caching, sandboxes, tool calls                                                     | Executes a plan through a native builder, a Bazel adapter, or another integration                                     |
| Lean integration     | Semantic encoding, construction of proof targets, map of Lean dependencies                                                        | Connects Silicon artifacts to explicit Lean modules and proof inputs                                                  |
| Lean                 | Elaboration and kernel checks of theorem declarations                                                                             | Checks claims in a pinned Lean environment                                                                            |

Behavior that is specific to one tool belongs in build rules, adapters, and toolchains. Lattice can expose convenient build commands. The dispatch of these commands must not make dependency resolution depend on a specific execution engine.

Silicon must not fetch packages or resolve version constraints during compilation. The compiler receives a resolved dependency map. Lean must not select versions of Silicon packages independently.

## 4. Package resolution and identity

Lattice separates the package manager from the build system. The Cargo integration model shows this separation:

1. A manifest declares the package requirements.
2. A resolver produces an exact dependency universe.
3. A lockfile records that universe.
4. Build integrations consume the universe and do not resolve it again.

The proposed file names are `lattice.toml` and `lattice.lock`.

```toml
[package]
name = "cpu"
version = "4.2.0"
silicon-edition = "2030"
minimum-silicon-version = "1.12"

[dependencies]
axi = "^2.3"
fifo = "~1.7"
```

An immutable package identity contains these items:

```text
PackageId = (name, version, canonical source identity, source content digest)
```

The lockfile records the exact package identities, the dependency edges, and the source integrity information. A name and a version alone are not sufficient. Different sources or changed content can use the same version string.

An editable workspace package can keep its declared identity while its content changes. Build inputs and proof inputs must then also include the current source digest. A mutable development directory cannot replace an immutable published identity.

Toolchain pins and build configuration can live outside the package lockfile. The package lockfile and the build inputs together must identify each item that can change the result. These items include:

- The compiler version and the Lean version.
- The version of the semantic model.
- Features, parameters, and defines.
- The target configuration.
- The relevant external tools.

## 5. Multiple versions and mandatory uniquification

Multiple dependency versions are first-class. For example, a SoC uses a DMA that depends on `axi@1.8` and a GPU that depends on `axi@2.3`. Both versions must stay distinct through resolution, elaboration, RTL generation, and formal verification.

**Silicon must do a uniquification step. This step puts the package and version identity, or a deterministic identity from a SHA digest, into the emitted module names.** Different package labels or build labels alone do not support multiple versions.

[ADR 0007](../adr/0007-mandatory-uniquification.md) records this decision.

### 5.1 Logical names and emitted names

Source code uses logical module names. The compiler resolves them through the exact dependency graph of the importing package. The output uses globally unique names that are valid in the HDL namespace of the destination.

Example maps:

| Resolved logical module          | Emitted module name                                     |
| -------------------------------- | ------------------------------------------------------- |
| `axi@1.8.0::fifo`                | `axi__v1_8_0__h<identity_digest>__fifo`                 |
| `axi@2.3.1::fifo`                | `axi__v2_3_1__h<identity_digest>__fifo`                 |
| Same version from another source | Same readable version prefix, different identity digest |

A version is a useful readable part of a name. A name from the version only cannot tell all legal package identities apart. The recommended default is a readable package and version prefix, and a suffix from a SHA-256 identity digest.

### 5.2 Identity inputs

The design uses three identities:

```text
PackageId       = exact source package identity
ModuleId        = (PackageId, qualified declaration path)
InstantiationId = (ModuleId, canonical elaboration inputs)
```

An emitted module for a specialized instantiation must include each input that changes its meaning. These inputs are the relevant parameters, the features, and the resolved dependency bindings. The uniquification algorithm has a version. It uses a specified canonical serialization. It does not use host paths, timestamps, or the order of the dependency traversal.

### 5.3 Required behavior

Uniquification must:

- Occur before modules enter a shared elaboration namespace or a shared emitted HDL namespace.
- Apply the map to declarations and to all references. References include instantiations, generated wrappers, binds, and helper modules from the compiler.
- Cover other emitted items with global names where necessary, for example HDL packages, interfaces, and types.
- Rewrite through resolved symbols or through an AST or IR transformation. A text search and replace is not sufficient.
- Make names that are valid for the target language and the toolchain.
- Reserve a namespace for generated names. Detect collisions with user identifiers and foreign identifiers.
- Give the same emitted name for the same identity on each machine and with each build backend.
- Keep a machine-readable name map. The name map links source names, full identities, emitted names, and source locations.

A tool can have a limit on identifier length, and the compiler can then shorten the digest. In this case, compare the full identities and detect collisions before the downstream tools run. The collision handling must be deterministic. Never merge modules silently. Never make a name depend on the order of discovery.

### 5.4 External HDL and integration boundaries

Isolation or uniquification must also cover imported HDL when multiple versions share global names. An adapter can use a transformation that understands the HDL syntax. It can also use a proven library isolation mechanism of the tool. A wrapper alone does not resolve a collision between two inner definitions with the name `fifo`.

Foreign IP that the compiler cannot rename safely needs an explicit integration restriction or a supported isolation mechanism. Diagnose this limit before the downstream elaboration.

A top-level wrapper can keep an external module name that the user selects. Its internal implementation then uses unique names. Constraints, waveform tools, testbenches, and hierarchical references must use the generated name map or an explicit stable integration interface.

Uniquification solves identity collisions and name collisions. It does not make two versions compatible in their protocol. A connection between incompatible interfaces still needs an adapter or a diagnostic.

### 5.5 Lean identity

Lean module paths and namespaces must also tell package identities and module identities apart. The formal integration derives these names from the same identity map, with an encoding that is valid for Lean. RTL names and Lean names can differ in their text. Their correspondence must be explicit.

## 6. Build model for any backend

The build graph must be derivable without Bazel. Package semantics and compiler artifacts must not use Bazel labels or Bazel repository names in their definition.

The planning interface describes these elements:

| Element         | Required information                                                 |
| --------------- | -------------------------------------------------------------------- |
| Target          | Identity, requested facet, configuration                             |
| Artifact        | Producer, format or schema, content identity                         |
| Action          | Toolchain, declared inputs, outputs, arguments, relevant environment |
| Dependency edge | Required artifact or action order                                    |
| Toolchain       | Exact implementation and configuration                               |
| Proof target    | Semantic inputs, proof sources, Lean environment, assumptions        |

Possible package facets are interface, RTL, simulation, synthesis, semantic model, and proofs. A build makes only the requested facets and their dependencies.

At first, a native builder handles these tasks:

- Silicon compilation.
- A local cache.
- Parallel execution.
- Lean actions.
- A limited set of external tool integrations.

Bazel stays valuable for heterogeneous projects, hermetic execution, remote caches, and larger build environments.

Convenience commands can dispatch through a configured backend:

```sh
lattice build
lattice test
lattice prove
```

These commands are a proposal for the user interface. They do not require that Lattice itself schedules actions or discovers tools. Native builds and Bazel builds must consume the same resolved identities and semantic contracts.

## 7. Incremental compilation and artifacts

Incrementality that knows the language belongs in Silicon. The compiler tracks these steps:

- Parsing.
- Name resolution.
- Type inference and width inference.
- Elaboration.
- Interfaces.
- Generation of the semantic model.

The build backend tracks action dependencies and cached outputs.

Silicon exposes deterministic, versioned artifacts for these items:

- Exported interfaces and signatures.
- Elaborated or normalized semantic IR.
- Generated RTL.
- Formal model inputs.
- Source maps and uniquification maps.

Different consumers need different fingerprints. An interface hash lets downstream type checks reuse work after a change to a private implementation. Synthesis and proofs about that implementation must still depend on the changed semantic artifact.

**An unchanged interface is not evidence that the hardware behavior or the correctness proofs stay unchanged.** A downstream proof that uses a contract can reuse a stable contract only after the changed implementation discharges its obligations against that contract.

Persistent incremental state is an optimization. A clean build with the same declared inputs must produce equivalent artifacts. External backends must be able to cache stable artifacts without a dependency on undeclared mutable compiler state.

## 8. Formal integration and provenance

A Silicon package can publish reusable formal interfaces and proofs together with its implementation. Proof dependencies follow the exact resolved package graph.

A proof target records at least these items:

```text
package and module identities
resolved dependency identities
source and semantic artifact digests
edition and language-semantics identity
semantic encoding/schema version
elaboration configuration
compiler and model-generator identities
proof sources and dependency artifacts
Lean toolchain and library identities
theorem statement and relevant assumptions
```

Each Lean dependency must also have a pin. Lake metadata can supply this dependency universe. The selected backend then constructs explicit Lean compilation actions. Package resolution and build execution stay separate in both arrangements.

Prefer visible Lean module dependencies to a single opaque build action where practical. The cache key of a proof artifact must contain its actual inputs, including the Lean environment and the semantic model.

A Lean check shows that a theorem follows in the encoded model under its assumptions. It does not show that RTL generation, model generation, synthesis, or physical implementation keeps that model. The project must name each of these bridges as a trusted component, or support it with explicit validation or proofs.

Formal model generation is a facet of the elaborated Silicon semantics. It does not have to occur after simulation or synthesis. The backend executes actions in the order of their actual dependencies.

## 9. Language evolution

Keep these concepts distinct:

| Version axis               | Purpose                                                        |
| -------------------------- | -------------------------------------------------------------- |
| Compiler version           | Implementation, optimizations, diagnostics, fixes              |
| Edition                    | Source interpretation and compatibility rules for each package |
| Package version            | Published library API and behavior                             |
| Minimum compiler version   | Features that the compilation of the package needs             |
| Language-semantics version | Meaning of hardware constructs                                 |
| Artifact schema version    | Encoding and compatibility of compiler outputs                 |
| Formal-model version       | Lean encoding and semantic library                             |

During `0.x`, deliberate breaking changes are acceptable. Migration help is best effort. Before stability, define the compatibility policy. Do not freeze weak designs too early.

After stability:

- Compiler upgrades keep the specified behavior for supported editions.
- An intentional incompatible source change needs an explicit edition opt-in.
- Dependencies with different supported editions work together through compatible semantic artifacts.
- Semantic changes get a stricter review than syntax changes.
- The project documents the semantic and artifact compatibility rules and gives them versions.

A common semantic IR is the target for interoperability. It can change through versioned schemas and checked conversions. One immutable encoding forever would freeze the compiler without need.

Compatibility applies to the specified semantics. A compiler bug can get a fix. A fix that changes hardware needs clear diagnostics, release documentation, and revalidation guidance. Do not promise identical netlists across compiler releases. An optimization can change the structure and keep the behavior.

These areas need explicit semantic policies, because a change can alter the observable hardware behavior:

- Width inference and signedness.
- Arithmetic.
- Clocks and reset.
- Memory.
- Constant evaluation and elaboration.
- X and Z handling.

## 10. Migration workflow

The responsibilities in a migration are:

- Silicon owns the migration knowledge. It emits structured diagnostics and machine-applicable edits.
- Lattice coordinates the workspace changes.
- The configured backend rebuilds and validates the changes.
- Lean checks the affected proof obligations.

Proposed command:

```sh
lattice migrate --edition 2032
```

A migration does these steps:

1. Build a baseline. Record the semantic inputs, the interfaces, and the proof results.
2. Request diagnostics for the future edition and structured compiler edits.
3. Apply the safe edits. Prefer a form that both editions accept.
4. Update the edition metadata of the package explicitly.
5. Rebuild through the selected backend.
6. Run the relevant simulations and proof checks again.
7. Compare the interfaces and the semantic artifacts under a declared comparison policy.
8. Report the unresolved edits, the changed behavior, and the obligations that need a review.

For a change of syntax only, equal canonical semantic artifacts are a strong acceptance condition. This applies when the encoding rules and the normalization rules are comparable. Different hashes do not prove different behavior. Identical hashes only show identity within the specified artifact contract. A change across representations can need a translation or LEC.

Existing proofs that pass after a migration are useful. They cover only their stated properties. An intended change of behavior needs explicit acceptance and updated contracts or proofs. Do not show it as an upgrade that keeps the semantics.

## 11. Architectural invariants

1. Lattice resolves a package once. All consumers use that exact dependency map.
2. Different package versions keep distinct identities through the full pipeline.
3. Shared HDL namespaces get deterministic, collision-checked uniquified names.
4. RTL, formal artifacts, and debug tools share an explicit identity and name map.
5. Compiler semantics and package identity do not depend on a build backend.
6. Cache keys include every declared input that is relevant to the meaning of the artifact.
7. Interface reuse does not bypass the proof obligations of an implementation.
8. Edition migration is explicit, and each package can do it separately.
9. A proof result names its model, its assumptions, its inputs, and its trusted bridges.

ADRs record these invariants:

- [ADR 0006](../adr/0006-lattice-resolves-silicon-defines.md): items 1 and 5 to 9.
- [ADR 0007](../adr/0007-mandatory-uniquification.md): items 2 to 4.

## 12. Proposed implementation sequence

1. Define package identities, the canonical serialization, lockfile edges, and explicit dependency bindings.
2. Implement module resolution and mandatory uniquification. Include the case of the same version from a different source. Include the rewrite of emitted references.
3. Publish versioned contracts for interfaces, semantic IR, and name maps.
4. Implement a minimal build plan for any backend and a native execution path.
5. Add a Bazel adapter that uses the same package and artifact contracts.
6. Add pinned Lean compilation and exact provenance of the semantic model.
7. Develop compiler migration diagnostics before the project makes stable promises about editions.

These details are still open:

- The exact grammar of emitted names.
- The policy for the digest length.
- The artifact schemas.
- The formal semantic representation.
- The support lifetime of an edition.
- The registry protocol.
- The adapters for foreign HDL.
- The scope of the first native builder.

These choices must keep the invariants above.
