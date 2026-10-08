# Context

This file is the project glossary. Each term has one definition. Use the term with this meaning only. An `_Avoid_` line lists synonyms that the project rejects. `xtask` makes the vale vocabulary from this file.

## Language and semantics

### core IR

The small intermediate representation that has a formal semantics in Lean 4. It contains registers, memories, combinational logic, and module instances. Elaboration produces it.

_Avoid_: intermediate language

### elaboration

The step that evaluates parameters, generics, and loops of the source. Its output is core IR without these constructs.

_Avoid_: unrolling

### register

A state element that updates once per clock edge. It is a first-class primitive of the language.

_Avoid_: flop, flip-flop

### memory

An addressable array of state elements in the core IR.

### module

A named hardware unit with ports. A module declaration defines it. A design uses it through instances.

_Avoid_: entity

### instance

One use of a module inside another module. Each instance has its own state.

### instantiation

A module together with its specific elaboration inputs, for example its parameters. `InstantiationId` identifies it.

### design

The full hierarchy of instances under one top module. Its semantics is a Mealy machine.

### step function

The Lean function that defines one clock cycle of a design. It maps a state and an input to the next state and an output.

_Avoid_: transition function

### black box

A primitive with an assumed contract and no Silicon body. Examples are SRAM macros, PLLs, vendor IP, and clock gates.

_Avoid_: blackbox

### clock domain

The set of registers and memories that one clock drives. A crossing between two clock domains goes through an explicit primitive.

### edition

A version of the source language rules. Each package selects one edition. Packages with different editions work together.

_Avoid_: language version

## Correctness

### translation validation

A check for each compiler run. The compiler emits the core IR as a Lean term, and a checker confirms it. It replaces a verified compiler.

### LEC

Logical equivalence checking. A tool, for example `circt-lec`, proves that the core IR and the emitted Verilog have the same behavior.

_Avoid_: equivalence check

### trust boundary

The line between the parts that are proven, the parts that are validated, and the parts that are trusted. `doc/trust.md` describes it.

### oracle

A tool or a model that can say "wrong" mechanically. Each agent works against an oracle.

## Packages and names

### package

A unit of source that Lattice resolves and Silicon compiles. It has a name, a version, and an edition.

### PackageId

The exact identity of a source package. It contains the name, the version, the canonical source identity, and the source content digest.

### ModuleId

The identity of a module: a `PackageId` and the qualified declaration path.

### InstantiationId

The identity of an instantiation: a `ModuleId` and the canonical elaboration inputs.

### uniquification

The mandatory step that puts the package identity into each emitted module name. Two versions of one package then do not collide.

_Avoid_: name mangling

### emitted name

The globally unique name of a module in the output HDL. Uniquification makes it from a readable package prefix and an identity digest.

_Avoid_: mangled name

### name map

A machine-readable map from source names to full identities, emitted names, and source locations. Tools use it to find a source name from an emitted name.

### semantic artifact

A deterministic compiler output that holds the meaning of a package, for example its elaborated core IR. Proofs and synthesis depend on it.

## Process

### worktree

A git worktree under `.claude/worktrees/`. Each task has its own worktree and its own branch.

### orchestrator

The main Claude Code session. It splits work, dispatches subagents, reads their results, and merges. It does not write product code.

_Avoid_: coordinator
