-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Vectors
import Silicon.Source.Flatten

/-!
The source vectors of section 11.2 of the front-end spec, and the port schema of the top.

A source vector has the form of a core vector (core IR spec, section 6.4.3), with source names
and source values. The port schema maps each source port of the top to its core port.
`parseLine` maps a source input line to the core input values, and `printLine` maps the core
output values to a source output line.

These rules settle the open points of the spec:

- Schema order is the port layout of `Source.Layout`, without the clock.
- An input line lists the reset `d$0rst` of the domain `d` first. A combinational top has none.
- The reset is a `Bool` value. The clock has no entry.
- An input value has the decimal forms of a core value. A `UInt` value and the magnitude of an
  `SInt` value can thus have leading zeros, and `-0` is 0.
- An output value has no leading zeros, and only a negative `SInt` value has `-`.
-/
namespace Silicon.Source.Vectors

open Names

/-! One port of the schema: its name in a source vector, its core name, and its type. -/
structure Entry where
  name : String
  core : String
  ty : Ty

/-! The port schema of the top: the inputs and the outputs, each in schema order. -/
structure Schema where
  inputs : List Entry
  outputs : List Entry

/-!
The port schema of the top of `d`. The reset of the domain comes before the inputs. The result
is `none` when the top is not a done instantiation.
-/
def schema (d : Elab.Design) : Option Schema := do
  let top ← d.insts[d.top]?
  let b := top.body
  let entry (q : Elab.PortDecl) : Entry := ⟨q.name, encode (Flatten.portName q.name), q.ty⟩
  let reset := match b.domain with
    | some dom => let x := encode (Flatten.resetName dom); [⟨x, x, .bool⟩]
    | none => []
  let layout := Layout.arrange reset (b.ports.map fun q => (q, entry q))
  return ⟨layout.inputs, layout.outputs⟩

/-!
The schema fits the core design `d` when its core names are the port names of the top module of
`d`, in port order. The clock is not in the schema.
-/
def fits (s : Schema) (d : Core.Design) : Bool :=
  match d.items.find? (·.name == d.top) with
  | some (.module m) =>
    let names (dir : Core.PortDir) :=
      (m.ports.filter fun p => p.dir == dir && p.ty != .clock).map (·.name)
    names .input == s.inputs.map (·.core) && names .output == s.outputs.map (·.core)
  | _ => false

/-! A decimal natural number with at least one digit. -/
def decimal (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

/-! The core value of the source value `v` for a port of type `t`. -/
def parseValue (name : String) (t : Ty) (v : String) : Except String Nat := do
  let bad := s!"input {name} has no value of its type"
  match t with
  | .bool => if v == "true" then return 1 else if v == "false" then return 0 else throw bad
  | .uint w =>
    let some n := decimal v | throw bad
    if n < 2 ^ w then return n else throw s!"input {name} exceeds its width"
  | .sint w =>
    let (neg, digits) := if v.startsWith "-" then (true, (v.drop 1).toString) else (false, v)
    let some n := decimal digits | throw bad
    let half := 2 ^ (w - 1)
    if neg && n ≤ half then return (2 ^ w - n) % 2 ^ w
    else if !neg && n < half then return n
    else throw s!"input {name} exceeds its width"
  | _ => throw bad

/-! The pairs of the tokens `tokens` for the entries `es`, in schema order. -/
def pairs : List Entry → List String → Except String (List (String × Nat))
  | [], [] => .ok []
  | [], _ => .error "extra input tokens"
  | e :: es, name :: value :: rest => do
    if name != e.name then throw s!"expected input {e.name}"
    return (e.core, ← parseValue e.name e.ty value) :: (← pairs es rest)
  | _ :: _, _ => .error "missing input"

/-! The core input values of a source input line. The tokens follow the core vector format. -/
def parseLine (s : Schema) (line : String) : Except String (List (String × Nat)) := do
  pairs s.inputs (← Core.inputTokens line)

/-! The source text of the core value `n` of type `t`. -/
def valueText (t : Ty) (n : Nat) : String :=
  match t with
  | .bool => if n == 0 then "false" else "true"
  | .sint w => if 2 ^ (w - 1) ≤ n then s!"-{2 ^ w - n}" else toString n
  | _ => toString n

/-!
The source output line of the core output values `values`, in port order. The schema must fit
the design, so the values and the outputs of the schema agree in order.
-/
def printLine (s : Schema) (values : List (String × Nat)) : String :=
  Core.outputLine (s.outputs.zipWith (fun e v => (e.name, valueText e.ty v.2)) values)

end Silicon.Source.Vectors
