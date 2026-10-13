-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Elab

/-!
The port layout of section 7.5 of the front-end spec: the order of the core ports of a module.
This module also expands each port into its leaves. `Flatten` and `Vectors` both read it. No
other module expands a port.

The domain ports come first, then the inputs, then the outputs. In each group of inputs and
outputs, the ports sort by the byte order of their source names. The leaves of one port follow
in packing order. The resolver makes the port names of a module unique, so this order
has no ties, although `qsort` is not stable.

`foldLeaves` streams the leaves of a port: it makes no list of them. A caller thus charges each
leaf before it makes the leaf. In this phase, a port has a scalar type and thus one leaf.
-/
namespace Silicon.Source.Layout

open Names

/-! The core name of the port with the source name `x`. -/
def portName (x : String) : Name := ⟨x, []⟩

/-! One leaf of a port: its core name, its name in a source vector, and its scalar type. -/
structure Leaf where
  name : Name
  entry : String
  ty : Ty

/-! Runs `f` on each leaf of the port `q` in packing order, from the start value `b`. -/
@[inline] def foldLeaves [Monad m] (q : Elab.PortDecl) (b : β) (f : β → Leaf → m β) : m β :=
  f b ⟨portName q.name, q.name, q.ty⟩

/-! The ports of one module in layout order: the inputs, then the outputs. -/
structure Ports (α : Type) where
  inputs : List α
  outputs : List α

/-!
The layout of the domain ports `domain` and the declared ports `ps`. Each declared port comes
with the values of its leaves in packing order. The domain ports stay in their order, `d$0clk`
before `d$0rst`.
-/
def arrange (domain : List α) (ps : Array (Elab.PortDecl × Array α)) : Ports α :=
  let sorted := (ps.qsort fun x y => x.1.name < y.1.name).toList
  let leaves (input : Bool) := (sorted.filter (·.1.input == input)).flatMap (·.2.toList)
  ⟨domain ++ leaves true, leaves false⟩

end Silicon.Source.Layout
