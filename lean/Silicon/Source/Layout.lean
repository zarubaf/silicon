-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Elab

/-!
The port layout of section 7.5 of the front-end spec: the order of the core ports of a module.
`Flatten` and `Vectors` both read it.

The domain ports come first, then the inputs, then the outputs. In each group of inputs and
outputs, the ports sort by the byte order of their source names. This order equals the order of
the core names, because a name that `encode` changes only gets `$0k`, and `$` sorts before each
name character. The resolver makes the port names of a module unique, so this order has no ties,
although `qsort` is not stable.
-/
namespace Silicon.Source.Layout

/-! The ports of one module in layout order: the inputs, then the outputs. -/
structure Ports (α : Type) where
  inputs : List α
  outputs : List α

/-!
The layout of the domain ports `domain` and the declared ports `ps`. Each declared port comes
with its value. The domain ports stay in their order, `d$0clk` before `d$0rst`.
-/
def arrange (domain : List α) (ps : Array (Elab.PortDecl × α)) : Ports α :=
  let sorted := (ps.qsort fun x y => x.1.name < y.1.name).toList
  ⟨domain ++ (sorted.filter (·.1.input)).map (·.2), (sorted.filter (!·.1.input)).map (·.2)⟩

end Silicon.Source.Layout
