-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Elab

/-!
The port layout of section 7.5 of the front-end spec: the order of the core ports of a module.
This module also expands each part of a hardware data type into its leaves. `Flatten` and
`Vectors` both read it. No other module expands a port.

The domain ports come first, then the inputs, then the outputs. In each group of inputs and
outputs, the ports sort by the byte order of their public names, then by their family keys as
numbers (`Eval.portBefore`). A public name is the binder or the name of an `as` key (section 5.6). A
scalar port has no key, and no key sorts before each key, so `req[2]` comes before `req[10]`.
The sort compares two names only when their symbols differ. The leaves of one port follow in
packing order. Thus the layout order is not the byte order of the core names. One public name
has one form (section 5.6), and one family has each key once. Thus this order has no ties,
although `qsort` is not stable.

`foldLeaves` streams the leaves of a type in packing order: it makes no list of them. A caller
thus charges each leaf before it makes the leaf. A part without a leaf takes one step, and a
struct visits only its fields with a leaf. An enum has the two leaves `tag` and `payload`, or
only `tag` when its payload is empty (section 5.1). A port, a register, a wire, a child port, a
memory word, and a `:=` binding all take their leaves from it.
-/
namespace Silicon.Source.Layout

open Names Eval

/-!
The named parts with a leaf of a struct type or an enum type, in packing order. Each has its
number, its name, and its type (`Elab.Design.fields`). An enum has the parts `tag` and `payload`.
-/
abbrev Fields := Ty → Option (Array (Nat × String × Ty))

/-! One leaf of a part: its path with the leaf fields of section 7.3, and its scalar type. -/
structure Leaf where
  path : Path
  ty : Ty

/-! The core name of a leaf. -/
def Leaf.name (l : Leaf) : Name := l.path.name

/-!
The name of a leaf of a port in a source vector (section 11.2). It is the public name of the
port, then `[k]` for the key of a family entry. Then each level adds `.f` for a field and `.k`
for an element.
-/
def Leaf.entry (l : Leaf) : String :=
  l.path.inner.foldr (fun f s => s ++ text f) l.path.outer
where
  text : Field → String
    | .user x => "." ++ x
    | .elem k => "." ++ toString k
    | .family k => s!"[{k}]"
    | f => "." ++ f.encode

/-!
Runs `f` on each leaf of the part of the type `t` at the path `p` in packing order, from the
start value `b`. `x` is the source of the part. `sub` gives the source of its element `k` of the
type `u` with the leaf field `fd`. `f` gets the source of each leaf. The bound `d` is the
depth of `t`. A part without a leaf takes one step, and a struct or an enum visits only its parts
with a leaf. A struct or an enum type without its parts in `fs` gives `bad`.
-/
def foldLeaves [Monad m] (fs : Fields) (sub : α → Field → Nat → Ty → α)
    (f : β → Leaf → α → m β) (bad : β → Ty → m β) : Nat → Path → Ty → α → β → m β
  | 0, _, _, _, b => pure b
  | d + 1, p, t, x, b =>
    if t.info.leaves = 0 then pure b
    else match t with
    | .bool | .uint _ | .sint _ => f b ⟨p, t⟩ x
    | .array e n => do
      let mut b := b
      for k in [0:n] do
        b ← foldLeaves fs sub f bad d (p.push (.elem k)) e (sub x (.elem k) k e) b
      return b
    | .tuple ts => do
      let mut b := b
      for k in [0:ts.size] do
        let u := ts.getD k .unit
        b ← foldLeaves fs sub f bad d (p.push (.elem k)) u (sub x (.elem k) k u) b
      return b
    | .struct .. | .enum .. => do
      let some nfs := fs t | bad b t
      let mut b := b
      for (k, y, u) in nfs do
        b ← foldLeaves fs sub f bad d (p.push (.user y)) u (sub x (.user y) k u) b
      return b
    | _ => pure b

/-! Runs `f` on each leaf of the port `q` in packing order, from the start value `b`. -/
@[inline] def foldPort [Monad m] (fs : Fields) (q : Elab.PortDecl) (b : β) (f : β → Leaf → m β)
    (bad : β → Ty → m β) : m β :=
  foldLeaves fs (fun _ _ _ _ => ()) (fun b l _ => f b l) bad q.ty.depth q.path q.ty () b

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
  let ident (q : Elab.PortDecl) : String × PortId := (q.name, q.sym, q.key)
  let sorted := (ps.qsort fun x y => portBefore (ident x.1) (ident y.1)).toList
  let leaves (input : Bool) := (sorted.filter (·.1.input == input)).flatMap (·.2.toList)
  ⟨domain ++ leaves true, leaves false⟩

end Silicon.Source.Layout
