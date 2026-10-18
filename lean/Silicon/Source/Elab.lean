-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval

/-!
This module holds the top selection and the design of an elaboration. Sections 5.3, 6.1, and 6.2
of the front-end spec define them. `elaborate` runs the top selection and each instantiation
that it reaches, in the evaluation order that section 5.2 gives. The statement walk and the
instantiations are in `Eval` (`Eval.hwStmt` and `Eval.instantiate`), because a call can reach
them. `Source.Eval.Inst` holds their rules and their parts that need no evaluation.
`Source.Flatten` lowers the design to core IR.
-/
namespace Silicon.Source.Elab

open Resolve Names Eval

/-!
A design: the done instantiations in the order they finish, and the top among them. `fields`
gives the named parts with a leaf of each struct type and each enum type of the design. It gives
the number, the name, and the type of each part, in packing order. The lowering thus names the
leaves of a record and of an enum, and it skips an empty part with no step.
-/
structure Design where
  insts : Array Inst
  top : Nat
  fields : Ty → Option (Array (Nat × String × Ty))

/-! The named parts `ps` with a leaf (`Specs.parts`), each with its number. -/
def leafParts (ps : Array (String × Ty)) : Array (Nat × String × Ty) :=
  ps.zipIdx.filterMap fun ((x, u), k) => if u.info.leaves = 0 then none else some (k, x, u)

/-!
The fields with a leaf of each done struct specialization, by its number. `elaborate` makes the
table once, from the fields that each specialization paid for when it completed.
-/
def leafFields (specs : Specs) : Array (Option (Array (Nat × String × Ty))) :=
  specs.entries.map fun e => do
    let .done t _ := e.state | none
    return leafParts (← specs.parts t)

/-!
The named parts with a leaf of the type `t`. A struct type reads them from the table `table`.
An enum type reads them from its done entry in `specs`, with no walk.
-/
def fieldsOf (specs : Specs) (table : Array (Option (Array (Nat × String × Ty)))) :
    Ty → Option (Array (Nat × String × Ty))
  | .struct k .. => table[k]?.join
  | t@(.enum ..) => (specs.parts t).map leafParts
  | _ => none

/-!
The elaboration of the top selection at `pos`: the module item `top` with the literal
arguments `xs`. The arguments get their typed use and charge as those of an `instance`
statement. The result is the
records and the design with the used fuel, or the records and the first error (section 8.2).
-/
def observe (budget : Budget) (items : Array Resolve.Item) (digest : String → String)
    (pos : Pos) (top : Nat) (xs : List Resolve.Expr) :
    Array Record × Except Error (Design × Nat) :=
  Eval.observeRun budget items fun n => withTheReader Ctx (fun c => { c with digest }) do
    let tvs ← arguments (eval n) (typeExpr n) pos top xs
    let k := (← instantiate n pos top tvs).2
    let s ← get
    return ⟨s.inst.done, k, fieldsOf s.specs (leafFields s.specs)⟩

/-! The elaboration of the top selection, without the records. -/
def elaborate (budget : Budget) (items : Array Resolve.Item) (digest : String → String)
    (pos : Pos) (top : Nat) (xs : List Resolve.Expr) : Except Error (Design × Nat) :=
  (observe budget items digest pos top xs).2

/-! The output of `cost` (section 8): the total, then the units of each instantiation by name. -/
def costLines (d : Design) (total : Nat) : String :=
  let lines := d.insts.map fun i => (encode i.iface.name, i.units)
  let sorted := lines.qsort fun a b => a.1 < b.1
  sorted.foldl (fun s (x, u) => s ++ s!"{x} {u}\n") s!"total {total}\n"

end Silicon.Source.Elab
