-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Basic

/-!
The types as values of the evaluator: the type constructors with their charges, the join of two
types, the table of constants for the `type` aliases, and the table of struct specializations.
`Source.Eval` evaluates the type expressions with these rules. The types as values of slice 2
follow sections 5.1, 5.4, 5.5, and 5.6. These rules settle their open points:

- Each new type checks its depth before its charge (`S015` at its node).
- `[T; N]` charges its size and the three products of its metadata (`Meta.arrayCharge`). A tuple
  type charges its size and the sizes of the four integers of its metadata, as a struct does.
- A join walks two types together. It charges 1 before it visits each pair of container types:
  arrays, tuples, and struct types. A pair of two struct types charges as a type equality, the
  sum of the two sizes, and compares the identities. Another pair charges nothing. A visit that
  fails stops the walk, so the charge counts the pairs up to that visit.
- A `type` item is a constant of type `Type` in the table of constants. Its first use evaluates
  its type expression, and a use while it is in progress is `S019`.
- The table of struct specializations holds each struct item with its static arguments as they
  evaluate, before the typed use at the parameters, as an `InstantiationId` does. The first use
  counts toward the nesting depth (`S015`). It charges the size of the struct type, binds the
  parameters as typed uses, and evaluates the field types in the scope of the struct. Then it
  checks the depth of the struct type (`S015`) and charges `Meta.structCharge`. A use in progress
  is `S019`. A use of a done entry charges nothing more than its node.
-/
namespace Silicon.Source.Eval

open Resolve

/-! A new value or type of the depth `d` at `pos`. Above the nesting depth, it is `S015`. -/
def bounded (pos : Pos) (d : Nat) : M Unit := do
  let c ← read
  if c.limit < d then fail .S015 pos s!"the depth {d} goes above the nesting depth {c.limit}"

/-!
A walk over types or values that counts its charge. A failure keeps the charge of the visits
before it.
-/
abbrev Walk := ExceptT Fault (StateM Nat)

/-! Runs the walk `w` at `pos`. It charges the visits of the walk, then gives its result. -/
def walked (pos : Pos) (w : Walk α) : M α := do
  let (r, k) := Id.run (w.run.run 0)
  charge pos k
  lift pos r

/-! A container type: an array, a tuple, or a struct type. -/
def containerTy : Ty → Bool
  | .array .. | .tuple _ | .struct .. => true
  | _ => false

/-! The common type of two types that are not two arrays or two tuples: the operand rule. -/
def scalarJoin : Ty → Ty → Option Ty
  | .nat, .nat => some .nat
  | .int, .int | .int, .nat | .nat, .int => some .int
  | .int, t | .nat, t => if t.finite then some t else none
  | s, .int | s, .nat => if s.finite then some s else none
  | s, t => if s = t then some s else none

/-!
The join of two types: their common type by the operand rule. A static integer takes the finite
type of the other side. Arrays need one length and tuples one arity.
-/
mutual
  def joinTy : Ty → Ty → StateM Nat (Option Ty)
    | .array s n, .array t m => do
      modify (· + 1)
      if n = m then
        let r ← joinTy s t
        return r.map (.array · n)
      else return none
    | .tuple ⟨ss⟩, .tuple ⟨ts⟩ => do
      modify (· + 1)
      if ss.length = ts.length then
        let r ← joinAll ss ts
        return r.map fun us => .tuple us.toArray
      else return none
    | s@(.struct ..), t@(.struct ..) => do
      modify (· + (s.size + t.size))
      return if s = t then some s else none
    | s, t => do
      if containerTy s && containerTy t then modify (· + 1)
      return scalarJoin s t

  def joinAll : List Ty → List Ty → StateM Nat (Option (List Ty))
    | s :: ss, t :: ts => do
      let some u ← joinTy s t | return none
      let r ← joinAll ss ts
      return r.map (u :: ·)
    | _, _ => return some []
end

/-! The type of the value of the name `x` at `p`. Another value is `S010`. -/
def typeOf (p : Pos) (x : String) : Val → M Ty
  | .static (.type t) => pure t
  | v => fail .S010 p s!"`{x}` names a type, not {v.text}"

/-!
A use at `p` of the item `i` with the name `x` in the table of constants: a `const` or a `type`
item. The first use evaluates `body` one level deeper. A use in progress is `S019`.
-/
def constant (p : Pos) (x : String) (i : Nat) (body : M Value) : M Value := do
  match (← get).consts[i]? with
  | some (.done c) => return c
  | some .inProgress => fail .S019 p s!"`{x}` depends on itself"
  | _ => nested p do
    setConst i .inProgress
    let c ← inFrame none body
    setConst i (.done c)
    return c

/-!
A use at `p` of the struct item `i` with the name `x` and the static arguments `args`. The first
use runs `fields`, which binds the parameters and evaluates the field types.
-/
def specialize (p : Pos) (x : String) (i : Nat) (args : List Value) (fields : M (List Ty)) :
    M Ty := do
  let found : Option SpecState :=
    ((← get).specs.find? fun e => e.item == i && e.args == args).map (·.state)
  match found with
  | some (.done t _) => return t
  | some .inProgress =>
    fail .S019 p s!"the specialization {(Ty.struct x args.toArray Meta.static).text} is in progress"
  | none => nested p do
    charge p (Ty.struct x args.toArray Meta.static).size
    let k := (← get).specs.size
    modify fun s => { s with specs := s.specs.push ⟨i, args, .inProgress⟩ }
    let fs ← fields
    let ms := fs.map Ty.info
    let m := Meta.struct ms (args.map Value.depth)
    bounded p m.depth
    charge p (Meta.structCharge ms m)
    let t := Ty.struct x args.toArray m
    modify fun s => { s with specs := s.specs.set! k ⟨i, args, .done t fs⟩ }
    return t

/-!
The array type `[e; k]` at `pos`. The length at `q` is a static `Nat`. It charges its size and
the products of its metadata.
-/
def arrayTy (pos q : Pos) (e : Ty) : Value → M Ty
  | .int k => do
    if k < 0 then fail .S012 q s!"the length {intText k} is not a Nat"
    let t := Ty.array e k.toNat
    bounded pos t.depth
    charge pos (t.size + e.info.arrayCharge k.toNat)
    return t
  | v => fail .S010 q s!"the length of an array is a static Nat, not {v.text}"

/-! The tuple type of `ts` at `pos`. It charges its size and the integers of its metadata. -/
def tupleTy (pos : Pos) (ts : List Ty) : M Ty := do
  let t := Ty.tuple ts.toArray
  bounded pos t.depth
  charge pos (t.size + t.info.intCharge)
  return t

end Silicon.Source.Eval
