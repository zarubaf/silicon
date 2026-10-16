-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Basic

/-!
The types as values of the evaluator. These are the type constructors with their charges and the
join of two types. The table of constants for the `type` aliases and the table of struct
specializations are here too.
`Source.Eval` evaluates the type expressions with these rules. The types as values of slice 2
follow sections 5.1, 5.4, 5.5, and 5.6. These rules settle their open points:

- Each new type checks its depth before its charge (`S015` at its node).
- `[T; N]` charges its size and the three products of its metadata (`Meta.arrayCharge`). A tuple
  type charges its size, then the sums of its metadata (`sums`), as a struct does.
- A function type evaluates its parameter types, then its result type. Its metadata reads only
  the depths of its parts, as `List[T]` does, so it adds no charge. It checks its depth, then
  charges its size (`fnTy`).
- A join walks two types together. It charges 1 before it visits each pair of container types:
  arrays, tuples, lists, and struct types. A pair of two struct types charges as a type
  equality, the sum of the two sizes, and compares the identities. A pair of two function types
  charges in the same way and needs two equal types, also in their `mut` marks. Another pair
  charges nothing. A visit that fails stops the walk, so the charge counts the pairs up to that
  visit.
- A `type` item is a constant of type `Type` in the table of constants. Its first use evaluates
  its type expression, and a use while it is in progress is `S019`.
- The key of a struct specialization is its struct item and its static arguments. Each
  argument comes after its typed use at its parameter type: the normalized identity of v0.1.
  Thus `P[8]` and
  `P[UInt[4](8)]` are one type when the parameter of `P` has the type `UInt[4]`. Each use counts
  toward the nesting depth (`S015`). It evaluates the parameter types in the scope of the
  struct and binds the parameters as typed uses, with their charges and errors. The work of
  the prelude struct `ReadResponse` reports each of its errors at the use (`atUse`). Then it
  charges the sum of the sizes of the arguments, before the lookup, because the lookup reads
  them in full. A first use then charges the size of the struct type and evaluates the field
  types. Then it checks the depth of the struct type (`S015`) and charges the sums of its
  metadata. A use in progress is `S019`. A use of a done entry charges nothing more. A use of
  a struct item while its own parameter types evaluate is `S019` too, because its key does not
  exist yet.
-/
namespace Silicon.Source.Eval

open Resolve

/-!
A new value or type of the depth `d` at `pos`. Above the nesting depth, it is `S015` at `pos`,
or at the name of a function value whose signature evaluates.
-/
def bounded (pos : Pos) (d : Nat) : M Unit := do
  let c ← read
  if c.limit < d then
    fail .S015 (c.site.getD pos) s!"the depth {d} goes above the nesting depth {c.limit}"

/-!
A walk over types or values that counts its charge. A failure keeps the charge of the visits
before it.
-/
abbrev Walk := ExceptT Fault (StateM Nat)

/--
Runs the walk `w` at `pos`. It charges the visits of the walk, then gives its result. A charge
above the fuel is `S015` with a message that names no count. The Rust front end stops its walk
when the fuel cannot pay it, so it does not know the whole count.
-/
def walked (pos : Pos) (w : Walk α) : M α := do
  let (r, k) := Id.run (w.run.run 0)
  chargeWith pos k fun left =>
    s!"the fuel cannot pay the joins of the types; {intText left} remain"
  lift pos r

/-!
Runs `act`, the work of the prelude struct at its use `p`. Each error of `act` reports at `p`,
because the prelude struct has no source position (section 6.2).
-/
def atUse (p : Pos) (act : M α) : M α := fun c s =>
  match act c s with
  | .ok r => .ok r
  | .error e => .error { e with err.pos := p }

/-!
The charge at `pos` of the metadata sums of a tuple or a struct type with the metadata `m` and
the parts `parts`. The sums read the four integers of each part, so they charge their sizes
first. Then they charge the sizes of the four new integers of `m`.
-/
def sums (pos : Pos) (parts : List Meta) (m : Meta) : M Unit := do
  charge pos (Meta.readCharge parts)
  charge pos m.intCharge

/-! A container type: an array, a tuple, a list, or a struct type. -/
def containerTy : Ty → Bool
  | .array .. | .tuple _ | .list _ | .struct .. => true
  | _ => false

/-! The common type of two types that are not two arrays or two tuples: the operand rule. -/
def scalarJoin : Ty → Ty → Option Ty
  | .nat, .nat => some .nat
  | .int, .int | .int, .nat | .nat, .int => some .int
  | .int, t | .nat, t => if t.finite then some t else none
  | s, .int | s, .nat => if s.finite then some s else none
  | s, t => if s.same t then some s else none

/-!
The join of two types: their common type by the operand rule. A static integer takes the finite
type of the other side. Arrays need one length and tuples one arity. Two lists join their
element types.
-/
mutual
  def joinTy : Ty → Ty → StateM Nat (Option Ty)
    | .array s n, .array t m => do
      modify (· + 1)
      if n = m then
        let r ← joinTy s t
        return r.map (.array · n)
      else return none
    | .list s, .list t => do
      modify (· + 1)
      return (← joinTy s t).map .list
    | .tuple ⟨ss⟩, .tuple ⟨ts⟩ => do
      modify (· + 1)
      if ss.length = ts.length then
        let r ← joinAll ss ts
        return r.map fun us => .tuple us.toArray
      else return none
    | s@(.struct ..), t@(.struct ..) | s@(.fn ..), t@(.fn ..) => do
      modify (· + (s.size + t.size))
      return if s.same t then some s else none
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
item. The first use evaluates `body` one level deeper, in the scope of the item, so the field
names of `body` have their symbols. A use in progress is `S019`.
-/
def constant (p : Pos) (x : String) (i : Nat) (body : M Value) : M Value := do
  match (← get).consts[i]? with
  | some (.done c) => return c
  | some .inProgress => fail .S019 p s!"`{x}` depends on itself"
  | _ => structural <| nested p do
    setConst i .inProgress
    let c ← inFrame none <| withReader (fun c => { c with item := i }) body
    setConst i (.done c)
    return c

/-!
A use at `p` of the struct item `i` with the name `x`, the prelude flag `pre`, and the
normalized static arguments `args`. It charges their sizes before the lookup. The key of the
lookup is the item and the arguments, so its work stays in that charge. The first use runs
`fields`, which evaluates the field types. The caller nests it.
-/
def specialize (p : Pos) (x : String) (i : Nat) (pre : Bool) (args : List Value)
    (fields : M (List Ty)) : M Ty := do
  charge p (Value.sizeAll args)
  match (← get).specs.find? i args with
  | some (_, ⟨_, _, .done t _⟩) => return t
  | some (k, ⟨_, _, .inProgress⟩) =>
    let t := Ty.struct k x args.toArray Meta.static pre
    fail .S019 p s!"the specialization {t.text} is in progress"
  | none => do
    let k := (← get).specs.entries.size
    charge p (Ty.struct k x args.toArray Meta.static pre).size
    modify fun s => { s with specs := ⟨s.specs.entries.push ⟨i, args, .inProgress⟩,
      s.specs.index.insert (i, args) k⟩ }
    let fs ← fields
    let ms := fs.map Ty.info
    let m := Meta.struct ms (args.map Value.depth)
    bounded p m.depth
    sums p ms m
    let t := Ty.struct k x args.toArray m pre
    modify fun s => { s with specs := { s.specs with
      entries := s.specs.entries.set! k ⟨i, args, .done t fs.toArray⟩ } }
    return t

/-!
The struct item and the field types of the struct type `t`, from its done entry in the table of
specializations. The type holds the number of the entry. A record exists only after its
specialization is done, so each record type has one.
-/
def fieldsIn (specs : Specs) : Ty → Option (Nat × Array Ty)
  | .struct k .. => do
    let e ← specs.entries[k]?
    match e.state with
    | .done _ fs => some (e.item, fs)
    | .inProgress => none
  | _ => none

/-! The numbered field types of the struct type `t` (`fieldsIn`), for the offset of a word part. -/
def partsIn (specs : Specs) : Parts := fun t =>
  (fieldsIn specs t).map fun (_, fs) => fs.zipIdx.map fun (u, k) => (k, u)

/-!
The zero of a hardware data type `t` (section 5.6): 0 for each integer leaf and `false` for each
`Bool` leaf. A struct type takes the field types of its done entry. The bound `b` is the depth
of `t`, because each part of a type is less deep than the type.
-/
def zeroOf (specs : Specs) : Nat → Ty → Option Value
  | 0, _ => none
  | b + 1, t =>
    match t with
    | .bool => some (.bool false)
    | .uint w => some (.uint w 0)
    | .sint w => some (.sint w 0)
    | .unit => some .unit
    | .array e k => do return .array e (Array.replicate k (← zeroOf specs b e))
    | .tuple ⟨ts⟩ => do return .tuple (← ts.mapM (zeroOf specs b)).toArray
    | .struct .. => do
      let (_, fs) ← fieldsIn specs t
      return .record t (← fs.mapM (zeroOf specs b))
    | .nat | .int | .type | .string | .list _ | .fn .. => none

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

/-! The tuple type of `ts` at `pos`. It charges its size and the sums of its metadata. -/
def tupleTy (pos : Pos) (ts : List Ty) : M Ty := do
  let t := Ty.tuple ts.toArray
  bounded pos t.depth
  charge pos t.size
  sums pos (ts.map Ty.info) t.info
  return t

/-!
The function type with the parameter types `ps` and the result type `r` at `pos`. It checks its
depth, then charges its size.
-/
def fnTy (pos : Pos) (ps : List TyParam) (r : Ty) : M Ty := do
  let t := Ty.fn ps.toArray r
  bounded pos t.depth
  charge pos t.size
  return t

end Silicon.Source.Eval
