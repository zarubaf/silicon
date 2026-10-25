-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Container

/-!
The type steps of `@TypeOf(x)` (sections 5.4 and 9.3). `Eval.typeOfPart` resolves the root of
the place `x`. `Eval.queryWalk` charges each step and evaluates its key in a structural context
of the kind `query`. Then the step runs here. The walk goes once from the root outward.

The walk holds a `Query`. A static value, a container node, and an `Instance` handle keep their
value and their declared type, if they have one. A reference and a hardware value keep only
their data type (`Val.typeOnly?`). So does a handle of a register, a wire, an own output, or a
child input. Each later step then selects in the type. It reads nothing, it charges no zero
size, and it makes no node. A field of an `Instance` handle selects the child port.
`Eval.queryWalk` does it, because it needs the port look-ups.

The result refers to an existing type, so it charges nothing more. A static tuple without a
declared type stores no type, so the walk builds its type at the end (`builtTy`). Each tuple
node charges 1 before the walk visits its elements, then the size of the built type charges.
Only then the result exists.
-/
namespace Silicon.Source.Eval

open Resolve Names

/-!
The part of a query operand after the steps so far. It is a value with its declared type, if it
has one, or only a data type.
-/
inductive Query where
  | value (v : Val) (decl : Option Ty)
  | type (t : Ty)

/-!
A step of a query operand after its key evaluated. It is an index at `pos` with the static key
`k` at `q`, or a selector `.i` with its literal at `q`. It can also be a field at `pos` with the
symbol `y` and the name `name`. `shown` is the name in a message.
-/
inductive QueryStep where
  | index (pos q : Pos) (k : Value)
  | select (pos q : Pos) (i : Nat)
  | field (pos : Pos) (y : Option Nat) (name shown : String)

/-!
The data type of the value `v` when a step on it selects in the type only (section 9.3). These
values are a reference, a hardware value, and a handle of a register, a wire, an own output, or a
child input. Another value holds its parts, so it gives `none`.
-/
def Val.typeOnly? : Val → Option Ty
  | .hw h => some h.ty
  | .agg (.ref _ t) => some t
  | .handle (.res _ _ t _) => some t
  | .handle (.input _ _ q) => some q.ty
  | _ => none

/-!
The type that the container value `v` stores, with no walk. A static tuple stores none, and
neither does a value that is no container.
-/
def Val.stored? : Val → Option Ty
  | .static (.tuple _) => none
  | .static v => v.ty?
  | .agg a => a.ty?
  | _ => none

/-! The value `{a}` of a part of the type `t` in a message, as a reference of `t` names it. -/
def partText (t : Ty) : String := if t.info.leaves = 0 then t.text else s!"hardware {t.text}"

/-!
The step `s` on a part of the data type `t` (section 9.3). A field selects the field type of a
struct, and a selector the element type of a tuple. An index selects the element type of an
array or a tuple. The checks and their texts are those of a step on a reference of `t`
(`fieldBy`, `selectKey`, `pickKey`). An index checks its range against the length of the type.
-/
def tyStep (t : Ty) : QueryStep → M Ty
  | .field q y _ shown => do
    noEnumField q shown (some t)
    if t matches .struct .. then return (← fieldBy q y shown t (partText t)).2
    fail .S010 q s!"{partText t} has no field `{shown}`"
  | .select q r i => do
    noEnumField q (toString i) (some t)
    match t with
    | .tuple ts =>
      match ts[i]? with
      | some u => pure u
      | none => fail .S013 r s!"the selector {i} is out of range for {partText t}"
    | _ => fail .S010 q s!"the selector `.{i}` needs a tuple, not {partText t}"
  | .index q r k => do
    match t with
    | .array e n => do
      let _ ← within r n k
      return e
    | .tuple ts => do
      match ts[← within r ts.size k]? with
      | some u => pure u
      | none => fail .S013 r s!"the index is out of range for {ts.size} element(s)"
    | _ => fail .S010 q s!"an index needs an array, a list, or a tuple, not {partText t}"

/-!
The step `s` on the value `v` that holds its parts (section 9.3). A container node gives its
element as it is, so a reference in it charges no zero size. A list node checks the index
against its own length. Each other value takes the step of a place (`pickKey`, `selectKey`,
`fieldKeyBy`). A static value selects there with no charge, and another value fails there, for
example a memory with `S010`. The result is the number of the part, the part, and the field
type of a field.
-/
def valueStep (v : Val) (s : QueryStep) : M (Nat × Val × Option Ty) := do
  match s, v with
  | .index _ q k, .agg (.array _ xs) | .index _ q k, .agg (.tuple _ xs)
  | .index _ q k, .agg (.list _ _ xs) => do
    let j ← within q xs.size k
    match xs[j]? with
    | some x => return (j, x.val, none)
    | none => fail .S013 q s!"the index is out of range for {xs.size} element(s)"
  | .select _ r i, v@(.agg (.tuple _ xs)) =>
    match xs[i]? with
    | some x => return (i, x.val, none)
    | none => fail .S013 r s!"the selector {i} is out of range for {v.text}"
  | .field q y _ shown, v@(.agg (.record n xs)) => do
    noEnumField q shown (some n.ty)
    let (k, ft) ← fieldBy q y shown n.ty v.text
    match xs[k]? with
    | some x => return (k, x.val, some ft)
    | none => fail .S010 q s!"{v.text} has no field `{shown}`"
  | .index p q k, v => do
    let (j, w) ← pickKey p q v k
    return (j, w, none)
  | .select p q i, v => do
    let (j, w) ← selectKey p q i v
    return (j, w, none)
  | .field p y name shown, v => do
    let (k, w, ft) ← fieldKeyBy p p y name shown v
    return (k, w, some ft)

/-!
The step `s` on the part `q` (section 9.3). A part that keeps only its type selects in the type
(`tyStep`). Another part selects in its value (`valueStep`). A field gives its field type as
the declared type of the part. Another step gives the part of the declared type, else of the
stored type of the container. A static tuple without a declared type has none.
-/
def queryStep (q : Query) (s : QueryStep) : M Query := do
  match q with
  | .type t => return .type (← tyStep t s)
  | .value v decl =>
    match v.typeOnly? with
    | some t => return .type (← tyStep t s)
    | none => do
      let (k, w, ft) ← valueStep v s
      return .value w (ft <|> ((decl <|> v.stored?).bind (partTy · k)))

/-!
The part that the port `port` of the child number `id` with the path `path` gives in a query
operand (section 9.3). An input gives its handle, and an output its type, with no read.
-/
def portQuery (id : Nat) (path : Path) (port : Port) : Query :=
  if port.input then .value (.handle (.input id path port)) none else .type port.ty

/-!
The type of the static value `v` at the node `p` of `@TypeOf` (section 5.4). A tuple stores no
type, so the walk builds it: each tuple node charges 1 before the walk visits its elements. Each
other value refers to its type, with no charge.
-/
mutual
  def builtWalk (p : Pos) : Value → M Ty
    | .tuple xs => do
      charge p 1
      return .tuple (← builtAll p xs.toList).toArray
    | v => pure v.ty

  def builtAll (p : Pos) : List Value → M (List Ty)
    | [] => pure []
    | x :: xs => do
      let t ← builtWalk p x
      return t :: (← builtAll p xs)
end

/-!
The type of the static value `v` at the node `p` of `@TypeOf`. A tuple builds its type
(`builtWalk`), then the size of the type term charges. Only then the result exists.
-/
def builtTy (p : Pos) (v : Value) : M Ty := do
  let t ← builtWalk p v
  if v matches .tuple _ then charge p t.size
  return t

/-!
The type of the part `q` at the end of the walk, at the node `p` of `@TypeOf` (section 9.3).
A declared type and a type of the walk are the result. A value gives its type: a static value by
`builtTy`, an own output its data type, and a handle its handle type. A domain has no type.
-/
def queryTy (p : Pos) : Query → M Ty
  | .type t | .value _ (some t) => pure t
  | .value (.static v) none => builtTy p v
  | .value (.handle (.res .output _ t _)) none => pure t
  | .value v none =>
    match v.ty? with
    | some t => pure t
    | none => fail .S010 p (s!"`@TypeOf` takes a part with a type, not {v.text}; pass a value, " ++
        "a port, or a resource")

end Silicon.Source.Eval
