-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Types

/-!
The static containers of the evaluator. These are the typed use of a container, the common type,
`==` on containers, and the literals with their depth and their charge. The literals that wait
for their type, the index, the selector `.N`, `len`, and the places of an assignment are here too.
So are the records of section 5.6: the constructor, the field `.f`, and the zero `T()`.

The static containers of slice 2 follow section 5.1. These rules settle its open points:

- In this phase, a container holds only static values. A hardware element is `S010` at the
  element. A handle as an element is `S010` until slice 3.
- An array literal takes the common type of its elements by the operand rule. The join of the
  types charges its visits (`Source.Eval.Types`). The typed use of each element at that type
  charges as a conversion. Then the literal charges its size.
- `[]` gets its type `[T; 0]` only at a typed use: an annotation, an assignment, an argument,
  a return, a constant, or a module argument. A literal with `[]` as an element waits for its
  type too. The typed use then gives each `[]` the type at its place, and each literal charges
  as at its node. Without a typed use, it is `S010` at the first `[]`.
- A typed use of a container at another type converts each element. It charges the size of
  the value plus the size of the result.
- `==` and `!=` on containers need a common type for each pair of elements. Each pair of arrays
  and each pair of lists joins its element types and charges the visits of the join. Then the
  operator charges the sum of the two sizes. Each pair compares, so each conversion checks its
  fit (`S012`). The length of a list is a value, not a part of its type, so two lists of
  different lengths are unequal.
- An index and a selector `.N` refer to an element, and `len` refers to its array. They charge
  no size, so a binding of the result is a copy. A string is the exception: its index and its
  `len` scan it, so they charge its size, and the index makes a new string. An index with two
  or more arguments is `S010` before its operands run.
- Each new container checks its depth before the charge of its size (`S015`). These are the
  literals, the tuple and array types, and `[]` at its typed use.
- `()` charges the size 1 as a value and as a type.
- A record constructor `P[8](a, b)` charges the copies of its arguments. Then it makes the typed
  use of each field in declaration order (`S010` and `S012`), and it charges its size. In this
  phase a field holds only a static value: a hardware argument is `S010`. A struct type of a
  local or of a `type` item checks the number of its arguments here (`S007`).
- `==` on two records needs one struct type. The join of the two types charges as a type
  equality. Then the operator charges the sum of the two sizes.
- A field `.f` refers to the field, so it charges no size. A missing field is `S010`.
- `T()` is the zero of a hardware data type, also of a struct type. Another type is `S010`. The
  zero checks its depth (`Ty.zeroDepth`) and charges its size from the metadata before it exists.
- An assignment to a place with indices, selectors `.N`, and fields evaluates its indices from
  left to right. Each index checks when it evaluates: its stage (`S011`), the container and its own
  type (`S010`), then its range (`S013`). Then the right side evaluates, with the element type
  as its type. The update copies only the containers on the path of the place, so it charges
  nothing more. A binding that shares a container paid its copy before.
-/
namespace Silicon.Source.Eval

open Resolve Names

/-!
The typed use of a container `v` at `t`, element by element. The result is the size of the
converted value and the conversion. A shape or a scalar type that differs is `S010` before the
charge. A value that does not fit is `S012` in the conversion, after the charge.
-/
mutual
  def plan : Ty → Value → Except Fault (Nat × (Unit → Except Fault Value))
    | .array t n, v@(.array _ ⟨xs⟩) =>
      if xs.length = n then do
        let (k, f) ← planEach t xs
        .ok (1 + k, fun u => do return .array t (← f u).toArray)
      else typeError s!"expected {(Ty.array t n).text}, but the value is {v.text}"
    | .list t, .list _ ⟨xs⟩ => do
      let (k, f) ← planEach t xs
      .ok (1 + k, fun u => do return .list t (← f u).toArray)
    | .tuple ⟨ts⟩, v@(.tuple ⟨xs⟩) =>
      if ts.length = xs.length then do
        let (k, f) ← planZip ts xs
        .ok (1 + k, fun u => do return .tuple (← f u).toArray)
      else typeError s!"expected {(Ty.tuple ⟨ts⟩).text}, but the value is {v.text}"
    | t, v => do
      let s ← convertLeaf t v
      .ok (leafSize t v, s.run)

  def planEach (t : Ty) : List Value → Except Fault (Nat × (Unit → Except Fault (List Value)))
    | [] => .ok (0, fun _ => .ok [])
    | x :: xs => do
      let (k, f) ← plan t x
      let (ks, fs) ← planEach t xs
      .ok (k + ks, fun u => do return (← f u) :: (← fs u))

  def planZip : List Ty → List Value → Except Fault (Nat × (Unit → Except Fault (List Value)))
    | t :: ts, x :: xs => do
      let (k, f) ← plan t x
      let (ks, fs) ← planZip ts xs
      .ok (k + ks, fun u => do return (← f u) :: (← fs u))
    | _, _ => .ok (0, fun _ => .ok [])
end

/-!
A typed use of `v` at the type `t`. A value of the type `t` charges nothing. Another container
charges its size plus the size of the result, as a scalar conversion does.
-/
def convert (t : Ty) (v : Value) : Except Fault Step :=
  match t with
  | .unit | .array .. | .tuple _ | .list _ =>
    if v.ty? = some t then .ok ⟨0, fun _ => .ok v⟩
    else do
      let (k, f) ← plan t v
      .ok ⟨v.size + k, f⟩
  | _ => convertLeaf t v

/-!
The common type of the elements of an array literal, if they have one. It joins the type of each
element after the first with the join of the earlier elements.
-/
def commonOf : List Value → Walk (Option Ty)
  | [] => return none
  | v :: vs => vs.foldlM (init := v.ty?) fun t w => do
    match t, w.ty? with
    | some t, some u => joinTy t u
    | _, _ => return none

/-! A container: `()`, an array, a tuple, a record, or a list. -/
def composite : Value → Bool
  | .unit | .array .. | .tuple _ | .record .. | .list .. => true
  | _ => false

/-! `==` on two scalars in a container. A static integer takes the finite type of the other. -/
def leafEq (a b : Value) : Except Fault (Unit → Except Fault Bool) :=
  let cmp (x y : Value) : Except Fault Bool := do return (← equal x y) ()
  match a, b, a.finiteTy?, b.finiteTy? with
  | .int _, _, _, some t => do
    let s ← convertLeaf t a
    .ok fun u => do cmp (← s.run u) b
  | _, .int _, some t, _ => do
    let s ← convertLeaf t b
    .ok fun u => do cmp a (← s.run u)
  | _, _, _, _ => do
    let r ← equal a b
    .ok fun u => .ok (r u)

/-!
The type check of `==` on containers, by the operand rule for each pair of elements, and the
comparison for the step after the charge. Each pair compares, so each conversion checks its
fit.
-/
mutual
  def same : Value → Value → Walk (Unit → Except Fault Bool)
    | .unit, .unit => return fun _ => .ok true
    | a@(.array s ⟨xs⟩), b@(.array t ⟨ys⟩) => do
      let j ← joinTy s t
      if j.isSome && xs.length == ys.length then sameAll xs ys
      else throw (.S010, s!"`==` needs a common type, not {a.text} and {b.text}")
    | a@(.tuple ⟨xs⟩), b@(.tuple ⟨ys⟩) =>
      if xs.length == ys.length then sameAll xs ys
      else throw (.S010, s!"`==` needs a common type, not {a.text} and {b.text}")
    | a@(.list s ⟨xs⟩), b@(.list t ⟨ys⟩) => do
      let j ← joinTy s t
      if j.isNone then throw (.S010, s!"`==` needs a common type, not {a.text} and {b.text}")
      else if xs.length == ys.length then sameAll xs ys
      else return fun _ => .ok false
    | a@(.record s ⟨xs⟩), b@(.record t ⟨ys⟩) => do
      let j ← joinTy s t
      if j.isSome then sameAll xs ys
      else throw (.S010, s!"`==` needs a common type, not {a.text} and {b.text}")
    | a, b =>
      if composite a || composite b then
        throw (.S010, s!"`==` needs a common type, not {a.text} and {b.text}")
      else
        match leafEq a b with
        | .ok r => return r
        | .error f => throw f

  def sameAll : List Value → List Value → Walk (Unit → Except Fault Bool)
    | x :: xs, y :: ys => do
      let r ← same x y
      let rs ← sameAll xs ys
      return fun u => do
        let a ← r u
        let b ← rs u
        return a && b
    | _, _ => return fun _ => .ok true
end

/-!
A binary operator with a container operand at `pos`. `==` and `!=` charge the visits of their
joins, then they read both operands in full, so they charge the sum of the sizes. The orderings
take no container.
-/
def containerOp (pos : Pos) (op : BinOp) (a b : Value) : M Value :=
  match op with
  | .eq | .ne => do
    let r ← walked pos (same a b)
    apply pos (.ok ⟨a.size + b.size, fun u => do
      let x ← r u
      return .bool (if op == .eq then x else !x)⟩)
  | .lt | .le | .gt | .ge => lift pos (typeError s!"`{op.text}` takes no container")
  | _ => lift pos (typeError s!"`{op.text}` does not accept {a.text} and {b.text}")

def conform (pos : Pos) (t : Ty) (v : Value) : M Value := apply pos (convert t v)

/-!
An element of a container literal at `pos`, and the position of its first `[]` if it waits for
its type. In this phase a container holds only static values. A hardware value is `S010`, and a
handle is `S010` until slice 3.
-/
def element (pos : Pos) : Val → M (Part × Option Pos)
  | .static v => pure (.value v, none)
  | .pending q p => pure (p, some q)
  | .hw _ | .agg _ => fail .S010 pos "a container holds only static values in this phase"
  | .handle h => fail .S010 pos s!"{(Val.handle h).text} is not an element before slice 3"

/-! The value of an element of a container in this phase. -/
def item (pos : Pos) (v : Val) : M Value := do
  match ← element pos v with
  | (.value v, _) => pure v
  | (_, q) => fail .S010 (q.getD pos) "`[]` needs the type [T; 0] from its context"

/-! The first `[]` of the elements of a literal that waits for its type. -/
def waiting (es : List (Part × Option Pos)) : Option Pos := (es.filterMap (·.2)).head?

/-! The values of the elements of a literal that does not wait. -/
def values (es : List (Part × Option Pos)) : List Value :=
  es.filterMap fun | (.value v, _) => some v | _ => none

/-! A tuple literal at `pos`: its depth, then the charge of its size. -/
def tupleOf (pos : Pos) (vs : List Value) : M Value := do
  let v := Value.tuple vs.toArray
  bounded pos v.depth
  charge pos v.size
  return v

/-!
An array literal at `pos`. Its elements take their common type. Then it checks its depth and
charges its size.
-/
def arrayOf (pos : Pos) (vs : List Value) : M Value := do
  let some t ← walked pos (commonOf vs)
    | fail .S010 pos "the elements of an array have no common type"
  let xs ← vs.mapM (conform pos t)
  let v := Value.array t xs.toArray
  bounded pos v.depth
  charge pos v.size
  return v

/-!
A literal that waits, at a typed use of the type `t` at `pos`. The type flows into each
element: `[]` takes the type `[T; 0]`, and a literal of the shape of `t` makes its elements at
the element types of `t`. Then the literal charges as it does at its node. Another shape is
`S010` at `pos`.
-/
mutual
  def build (pos : Pos) (t : Ty) : Part → M Value
    | .value v => pure v
    | p@(.empty q) =>
      match t with
      | .array e 0 => do
        bounded q (Value.array e #[]).depth
        return .array e #[]
      | _ => fail .S010 pos s!"expected {t.text}, but the value is {p.text}"
    | p@(.array q ps) =>
      match t with
      | .array e k =>
        if ps.length = k then do arrayOf q (← buildAll pos e ps)
        else fail .S010 pos s!"expected {t.text}, but the value is {p.text}"
      | _ => fail .S010 pos s!"expected {t.text}, but the value is {p.text}"
    | p@(.tuple q ps) =>
      match t with
      | .tuple ⟨ts⟩ =>
        if ps.length = ts.length then do tupleOf q (← buildZip pos ts ps)
        else fail .S010 pos s!"expected {t.text}, but the value is {p.text}"
      | _ => fail .S010 pos s!"expected {t.text}, but the value is {p.text}"

  def buildAll (pos : Pos) (t : Ty) : List Part → M (List Value)
    | [] => pure []
    | p :: ps => do return (← build pos t p) :: (← buildAll pos t ps)

  def buildZip (pos : Pos) : List Ty → List Part → M (List Value)
    | t :: ts, p :: ps => do return (← build pos t p) :: (← buildZip pos ts ps)
    | _, _ => pure []
end

/-! A typed use of the type `t` at `pos` gives a literal that waits its type. -/
def settle (pos : Pos) (t : Ty) : Val → M Val
  | .pending _ p => do return .static (← build pos t p)
  | v => pure v

/-!
The selector `.i` at `pos`, with its number literal at `q`. The result is the number of the
element and the element.
-/
def selectAt (pos q : Pos) (i : Nat) : Val → M (Nat × Value)
  | .static v@(.tuple xs) =>
    match xs[i]? with
    | some x => pure (i, x)
    | none => fail .S013 q s!"the selector {i} is out of range for {v.text}"
  | v => fail .S010 pos s!"the selector `.{i}` needs a tuple, not {v.text}"

/-! The selector `.i` refers to an element. -/
def select (pos q : Pos) (i : Nat) (v : Val) : M Val := do
  return .static (← selectAt pos q i v).2

/-! The value of a static index at `q`. It is a static `Int` or `UInt`, else `S010`. -/
def indexOf (q : Pos) : Value → M Int
  | .int k => pure k
  | .uint _ x => pure (x.toNat : Int)
  | i => fail .S010 q s!"an index is a static integer, not {i.text}"

/-!
The static index `i` at `q` of an array, a list, or a tuple at `pos`. The result is the number
of the element and the element.
-/
def pickAt (pos q : Pos) (v : Val) (i : Value) : M (Nat × Value) := do
  let xs ← match v with
    | .static (.array _ xs) | .static (.tuple xs) | .static (.list _ xs) => pure xs
    | v => fail .S010 pos s!"an index needs an array, a list, or a tuple, not {v.text}"
  let k ← indexOf q i
  if h : 0 ≤ k ∧ k.toNat < xs.size then return (k.toNat, xs[k.toNat])
  else fail .S013 q s!"the index {intText k} is out of range for {xs.size} element(s)"

/-!
The static index `i` at `q` of the string `s` at `pos`: a string with the scalar `i` of `s`. A
UTF-8 string needs a scan, so the index charges the size of `s`. The charge comes after the type
check of the index and before its range check (section 5.4).
-/
def strAt (pos q : Pos) (s : String) (i : Value) : M Value := do
  let k ← indexOf q i
  charge pos (Value.str s).size
  match if 0 ≤ k then s.toList[k.toNat]? else none with
  | some c => return .str (String.singleton c)
  | none => fail .S013 q s!"the index {intText k} is out of range for {s.length} scalar(s)"

/-! A static index refers to an element. -/
def pick (pos q : Pos) (v : Val) (i : Value) : M Val := do
  return .static (← pickAt pos q v i).2

/-! The type of the element `k` of a container type. -/
def partTy : Ty → Nat → Option Ty
  | .array e _, _ | .list e, _ => some e
  | .tuple ts, k => ts[k]?
  | _, _ => none

/-!
A step of a place after its root: an index at `pos`, a selector `.i` with its literal at `q`, or
a field `.f`.
-/
inductive Sel where
  | index (pos : Pos) (args : List Resolve.Expr)
  | select (pos q : Pos) (i : Nat)
  | field (pos : Pos) (f : Ident)

/-! The position of the node of a step, where the step charges. -/
def Sel.pos : Sel → Pos
  | .index p _ | .select p _ _ | .field p _ => p

/-! The root of a place and its steps from the root outward. Another target has no place. -/
def chain (e : Resolve.Expr) (acc : List Sel := []) : Option (Resolve.Expr × List Sel) :=
  match e with
  | .index p b xs => chain b (.index p xs :: acc)
  | .select p b q i => chain b (.select p q i :: acc)
  | .field p b f => chain b (.field p f :: acc)
  | .name .. => some (e, acc)
  | _ => none

/-!
The value `v` with `f` applied to the element at the numbers `ks`. Each step copies only the
container that it changes, so a part that another binding shares stays unchanged.
-/
def update (f : Value → Value) : Value → List Nat → Value
  | v, [] => f v
  | .array t xs, k :: ks => .array t (xs.modify k (update f · ks))
  | .tuple xs, k :: ks => .tuple (xs.modify k (update f · ks))
  | .record t xs, k :: ks => .record t (xs.modify k (update f · ks))
  | .list t xs, k :: ks => .list t (xs.modify k (update f · ks))
  | v, _ :: _ => v

/-!
The field `f` of a record at `pos`. The result is the number of the field, its value, and its
type. A field selection refers to the field, so it charges no size. The record type holds the
number of its specialization, and the symbol of `f` finds the number of the field, so the
selection compares no name.
-/
def fieldAt (pos : Pos) (f : Ident) : Val → M (Nat × Value × Ty)
  | .static v@(.record t xs) => do
    let some (i, fs) := fieldsIn (← get).specs t
      | fail .S010 pos s!"{v.text} has no specialization"
    let some (.struct ..) := (← read).items[i]?
      | fail .S010 pos s!"{v.text} has no struct item"
    let c ← read
    let found := do
      let k ← c.field f.pos >>= fun x => c.syms.members[i]? >>= (·[x]?)
      return (k, ← xs[k]?, ← fs[k]?)
    match found with
    | some r => return r
    | none => fail .S010 pos s!"{v.text} has no field `{f.name}`"
  | v => fail .S010 pos s!"{v.text} has no field `{f.name}`"

/-!
A record constructor of the struct type `t` with the field types `fs` at `pos`. The arguments
`vs` at the positions `ps` paid their copies. Each field is a typed use in declaration order. A
literal with `[]` takes the type of its field. In this phase a field holds only a static value,
so a hardware argument is `S010` at the argument. Then the record checks its depth and charges
its size.
-/
def recordOf (pos : Pos) (t : Ty) (fs : List Ty) (ps : List Pos) (vs : List Val) : M Value := do
  let xs ← (fs.zip (ps.zip vs)).mapM fun (ft, q, v) => do
    conform pos ft (← item q (← settle pos ft v))
  let r := Value.record t xs.toArray
  bounded pos r.depth
  charge pos r.size
  return r

/-!
The zero `T()` of the type `t` at `pos` (section 5.6). A type that is not hardware data is
`S010`. The zero checks its depth and charges its size from the metadata before it exists.
-/
def zero (pos : Pos) (t : Ty) : M Value := do
  unless t.info.data do fail .S010 pos s!"a zero `T()` needs a hardware data type, not {t.text}"
  bounded pos t.zeroDepth
  charge pos t.info.zeroSize
  match zeroOf (← get).specs t.depth t with
  | some v => return v
  | none => fail .S010 pos s!"{t.text} has no zero"

/-!
The normal form of the aggregate `a` at `pos` (section 5.1). A reference without a hardware leaf
is a static value, for example a part of the type `[Unit; 4]`. It charges the zero size of its
type from the metadata before the value exists (section 5.4). A reference of a scalar type is a
hardware value. Another part keeps its form.
-/
def normalize (pos : Pos) : Agg → M Val
  | .static v => pure (.static v)
  | .hw h => pure (.hw h)
  | a@(.ref b t) =>
    if t.info.leaves = 0 then do
      charge pos t.info.zeroSize
      match zeroOf (← get).specs t.depth t with
      | some v => return .static v
      | none => fail .S010 pos s!"{t.text} has no zero"
    else if t matches .bool | .uint _ | .sint _ then return .hw (.mk pos t b.op [])
    else return .agg a
  | a => pure (.agg a)

/-!
`len` of an array, a list, or a string at the call `pos`. It refers to an array or a list, so
it charges no size. A string needs a scan, so it charges the size of the string first.
-/
def lenOf (pos : Pos) : List Val → M Value
  | [v] => do
    match ← data pos v with
    | .static (.array _ xs) | .static (.list _ xs) => return .int xs.size
    | .static v@(.str s) => do
      charge pos v.size
      return .int s.length
    | v => fail .S010 pos s!"`len` takes an array, a list, or a string, not {v.text}"
  | vs => fail .S007 pos s!"`len` takes 1 argument(s), but it has {vs.length}"

end Silicon.Source.Eval
