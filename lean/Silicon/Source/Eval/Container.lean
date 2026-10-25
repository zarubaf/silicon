-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Types

/-!
The static containers of the evaluator. These are the typed use of a container, the common type,
`==` on containers, and the literals with their depth and their charge. The literals that wait
for their type, the index, the selector `.N`, `len`, and the places of an assignment are here too.
So are the records of section 5.6: the constructor, the field `.f`, and the zero `T()`.

The static containers of slice 2 follow section 5.1. These rules settle its open points:

- An element of a literal and a field of a record are static values, hardware values, or
  hardware aggregates (section 5.1). A literal with a hardware part makes an aggregate node. It
  checks its depth and charges its size as a static literal does. A handle as an element is
  `S010` until slice 3. A list holds no value with a hardware leaf (`S011`).
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
  use of each field in declaration order (`S010` and `S012`), and it charges its size. An
  argument is in a data context, so a register or a wire is read (section 9.2). A struct type of
  a local or of a `type` item checks the number of its arguments here (`S007`).
- `==` on two records needs one struct type. The join of the two types charges as a type
  equality. Then the operator charges the sum of the two sizes.
- A field `.f` refers to the field, so it charges no size. A missing field is `S010`.
- A hardware aggregate (section 5.1) takes an index, a selector `.N`, and a field `.f` as a static
  container does. An element of a container node keeps its normal form, so the selection refers
  to it. An implicit read of an aggregate register, wire, or output, and an aggregate child
  output, give a lazy reference with no charge. A step on a reference gives a reference to the
  part, in a number of steps that the path bounds. Thus `p[i]` takes the same work for a huge
  array type. A part without a hardware leaf is a static value: it charges its zero size from
  the metadata first (`normalize`). A hardware index stays `S011`. The word of a memory is a
  reference with a bit offset (section 7.6). A step adds the offset of the part from the widths
  in the metadata (`Base.sub`), so a leaf of a word refers to its bits.
- A typed use of a hardware aggregate checks a reference by its type in one step, so it never
  expands. The other parts check first: a hardware leaf needs the type of its position, and a
  static leaf its sign. Then the conversion charges, and the static leaves convert.
- A place update copies only the nodes on its path. A reference on the path expands one level.
  A static part on the path that takes a value with a hardware leaf opens one level.
- `T()` is the zero of a hardware data type, also of a struct type. Another type is `S010`. The
  zero checks its depth (`Ty.zeroDepth`) and charges its size from the metadata before it exists.
- A static enum payload packs into one bit buffer of `P` bits (`Bits`, `Value.pack`). Each leaf
  writes its words at its offset, so no step reads an earlier leaf. A node of an enum type with
  only static parts is a static enum value (`Agg.mkRecord`), and a static enum opens into its
  parts `tag` and `payload` (`Agg.opened`).
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
def commonOf : List (Option Ty) → Walk (Option Ty)
  | [] => return none
  | v :: vs => vs.foldlM (init := v) fun t w => do
    match t, w with
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
fit. Two static enums of one type are equal when their tags and payloads are equal. `==` never
reaches them (the enum flag), but the static pair of a hardware `if` compares them here.
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
    | a@(.enum s ..), b@(.enum t ..) => do
      let j ← joinTy s t
      if j.isSome then return fun _ => .ok (a == b)
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
The part of the type `t` of the base `b` at `pos` in its normal form (section 5.1), with no
charge. A part without a hardware leaf is the static zero of its type, for example a part of the
type `[Unit; 4]`. A part of a scalar type is a hardware value. Another part is a reference.
-/
def Agg.part (specs : Specs) (pos : Pos) (b : Base) (t : Ty) : Option Agg :=
  if t.info.leaves = 0 then (zeroOf specs t.depth t).map .static
  else if t matches .bool | .uint _ | .sint _ then some (.hw (.mk pos t b.op []))
  else some (.ref b t)

/-!
The normal form of the aggregate `a` at `pos` (section 5.1). A reference without a hardware leaf
checks the size limit before the static value exists (section 5.4). Then it charges the zero
size of its type from the metadata. Another part keeps its form.
-/
def Agg.normal (pos : Pos) : Agg → M Agg
  | .ref b t => do
    if t.info.leaves = 0 then
      if over t.info.zeroSize then fail .S015 pos zeroLimitText
      charge pos t.info.zeroSize
    match Agg.part (← get).specs pos b t with
    | some a => return a
    | none => fail .S010 pos s!"{t.text} has no zero"
  | a => pure a

/-! The normal form of the aggregate `a` at `pos` as a value (`Agg.normal`). -/
def normalize (pos : Pos) (a : Agg) : M Val := do
  return (← Agg.normal pos a).val

/-!
A read at `pos` of the name `b` of the type `t`: a port, a register, a wire, or a child output
(section 5.5). The read makes a value of the depth of a zero of `t`, so it checks this depth
first (`S015`), as `T()` does. A read of a leaf in a container adds the `above` nodes over the
leaf to this depth (section 5.4). Then it gives the reference in its normal form. A selection of
the reference has a smaller depth, so it makes no check.
-/
def readAgg (pos : Pos) (b : Base) (t : Ty) (above : Nat := 0) : M Agg := do
  bounded pos (above + t.zeroDepth)
  Agg.normal pos (.ref b t)

/-! The read of `readAgg` as a value. -/
def readRef (pos : Pos) (b : Base) (t : Ty) (above : Nat := 0) : M Val := do
  return (← readAgg pos b t above).val

/-! The fix `{h}` of the `S010` text of `read` (section 6.2), by the kind of the value. -/
def readHint : Val → String
  | .handle (.mem ..) => "read a word with `read_port`"
  | .handle (.inst ..) => "read an output of the instance, for example `u.q`"
  | .handle (.domain _) => "a domain has no value, so remove the `read`"
  | _ => "use the value directly, without `read`"

/-!
The `S017` text "`read` of an input" of the input `q` of the child at `path` (section 6.2). The
public name of the input has the limit of a string in a message (section 5.5).
-/
def inputText (path : Path) (q : Port) : String :=
  s!"the input `{strText q.text}` of `{sourceOf path}` is a target only; read the value that " ++
    "you bind to it"

/-!
The read of the handle `h` at `pos` in a `data` context, under `above` nodes of a container
(section 5.4). A register, a wire, and an own output read by `readRef`, so the depth check
comes first. A child input is never read (`S017`). A memory and an instance are not data
(`S010`), and their texts of section 6.2 name the fix. A domain is not data.
-/
def readHandle (pos : Pos) (above : Nat) : Handle → M Agg
  | .res _ _ ty path => readAgg pos (.name path) ty above
  | .input _ path q => fail .S017 pos (inputText path q)
  | h@(.mem _ path ..) =>
    fail .S010 pos s!"`{sourceOf path}` is a memory, not data; {readHint (.handle h)}"
  | .inst _ path .. =>
    let r := sourceOf path
    fail .S010 pos s!"`{r}` is an instance, not data; read its outputs as `{r}.q`"
  | h => fail .S010 pos s!"{(Val.handle h).text} is not data"

/-!
The data of a value at a use that only selects from it. These uses are the base of an index, of
a selector, and of a field, and the argument of `len`. A register, a wire, and an own output
give a reference to their name, in its normal form (`readRef`). Thus a scalar gives a hardware
value, and an aggregate a lazy reference with no charge (section 9.2). A container of handles
passes, so the selection reads only the part that it selects.
-/
def baseData (pos : Pos) : Val → M Val
  | .pending q _ => fail .S010 q "`[]` needs the type [T; 0] from its context"
  | .handle h => do return (← readHandle pos 0 h).val
  | v => pure v

/-!
The data type of a type with the handle flag: each `Reg[T]` and `Wire[T]` in an array or a
tuple becomes `T`. A read of a container of handles gives a value of this type (section 5.4).
Another type stays.
-/
mutual
  def dataTy : Ty → Ty
    | .reg t | .wire t => t
    | .array t n => .array (dataTy t) n
    | .tuple ⟨ts⟩ => .tuple ⟨dataTys ts⟩
    | t => t

  def dataTys : List Ty → List Ty
    | [] => []
    | t :: ts => dataTy t :: dataTys ts
end

/-! The text of a node of handles in a `data` context (section 6.2). -/
def handlesText (n : Node) : Agg → String
  | .list .. => s!"a `data` context does not read the list of handles `{n.ty.text}`; read each " ++
    "element, for example `read(hs[0])`"
  | _ => s!"a `data` context does not read the record of handles `{n.ty.text}`; construct the " ++
    "data record from the fields, for example `P(read(h.a), read(h.b))`"

/-!
The read at `pos` of the part `a` of a container of handles, under `above` nodes (section 5.4).
The caller charged the recursive size of the root. The walk visits the parts in packing order.
It does not enter a part of a type without the handle flag, because that part is data already.
A record node of handles and a list node are `S010`. A handle leaf reads by `readHandle`, so its
depth check comes first. Then a reference charges the zero size of its type, before it goes into
the result. The result is a new value.
-/
mutual
  def readPart (pos : Pos) (above : Nat) : Agg → M Agg
    | .handle h => do
      let a ← readHandle pos above h
      if a.val matches .agg _ then charge pos a.size
      return a
    | a@(.array n ⟨xs⟩) =>
      match n.ty with
      | .array e _ =>
        if e.info.handles then do
          return .mkArray (dataTy e) (← readParts pos (above + 1) xs).toArray
        else pure a
      | _ => pure a
    | a@(.tuple n ⟨xs⟩) =>
      match n.ty with
      | .tuple ⟨ts⟩ =>
        if n.ty.info.handles then do
          return .mkTuple ⟨dataTys ts⟩ (← readParts pos (above + 1) xs).toArray
        else pure a
      | _ => pure a
    | a@(.record n _) =>
      if n.ty.info.handles then fail .S010 pos (handlesText n a) else pure a
    | a@(.list n ..) => fail .S010 pos (handlesText n a)
    | a => pure a

  def readParts (pos : Pos) (above : Nat) : List Agg → M (List Agg)
    | [] => pure []
    | x :: xs => do return (← readPart pos above x) :: (← readParts pos above xs)
end

/-!
The text "Handles as data" of section 6.2 for a value of the type `t`.
-/
def handlesDataText (t : Ty) : String :=
  s!"a `data` context does not read `{t.text}`, a type that holds a memory, an instance, or an " ++
    "input; read the data of each element"

/-!
The data of a value at a use that reads it: the implicit read (section 9.2). A handle reads by
`readHandle`. A container of a type with the handle flag charges its recursive size first.
Then each leaf reads in packing order (`readPart`), and the error is at `pos`. An empty
container of memories, instances, or inputs has no leaf to report at. Thus a result that keeps
the flag is `S010` with the text "Handles as data". The check reads the flag of the result type.
Another value is data already.
-/
def data (pos : Pos) : Val → M Val
  | .agg a => do
    let some t := a.ty? | return .agg a
    unless t.info.handles do return .agg a
    charge pos a.size
    let r ← readPart pos 0 a
    if r.ty?.any (·.info.handles) then fail .S010 pos (handlesDataText t)
    return r.val
  | v => baseData pos v

/-!
The data of a value at a typed use at the type `t`. A position of a type with the handle flag
is `raw` (section 9.2), so it reads nothing: a handle and a container keep their handles. A
position of another type reads each handle (`data`).
-/
def dataAt (pos : Pos) (t : Ty) (v : Val) : M Val :=
  if t.info.handles then pure v else data pos v

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

/-! The `S010` text "Field of an enum" of section 6.2, for the enum type `t` and the field `f`. -/
def enumFieldText (t : Ty) (f : String) : String :=
  s!"`{t.text}` is an enum and has no field `{f}`; read a payload with `match`, or the bits " ++
    s!"with `reinterpret(UInt[{t.info.width}], e)`"

/-!
A field `.f` or a selector `.N` at `pos` of a part of the type `t` is `S010` when `t` is an enum.
Section 6.2 gives the text. An enum has the leaves `tag` and `payload`, but no field (section
5.1). `f` is the field name or the number of the selector. The text names `data_bits` of the
enum, the width of its metadata. Another type passes.
-/
def noEnumField (pos : Pos) (f : String) (t : Option Ty) : M Unit := do
  if let some t@(.enum ..) := t then fail .S010 pos (enumFieldText t f)

/-!
The selector `.i` refers to an element. A selector of a reference to a tuple gives a reference
to the element `<i>e`. The result is the number of the element and the element. An enum has no
element (`noEnumField`).
-/
def selectKey (pos q : Pos) (i : Nat) (v : Val) : M (Nat × Val) := do
  noEnumField pos (toString i) v.ty?
  match v with
  | v@(.agg (.tuple _ xs)) =>
    match xs[i]? with
    | some x => do return (i, ← normalize pos x)
    | none => fail .S013 q s!"the selector {i} is out of range for {v.text}"
  | v@(.agg (.ref b r@(.tuple ts))) =>
    match ts[i]? with
    | some t => do
      return (i, ← normalize pos (.ref (b.sub (partsIn (← get).specs) r i (.elem i)) t))
    | none => fail .S013 q s!"the selector {i} is out of range for {v.text}"
  | v => do
    let (k, w) ← selectAt pos q i v
    return (k, .static w)

def select (pos q : Pos) (i : Nat) (v : Val) : M Val := do return (← selectKey pos q i v).2

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
/--
The charge at `pos` for the scan of the string `v`. A charge above the fuel names no count: the
Rust front end does not count the scalars of a string that the fuel cannot pay.
-/
def chargeScan (pos : Pos) (v : Value) : M Unit :=
  chargeWith pos v.size fun left =>
    s!"the fuel cannot pay the scan of the string; {intText left} remain; raise --fuel"

def strAt (pos q : Pos) (s : String) (i : Value) : M Value := do
  let k ← indexOf q i
  chargeScan pos (Value.str s)
  match if 0 ≤ k then s.toList[k.toNat]? else none with
  | some c => return .str (String.singleton c)
  | none => fail .S013 q s!"the index {intText k} is out of range for {s.length} scalar(s)"

/-! The number of the static index `i` at `q` in a container with `n` elements. -/
def within (q : Pos) (n : Nat) (i : Value) : M Nat := do
  let k ← indexOf q i
  if 0 ≤ k ∧ k.toNat < n then return k.toNat
  else fail .S013 q s!"the index {intText k} is out of range for {n} element(s)"

/-!
A static index refers to an element. An index of a list node refers to its element too (section
5.4). An index of a reference to an array or a tuple gives a reference to the element `<k>e`.
Its type gives the length, so a huge array takes no more work. The result is the number of the
element and the element.
-/
def pickKey (pos q : Pos) (v : Val) (i : Value) : M (Nat × Val) := do
  match v with
  | .agg (.array _ xs) | .agg (.tuple _ xs) | .agg (.list _ _ xs) =>
    let k ← within q xs.size i
    match xs[k]? with
    | some x => return (k, ← normalize pos x)
    | none => fail .S013 q s!"the index is out of range for {xs.size} element(s)"
  | .agg (.ref b r@(.array e n)) => do
    let k ← within q n i
    return (k, ← normalize pos (.ref (b.sub (partsIn (← get).specs) r k (.elem k)) e))
  | .agg (.ref b r@(.tuple ts)) => do
    let k ← within q ts.size i
    match ts[k]? with
    | some t => return (k, ← normalize pos (.ref (b.sub (partsIn (← get).specs) r k (.elem k)) t))
    | none => fail .S013 q s!"the index is out of range for {ts.size} element(s)"
  | v =>
    let (k, w) ← pickAt pos q v i
    return (k, .static w)

def pick (pos q : Pos) (v : Val) (i : Value) : M Val := do return (← pickKey pos q v i).2

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
The reference of the type `t` to the base `b`, expanded one level into references to its parts
in their normal form. The caller paid for the parts, so this has no charge. `fs` gives the named
parts of a struct type and of an enum type.
-/
def Agg.expand (fs : Ty → Option (Array (String × Ty))) (specs : Specs) (pos : Pos) (b : Base) :
    Ty → Option Agg
  | r@(.array e n) => do
    let sub (k : Nat) := b.sub (partsIn specs) r k (.elem k)
    return .mkArray e (← (Array.range n).mapM fun k => Agg.part specs pos (sub k) e)
  | r@(.tuple ts) => do
    let sub (k : Nat) := b.sub (partsIn specs) r k (.elem k)
    return .mkTuple ts (← ts.zipIdx.mapM fun (t, k) => Agg.part specs pos (sub k) t)
  | t@(.struct ..) | t@(.enum ..) => do
    let sub (k : Nat) (x : String) := b.sub (partsIn specs) t k (.user x)
    return .mkRecord t (← (← fs t).zipIdx.mapM fun ((x, ft), k) => Agg.part specs pos (sub k x) ft)
  | _ => none

/-!
The sum of the zero sizes of the empty parts on the path `ks` in a reference of the type
`t`. Each reference on the path expands one level (`Agg.expand`) and makes these parts. The
type metadata gives each zero size, so the sum makes no part. A part of a scalar type is a
hardware leaf, so the path ends there.
-/
def Ty.emptySize (specs : Specs) : Ty → List Nat → Nat
  | _, [] => 0
  | t, k :: ks =>
    let empty (p : Ty) := if p.info.leaves = 0 then p.info.zeroSize else 0
    let (here, p) := match t with
      | .array e n => (n * empty e, some e)
      | t =>
        let ps : Array Ty := match t with
          | .tuple ts => ts
          | t => ((specs.parts t).getD #[]).map Prod.snd
        ((ps.map empty).sum, ps[k]?)
    match p with
    | some p =>
      if p.info.leaves = 0 || p matches .bool | .uint _ | .sint _ then here
      else here + Ty.emptySize specs p ks
    | none => here

/-!
The type of the first reference on the path `ks` of the aggregate `a`. `Agg.set` expands it and
each reference in it, so its zero size bounds the parts that the expansion makes.
-/
def Agg.firstRef : Agg → List Nat → Option Ty
  | _, [] => none
  | .ref _ t, _ => some t
  | .array _ xs, k :: ks | .tuple _ xs, k :: ks | .record _ xs, k :: ks
  | .list _ _ xs, k :: ks =>
    match xs[k]? with
    | some x => Agg.firstRef x ks
    | none => none
  | _, _ => none

/-!
The sum of the zero sizes of the empty parts that `Agg.set` makes on the path `ks` of the
aggregate `a` (`Ty.emptySize`). Only a reference on the path makes parts.
-/
def Agg.emptySize (specs : Specs) : Agg → List Nat → Nat
  | _, [] => 0
  | .ref _ t, ks => Ty.emptySize specs t ks
  | .array _ xs, k :: ks | .tuple _ xs, k :: ks | .record _ xs, k :: ks
  | .list _ _ xs, k :: ks =>
    match xs[k]? with
    | some x => Agg.emptySize specs x ks
    | none => 0
  | _, _ => 0

/-!
The sum of the part counts of the container nodes on the path `ks` of the aggregate `a`. A change
of a static part copies each of these nodes (`Agg.change`), so this sum bounds the work of the
refresh. A list node above the end of the path counts too. The list node at the end of the path
changes by a delta (`Agg.change`), so it adds nothing (section 5.4). The path ends at the first
part that is not a container node.
-/
def Agg.pathWidth : Agg → List Nat → Nat
  | .array _ xs, k :: ks | .tuple _ xs, k :: ks | .record _ xs, k :: ks
  | .list _ _ xs, k :: ks =>
    xs.size + match xs[k]? with
      | some x => Agg.pathWidth x ks
      | none => 0
  | _, _ => 0

/-!
The aggregate `a` with a change of the list at the numbers `ks`. The change keeps each hardware
leaf. A static list changes by `f`, and a list node changes its elements by `g`. Each
container node on the path maps its stored size by `sz`. Its depth becomes at least `d` plus the
number of steps from the node to the end of the path. Thus each node refreshes in one step, and
the walk reads no sibling. A list node at the end of the path refreshes by the delta of one
element, so it reads no element (section 5.4). The caller makes these numbers exact.
`sz` adds or removes the size of one element. `d` is the depth that the list at the end of the
path can reach. A change that can lower a depth does not use this walk.
-/
def Agg.change (f : Value → Value) (g : Array Agg → Array Agg) (sz : Nat → Nat) (d : Nat) :
    Agg → List Nat → Option Agg
  | .static v, ks => some (.static (update f v ks))
  | .list n e xs, [] => some (.list { n with size := sz n.size, depth := max n.depth d } e (g xs))
  | .array n xs, k :: ks => do
    let x ← Agg.change f g sz d (← xs[k]?) ks
    return .array (refresh n ks) (xs.set! k x)
  | .tuple n xs, k :: ks => do
    let x ← Agg.change f g sz d (← xs[k]?) ks
    return .tuple (refresh n ks) (xs.set! k x)
  | .record n xs, k :: ks => do
    let x ← Agg.change f g sz d (← xs[k]?) ks
    return .record (refresh n ks) (xs.set! k x)
  | .list n e xs, k :: ks => do
    let x ← Agg.change f g sz d (← xs[k]?) ks
    return .list (refresh n ks) e (xs.set! k x)
  | _, _ => none
where
  refresh (n : Node) (ks : List Nat) : Node :=
    { n with size := sz n.size, depth := max n.depth (ks.length + 1 + d) }

/-!
The static container `v` opened one level: its elements as static parts, and the builder of its
node. A static enum opens into its parts `tag` and `payload` (section 7.4). A list never holds a
hardware leaf, so it does not open.
-/
def Agg.opened : Value → Option (Array Agg × (Array Agg → Agg))
  | .array e xs => some (xs.map .static, .mkArray e)
  | .tuple xs => do
    let ts ← Value.tyAll? xs.toList
    return (xs.map .static, .mkTuple ts.toArray)
  | .record t xs => some (xs.map .static, .mkRecord t)
  | .enum t w x p y => some ((Value.enumParts w x p y).map .static, .mkRecord t)
  | _ => none

/-!
The aggregate `a` with the part at the numbers `ks` replaced by `y`. Each step copies only the
node on the path. A reference on the path expands one level by `ex`. A static part on the path
opens one level when `y` has a hardware leaf (`Agg.opened`). Each node keeps its normal form,
so a node without a hardware leaf is a static value.
-/
def Agg.set (ex : Base → Ty → Option Agg) (y : Agg) : Agg → List Nat → Option Agg
  | _, [] => some y
  | a, k :: ks => do
    let a ← match a with
      | .ref b t => ex b t
      | a => pure a
    match a, y with
    | .static v, .static w => some (.static (update (fun _ => w) v (k :: ks)))
    | .static v, _ => do
      let (xs, mk) ← Agg.opened v
      return mk (xs.set! k (← Agg.set ex y (← xs[k]?) ks))
    | .array _ xs, _ | .tuple _ xs, _ | .record _ xs, _ | .list _ _ xs, _ => do
      return a.rebuild (xs.set! k (← Agg.set ex y (← xs[k]?) ks))
    | _, _ => none

/-!
The number and the type of the field with the symbol `y` of the struct type `t` at `pos`. `name`
is the name in a message, and `text` names the value. The record type holds the number of its
specialization, and the symbol finds the number of the field, so the selection compares no name.
No symbol is no field.
-/
def fieldBy (pos : Pos) (y : Option Nat) (name : String) (t : Ty) (text : String) :
    M (Nat × Ty) := do
  let specs := (← get).specs
  let (some i, some fs) := (specs.item t, specs.parts t)
    | fail .S010 pos s!"{text} has no specialization"
  let some (.struct ..) := (← read).items[i]?
    | fail .S010 pos s!"{text} has no struct item"
  let c ← read
  let found := do
    let k ← y >>= fun x => c.syms.members[i]? >>= (·[x]?)
    return (k, ← fs[k]?.map (·.2))
  match found with
  | some r => return r
  | none => fail .S010 pos s!"{text} has no field `{name}`"

/-!
The field with the symbol `y` of a record at `pos`, with the name `name` in a message (`fieldBy`).
The result is the number of the field, its value, and its type. A field selection refers to the
field, so it charges no size.
-/
def fieldAtBy (pos : Pos) (y : Option Nat) (name : String) : Val → M (Nat × Value × Ty)
  | .static v@(.record t xs) => do
    let (k, ft) ← fieldBy pos y name t v.text
    match xs[k]? with
    | some x => return (k, x, ft)
    | none => fail .S010 pos s!"{v.text} has no field `{name}`"
  | v => fail .S010 pos s!"{v.text} has no field `{name}`"

/-!
The field with the symbol `y` and the name `name` of a record or of a hardware aggregate. The
look-up and its errors are at `kp`, with the name `shown` in a message (`fieldBy`), and the
selection reads at `pos`. A field of a reference to a record gives a reference to the part with
the leaf field `name`. The result is the number of the field, its value, and its type. An enum
has no field (`noEnumField`).
-/
def fieldKeyBy (pos kp : Pos) (y : Option Nat) (name shown : String) (v : Val) :
    M (Nat × Val × Ty) := do
  noEnumField kp shown v.ty?
  match v with
  | v@(.agg (.record n xs)) => do
    let (k, ft) ← fieldBy kp y shown n.ty v.text
    match xs[k]? with
    | some x => return (k, ← normalize pos x, ft)
    | none => fail .S010 kp s!"{v.text} has no field `{shown}`"
  | v@(.agg (.ref b t@(.struct ..))) => do
    let (k, ft) ← fieldBy kp y shown t v.text
    return (k, ← normalize pos (.ref (b.sub (partsIn (← get).specs) t k (.user name)) ft), ft)
  | v => do
    let (k, w, ft) ← fieldAtBy kp y shown v
    return (k, .static w, ft)

/-! The field `f` of a record or of a hardware aggregate at `pos` (`fieldKeyBy`). -/
def fieldKey (pos : Pos) (f : Ident) (v : Val) : M (Nat × Val × Ty) := do
  fieldKeyBy pos pos ((← read).field f.pos) f.name f.name v

def field (pos : Pos) (f : Ident) (v : Val) : M Val := do return (← fieldKey pos f v).2.1

/-!
The zero `T()` of the type `t` at `pos` (section 5.6). A type that is not hardware data is
`S010`. The call rejects a handle type before (`ctor`). The zero checks its depth and the size
limit, and it charges its size from the metadata before it exists.
-/
def zero (pos : Pos) (t : Ty) : M Value := do
  unless t.info.data do
    fail .S010 pos (s!"a zero `T()` needs a hardware data type, not `{t.text}`; write a full " ++
      "value, for example a constructor with one value for each field")
  bounded pos t.zeroDepth
  if over t.info.zeroSize then fail .S015 pos zeroLimitText
  charge pos t.info.zeroSize
  match zeroOf (← get).specs t.depth t with
  | some v => return v
  | none => fail .S010 pos s!"{t.text} has no zero"

/-! A typed use of the aggregate `a` at `t` with another type is `S010`. -/
def Agg.wrong (t : Ty) (a : Agg) : Except Fault α :=
  typeError s!"expected {t.text}, but the value is {a.val.text}"

/-!
A part `a` at a position of the handle type `t` (section 5.4). It needs a handle of exactly this
type, else `S010` with the text "Typed use at a handle type", which names the leaf. The compare
has no charge, and nothing reads the handle.
-/
def Agg.handleAt (t : Ty) (a : Agg) : Except Fault (Nat × (Unit → Except Fault Agg)) :=
  match a with
  | .handle h => if h.ty?.any (·.same t) then .ok (1, fun _ => .ok a) else bad
  | _ => bad
where bad := typeError (handleUseText t a.val.about)

/-!
The typed use of the aggregate `a` at `t` (section 5.4), part by part. The result is the size of the
converted aggregate and the conversion. A reference checks by its type in one step, so it never
expands. A handle position needs a handle of its type (`Agg.handleAt`). A handle at another position
is `S010`, and nothing reads it: at a data type, its text "Handle at a data leaf" names the fix. A
hardware leaf needs the type of its position. A static part checks its type and its sign (`plan`).
All these checks come before the charge. A static value that does not fit its finite type is `S012`
in the conversion, after the charge. An array, a tuple, and a list of a type with the handle flag
walk part by part. A record compares the identity of its type, so the walk does not enter it.
-/
mutual
  def Agg.plan : Ty → Agg → Except Fault (Nat × (Unit → Except Fault Agg))
    | t@(.reg _), a | t@(.wire _), a | t@(.input _), a | t@(.mem ..), a | t@(.inst ..), a =>
      Agg.handleAt t a
    | t, a@(.ref _ u) => if u.same t then .ok (a.size, fun _ => .ok a) else Agg.wrong t a
    | t, a@(.hw h) => if h.ty.same t then .ok (a.size, fun _ => .ok a) else Agg.wrong t a
    | t, .static v => do
      let (k, f) ← Eval.plan t v
      .ok (k, fun u => do return .typed t (← f u))
    | .array e n, a@(.array _ ⟨xs⟩) =>
      if xs.length = n then do
        let (k, f) ← Agg.planEach e xs
        .ok (1 + k, fun u => do return .mkArray e (← f u).toArray)
      else Agg.wrong (.array e n) a
    | .tuple ⟨ts⟩, a@(.tuple _ ⟨xs⟩) =>
      if ts.length = xs.length then do
        let (k, f) ← Agg.planZip ts xs
        .ok (1 + k, fun u => do return .mkTuple ⟨ts⟩ (← f u).toArray)
      else Agg.wrong (.tuple ⟨ts⟩) a
    | .list e, a@(.list n _ ⟨xs⟩) =>
      if n.ty.same (.list e) then .ok (a.size, fun _ => .ok a) else do
        let (k, f) ← Agg.planEach e xs
        .ok (1 + k, fun u => do return .mkList e (← f u).toArray)
    | t, a@(.record n _) | t, a@(.list n ..) =>
      if n.ty.same t then .ok (a.size, fun _ => .ok a) else Agg.wrong t a
    | t, a@(.handle _) =>
      if t.info.handles then typeError (handleUseText t a.val.about)
      else typeError (dataLeafText t a.val.about)
    | t, a => Agg.wrong t a

  def Agg.planEach (t : Ty) : List Agg → Except Fault (Nat × (Unit → Except Fault (List Agg)))
    | [] => .ok (0, fun _ => .ok [])
    | x :: xs => do
      let (k, f) ← Agg.plan t x
      let (ks, fs) ← Agg.planEach t xs
      .ok (k + ks, fun u => do return (← f u) :: (← fs u))

  def Agg.planZip : List Ty → List Agg → Except Fault (Nat × (Unit → Except Fault (List Agg)))
    | t :: ts, x :: xs => do
      let (k, f) ← Agg.plan t x
      let (ks, fs) ← Agg.planZip ts xs
      .ok (k + ks, fun u => do return (← f u) :: (← fs u))
    | _, _ => .ok (0, fun _ => .ok [])
end

/-!
The typed use of the aggregate `a` at `t` at `pos` (section 5.4). An aggregate of the type `t`
charges nothing. Another one checks each part first (`Agg.plan`), then charges its size plus the
size of the result, then converts its static parts. Each new node checks its depth (`S015`).
-/
def typedAgg (pos : Pos) (t : Ty) (a : Agg) : M Agg := do
  if a.ty?.any (·.same t) then return a
  let (k, f) ← lift pos (Agg.plan t a)
  charge pos (a.size + k)
  let r ← lift pos (f ())
  bounded pos r.depth
  return r

/-!
The typed use of the part `a` of a container at `t` at `pos`. A static part converts, a hardware
leaf needs the type `t`, and a hardware aggregate converts part by part (`typedAgg`).
-/
def conformAgg (pos : Pos) (t : Ty) : Agg → M Agg
  | .static v => do return .typed t (← conform pos t v)
  | .hw h =>
    if h.ty.same t then pure (.hw h)
    else fail .S010 pos s!"expected {t.text}, but the value is {h.ty.text}"
  | a => typedAgg pos t a

/-!
An element of a container literal at `pos`, and the position of its first `[]` if it waits for
its type. An element is in the `raw` context (section 9.2), so a handle is a handle leaf. An own
output has no handle type, so it reads as data (`data`). A domain has no value, so it is `S010`,
with the text of section 6.2.
-/
def element (pos : Pos) : Val → M (Part × Option Pos)
  | .pending q p => pure (p, some q)
  | .handle (.domain x) =>
    fail .S010 pos (s!"the domain `{x}` is not an element; a domain has no value, so remove " ++
      "it from the literal")
  | v@(.handle (.res .output ..)) => do
    match (← baseData pos v).agg? with
    | some a => pure (.value a, none)
    | none => fail .S010 pos s!"{v.text} is not data"
  | .handle h => pure (.value (.handle h), none)
  | .static v => pure (.value (.static v), none)
  | .hw h => pure (.value (.hw h), none)
  | .agg a => pure (.value a, none)

/-! The part of a container that the value `v` at `pos` gives, after its typed use. -/
def item (pos : Pos) (v : Val) : M Agg := do
  match ← element pos v with
  | (.value v, _) => pure v
  | (_, q) => fail .S010 (q.getD pos) "`[]` needs the type [T; 0] from its context"

/-! The first `[]` of the elements of a literal that waits for its type. -/
def waiting (es : List (Part × Option Pos)) : Option Pos := (es.filterMap (·.2)).head?

/-! The values of the elements of a literal that does not wait. -/
def values (es : List (Part × Option Pos)) : List Agg :=
  es.filterMap fun | (.value v, _) => some v | _ => none

/-!
A new container node `a` at `pos`: its depth (`S015`), then the charge of its size. The builder
gives a node without a hardware leaf as a static value, so a static literal keeps its charges.
-/
def made (pos : Pos) (a : Agg) : M Agg := do
  bounded pos a.depth
  charge pos a.size
  return a

/-! A tuple literal at `pos` with the elements `xs`. -/
def tupleOf (pos : Pos) (xs : List Agg) : M Agg := do
  let some ts := xs.mapM Agg.ty? | fail .S010 pos "an element of the tuple has no type"
  made pos (.mkTuple ts.toArray xs.toArray)

/-!
An array literal at `pos`. Its elements take their common type by a typed use. Then it checks
its depth and charges its size.
-/
def arrayOf (pos : Pos) (xs : List Agg) : M Agg := do
  let some t ← walked pos (commonOf (xs.map Agg.ty?))
    | fail .S010 pos "the elements of an array have no common type"
  let ys ← xs.mapM (conformAgg pos t)
  made pos (.mkArray t ys.toArray)

/-!
A literal that waits, at a typed use of the type `t` at `pos`. The type flows into each
element: `[]` takes the type `[T; 0]`, and a literal of the shape of `t` makes its elements at
the element types of `t`. An empty array of a type with the handle flag is a node (section 5.1).
Then the literal charges as it does at its node. Another shape is `S010` at `pos`.
-/
mutual
  def build (pos : Pos) (t : Ty) : Part → M Agg
    | .value v => pure v
    | p@(.empty q) =>
      match t with
      | .array e 0 => do
        bounded q (Value.array e #[]).depth
        return .mkArray e #[]
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

  def buildAll (pos : Pos) (t : Ty) : List Part → M (List Agg)
    | [] => pure []
    | p :: ps => do return (← build pos t p) :: (← buildAll pos t ps)

  def buildZip (pos : Pos) : List Ty → List Part → M (List Agg)
    | t :: ts, p :: ps => do return (← build pos t p) :: (← buildZip pos ts ps)
    | _, _ => pure []
end

/-! A typed use of the type `t` at `pos` gives a literal that waits its type. -/
def settle (pos : Pos) (t : Ty) : Val → M Val
  | .pending _ p => do return (← build pos t p).val
  | v => pure v

/-!
The bit buffer of a static pack (section 5.1): its words of 64 bits, the least significant word
first, and the next free bit. A pack allocates one buffer for the payload width and writes each
leaf at its offset. Thus a leaf of `w` bits takes at most `w / 64 + 1` word steps, and no step
reads the earlier leaves. Each Lean step shifts a natural number; a Rust word takes O(1) work.
-/
structure Bits where
  words : Array UInt64
  next : Nat

/-! An empty buffer of `n` bits. -/
def Bits.new (n : Nat) : Bits := ⟨Array.replicate ((n + 63) / 64) 0, 0⟩

/-!
Writes the low `w` bits of `x` at the next free bit, one word of `x` for each step. The bits of
`x` above `w` are zero, so a word adds no bit after the leaf.
-/
def Bits.put (b : Bits) (w x : Nat) : Bits := Id.run do
  let mut ws := b.words
  let mut y := x
  let mut o := b.next
  for _ in [0:(w + 63) / 64] do
    let c := y.toUInt64
    let i := o / 64
    let s := o % 64
    ws := ws.modify i (· ||| (c <<< s.toUInt64))
    if s != 0 then ws := ws.modify (i + 1) (· ||| (c >>> (64 - s).toUInt64))
    y := y >>> 64
    o := o + 64
  return ⟨ws, b.next + w⟩

/-! The number of the bits of the buffer, the first word in the low bits. -/
def Bits.toNat (b : Bits) : Nat := b.words.foldr (fun w acc => (acc <<< 64) ||| w.toNat) 0

/-!
The static pack of a value into the buffer `b` (section 5.1, ADR 0025). Its leaves go in packing
order, the first leaf in the low bits. A `Bool` has 1 bit, and a finite value its width. An enum
packs its tag, then its payload. `()` adds no bit. The payload values of a variant are hardware
data after their typed uses, so no other value occurs.
-/
mutual
  def Value.pack (b : Bits) : Value → Bits
    | .bool x => b.put 1 (if x then 1 else 0)
    | .uint w x | .sint w x => b.put w x.toNat
    | .enum _ w x p y => (b.put w x.toNat).put p y.toNat
    | .array _ ⟨xs⟩ | .tuple ⟨xs⟩ | .record _ ⟨xs⟩ => Value.packAll b xs
    | _ => b

  def Value.packAll (b : Bits) : List Value → Bits
    | [] => b
    | x :: xs => Value.packAll (Value.pack b x) xs
end

/-! The core `let` statements that a binding of an aggregate makes, in packing order. -/
abbrev Binds := StateT (Array Let) (Except Fault)

/-!
Take the part of the type `t` of the base `b`. Each of its hardware leaves gets a core `let`
at `path` with its leaf fields (section 7.3), in packing order. `fs` gives the named parts of
a struct type and of an enum type. The depth `d` of `t` bounds the walk.
-/
def leafLets (fs : Ty → Option (Array (String × Ty))) (pos : Pos) :
    Nat → Base → Path → Ty → Binds Unit
  | 0, _, _, t => throw (.S010, s!"{t.text} is deeper than its depth")
  | d + 1, b, path, t =>
    let sub (k : Nat) (f : Field) := b.sub (typesOf fs) t k f
    -- A part without a hardware leaf has no `let`, so the walk skips it, as `Layout` does.
    if t.info.leaves = 0 then pure () else
    match t with
    | .bool | .uint _ | .sint _ => modify (·.push ⟨path, .mk pos t b.op [], pos⟩)
    | .array e n => do
      for k in [0:n] do leafLets fs pos d (sub k (.elem k)) (path.push (.elem k)) e
    | .tuple ts => do
      for (u, k) in ts.zipIdx do leafLets fs pos d (sub k (.elem k)) (path.push (.elem k)) u
    | .struct .. | .enum .. => do
      let some nfs := fs t | throw (.S010, s!"{t.text} has no specialization")
      for ((x, u), k) in nfs.zipIdx do
        leafLets fs pos d (sub k (.user x)) (path.push (.user x)) u
    | _ => pure ()

/-!
The binding of the aggregate `a` to the core name `path` (section 7.3). Each hardware leaf gets
one core `let` at `path` with its leaf fields, and a reference expands into its leaves. The
result refers to the names: a hardware leaf becomes a name, a reference becomes a reference to
`path`, and a static part keeps its value. A handle and a list node hold no hardware leaf, so
they keep their form.
-/
mutual
  def Agg.bindAt (fs : Ty → Option (Array (String × Ty))) (pos : Pos) (path : Path) :
      Agg → Binds Agg
    | .static v => pure (.static v)
    | .handle h => pure (.handle h)
    | a@(.list ..) => pure a
    | .hw h => do
      modify (·.push ⟨path, h, pos⟩)
      return .hw (.mk pos h.ty (.ref path) [])
    | .ref b t => do
      leafLets fs pos t.depth b path t
      return .ref (.name path) t
    | a@(.array _ ⟨xs⟩) | a@(.tuple _ ⟨xs⟩) => do
      return a.rebuild (← Agg.bindEach fs pos path 0 xs).toArray
    | a@(.record n ⟨xs⟩) => do
      let some nfs := fs n.ty | throw (.S010, s!"{n.ty.text} has no specialization")
      return a.rebuild (← Agg.bindNamed fs pos path (nfs.toList.map (·.1)) xs).toArray

  def Agg.bindEach (fs : Ty → Option (Array (String × Ty))) (pos : Pos) (path : Path)
      (k : Nat) : List Agg → Binds (List Agg)
    | [] => pure []
    | x :: xs => do
      let y ← Agg.bindAt fs pos (path.push (.elem k)) x
      return y :: (← Agg.bindEach fs pos path (k + 1) xs)

  def Agg.bindNamed (fs : Ty → Option (Array (String × Ty))) (pos : Pos) (path : Path) :
      List String → List Agg → Binds (List Agg)
    | x :: ns, a :: xs => do
      let y ← Agg.bindAt fs pos (path.push (.user x)) a
      return y :: (← Agg.bindNamed fs pos path ns xs)
    | _, xs => pure xs
end

/-! The types of the named parts of the type `t` (`Specs.parts`), in packing order. -/
def fieldTys (specs : Specs) (t : Ty) : List Ty := ((specs.parts t).getD #[]).toList.map Prod.snd

/-!
The text of a part of the type `t` of a reference in a record (section 8.2): the value that it
stands for. A part without a hardware leaf is the static zero of its type, and a part of a scalar
type is a hardware leaf `(hw <type>)`. Another part is its container form with each part
rendered. An enum is `(enum <type> <tag> <payload>)`. The metadata and the done entries of
`specs` give it, so it reads no base and has no charge. The bound `b` is the depth of `t`,
because each part is less deep than its type.
-/
def Ty.render (specs : Specs) : Nat → Ty → String
  | 0, _ => "-"
  | b + 1, t =>
    if t.info.leaves = 0 then ((zeroOf specs t.depth t).map Value.serialize).getD "-"
    else
      let parts (ts : List Ty) := Print.list (ts.map (Ty.render specs b))
      match t with
      | .array e n =>
        Print.node "array" [e.serialize, Print.list (.replicate n (Ty.render specs b e))]
      | .tuple ⟨ts⟩ => Print.node "tuple" [parts ts]
      | .struct .. => Print.node "record" [t.serialize, parts (fieldTys specs t)]
      | .enum .. => Print.node "enum" (t.serialize :: (fieldTys specs t).map (Ty.render specs b))
      | t => Print.node "hw" [t.serialize]

/-!
The charge of the rendering of a part of the type `t` of a reference (section 5.4). Each
container part with a hardware leaf charges 1. A part without a hardware leaf renders as its
static zero with no charge, because the copy of the reference paid its zero size. An array
multiplies the charge of its element, so the charge reads each type once. The bound `b` is the
depth of `t`.
-/
def Ty.renderCharge (specs : Specs) : Nat → Ty → Nat
  | 0, _ => 0
  | b + 1, t =>
    if t.info.leaves = 0 then 0
    else
      let parts (ts : List Ty) := (ts.map (Ty.renderCharge specs b)).sum
      match t with
      | .array e n => 1 + n * Ty.renderCharge specs b e
      | .tuple ⟨ts⟩ => 1 + parts ts
      | .struct .. | .enum .. => 1 + parts (fieldTys specs t)
      | _ => 0

/-! The element type text of a container node: the element type of an array, the record type. -/
def Node.tyText (n : Node) : String :=
  match n.ty with
  | .array e _ => e.serialize
  | t => t.serialize

/-!
The texts `ys` of the parts `xs` of an enum node, with a static tag as an integer (section 8.2).
A tag is a scalar leaf, so its other forms keep their text.
-/
def Agg.tagFirst : List Agg → List String → List String
  | .static (.uint _ v) :: _, _ :: ys => toString v.toNat :: ys
  | _, ys => ys

/-!
The text of the handle `h` in a record (section 8.2), by its kind. A resource and a memory name
their type and their core name. An instance names its emitted module name and its core name, and
a child input the core name of its instance and its port name. A domain names itself.
-/
def Handle.render : Handle → String
  | .res k _ t path =>
    let kind := match k with | .reg => "reg" | .wire => "wire" | .output => "output"
    Print.node kind [t.serialize, encode path.name]
  | .mem _ path t k => Print.node "mem" [(Ty.array t k).serialize, encode path.name]
  | .inst _ path i _ => Print.node "instance" [encode i.name, encode path.name]
  | .input _ path q => Print.node "input" [q.ty.serialize, encode path.name, q.text]
  | .domain d => Print.node "domain" [d]

/-!
The text of the aggregate `a` in a record (section 8.2). A static part is its canonical
serialization, and a hardware leaf is `(hw <type>)`. A reference renders by its type
(`Ty.render`). A container node is its container form of section 7.1 with each part rendered. A
hardware enum is `(enum <type> <tag> <payload>)`, the form of a static enum value, so a static
tag is an integer (`Agg.tagFirst`). A handle leaf renders by its kind (`Handle.render`), and a
list node as a static list does. The text is pure.
-/
mutual
  def Agg.render (specs : Specs) : Agg → String
    | .static v => v.serialize
    | .hw h => Print.node "hw" [h.ty.serialize]
    | .ref _ t => Ty.render specs t.depth t
    | .handle h => h.render
    | .list _ e ⟨xs⟩ => Print.node "list" [e.serialize, Print.list (Agg.renderAll specs xs)]
    | .array n ⟨xs⟩ => Print.node "array" [n.tyText, Print.list (Agg.renderAll specs xs)]
    | .tuple _ ⟨xs⟩ => Print.node "tuple" [Print.list (Agg.renderAll specs xs)]
    | .record n ⟨xs⟩ =>
      if n.ty matches .enum .. then
        Print.node "enum" (n.ty.serialize :: Agg.tagFirst xs (Agg.renderAll specs xs))
      else Print.node "record" [n.tyText, Print.list (Agg.renderAll specs xs)]

  def Agg.renderAll (specs : Specs) : List Agg → List String
    | [] => []
    | x :: xs => Agg.render specs x :: Agg.renderAll specs xs
end

/-!
The measure charge of the aggregate `a` in a record (section 5.4). A static part charges its
`Value.measureCharge`. A container node charges 1, and a reference charges its rendered
containers (`Ty.renderCharge`). A hardware leaf and a handle leaf have no container, so they
charge nothing (section 5.4). The byte charge pays for their text.
-/
mutual
  def Agg.renderCharge (specs : Specs) : Agg → Nat
    | .static v => v.measureCharge
    | .hw _ => 0
    | .ref _ t => Ty.renderCharge specs t.depth t
    | .handle _ => 0
    | .array _ ⟨xs⟩ | .tuple _ ⟨xs⟩ | .record _ ⟨xs⟩ | .list _ _ ⟨xs⟩ =>
      1 + Agg.renderChargeAll specs xs

  def Agg.renderChargeAll (specs : Specs) : List Agg → Nat
    | [] => 0
    | x :: xs => Agg.renderCharge specs x + Agg.renderChargeAll specs xs
end

/-!
`len` of an array, a list, or a string at the call `pos`. It refers to an array or a list, also
to a list node, so it charges no size. A string needs a scan, so it charges the size of the
string first.
-/
def lenOf (pos : Pos) : List Val → M Value
  | [v] => do
    match ← baseData pos v with
    | .static (.array _ xs) | .static (.list _ xs) => return .int xs.size
    | .agg (.array _ xs) | .agg (.list _ _ xs) => return .int xs.size
    | .agg (.ref _ (.array _ k)) => return .int k
    | .static v@(.str s) => do
      chargeScan pos v
      return .int s.length
    | v => fail .S010 pos s!"`len` takes an array, a list, or a string, not {v.text}"
  | vs => fail .S007 pos s!"`len` takes 1 argument(s), but it has {vs.length}"

end Silicon.Source.Eval
