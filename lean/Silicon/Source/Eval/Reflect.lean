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

`@typeInfo(T)` builds its `TypeInfo` record here (`typeInfo`), after its argument and the use of
`TypeInfo` (section 6.2, **`@typeInfo` order**). It reads the stored parts of the type: the
fields of a struct entry and the variants of an enum entry. It charges them and the size of the
result before the record exists.
`@Struct(fs)` checks the kind of its argument here (`structArg`), and it makes its generated
record type here (`generated`), after the copy of its argument (section 6.2, **`@Struct`
order**). A builtin in a type position checks its value here (`builtinTy`).
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
    | .tuple ts => return ts[← within r ts.size k]
    | _ => fail .S010 q s!"an index needs an array, a list, or a tuple, not {partText t}"

/-!
The step `s` on the value `v` that holds its parts (section 9.3). A container node gives its
element as it is, so a reference in it charges no zero size. A list node checks the index
against its own length. Each other value takes the step of a place (`pickKey`, `selectKey`,
`fieldKeyBy`). A static value selects there with no charge, and another value fails there, for
example a memory with `S010`. An index of a string is "String index in a query", because the
walk selects in types and a `String` has no element type. The text names no value of the
string. The result is the number of the part, the part, and the field type of a field.
-/
def valueStep (v : Val) (s : QueryStep) : M (Nat × Val × Option Ty) := do
  match s, v with
  | .index _ q k, .agg (.array _ xs) | .index _ q k, .agg (.tuple _ xs)
  | .index _ q k, .agg (.list _ _ xs) => do
    let j ← within q xs.size k
    return (j, xs[j].val, none)
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
  | .index p _ _, .static (.str _) =>
    fail .S010 p ("a query cannot index a string; an index of a string has the type `String`, " ++
      "so write `String` instead of the query")
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
    | none => fail .S010 p (s!"`@TypeOf` takes a part with a type, not {v.about}; pass a value, " ++
        "a port, or a resource")

/-!
The kind tag of the type `t` in the field `kind` of `TypeInfo` (section 9.3). Each struct type is
a `record`, also a prelude struct.
-/
def kindTag : Ty → String
  | .bool => "bool"
  | .uint _ => "uint"
  | .sint _ => "sint"
  | .unit => "unit"
  | .array .. => "array"
  | .tuple _ => "tuple"
  | .struct .. => "record"
  | .int => "int"
  | .nat => "nat"
  | .string => "string"
  | .type => "type"
  | .fn .. => "function"
  | .list _ => "list"
  | .reg _ => "reg"
  | .wire _ => "wire"
  | .mem .. => "mem"
  | .input _ => "input"
  | .inst .. => "instance"
  | .enum .. => "enum"

/-!
The parts of a `TypeInfo` record before it exists (section 9.3). These are the kind tag, the
fields, the element type, the length, the width, and the variants. A field has its name and its
type. A variant has its name, its tag, and its payload types. A part that the kind does not use
keeps its default.
-/
structure Info where
  kind : String
  fields : Array (String × Ty) := #[]
  element : Ty := .unit
  length : Nat := 0
  width : Nat := 0
  variants : Array (String × Nat × Array Ty) := #[]

/-!
The parts of `@typeInfo(t)` at the node `p` (section 9.3). A struct type reads the fields of its
done entry, so a struct with parameters gives the field types of its specialization. An enum
reads its done entry and the variant names of its item. A tuple names its fields `0`, `1`, and
so on. Each read takes the stored parts, so it never enters a field type or a payload type.
-/
def infoOf (p : Pos) (t : Ty) : M Info := do
  let k := kindTag t
  match t with
  | .bool => return { kind := k, width := 1 }
  | .uint w | .sint w => return { kind := k, width := w }
  | .array e n => return { kind := k, element := e, length := n }
  | .tuple ⟨ts⟩ =>
    return { kind := k, fields := (ts.mapIdx fun i u => (toString i, u)).toArray,
             length := ts.length }
  | .struct .. => do
    let some fs := (← get).specs.parts t | fail .S010 p s!"{t.text} has no entry"
    return { kind := k, fields := fs, length := fs.size }
  | .list e | .reg e | .wire e | .input e => return { kind := k, element := e }
  | .mem e n => return { kind := k, element := e, length := n }
  | .enum i _ m => do
    let some (.done _ w _ vs _) := (← get).specs.enums[i]?
      | fail .S010 p s!"{t.text} has no entry"
    let some (.enum _ _ _ items) := (← read).items[i]?
      | fail .S010 p "the enum item is missing"
    let names := items.toArray.map (·.name.name)
    return { kind := k, element := .uint w, width := m.width,
             variants := vs.mapIdx fun j (tag, ps) => (names.getD j "", tag, ps) }
  | _ => return { kind := k }

/-!
The `TypeInfo` record of the parts `info`. `ti`, `fi`, and `vi` are the struct types `TypeInfo`,
`FieldInfo`, and `VariantInfo`. A `Nat` is an integer value.
-/
def Info.value (info : Info) (ti fi vi : Ty) : Value :=
  .record ti #[.str info.kind,
    .list fi (info.fields.map fun (x, u) => .record fi #[.str x, .type u]),
    .type info.element, .int info.length, .int info.width,
    .list vi (info.variants.map fun (x, tag, ps) =>
      .record vi #[.str x, .int tag, .list .type (ps.map .type)])]

/-!
A value has only type leaves when it is a `Type`. A tuple or a non-empty array has them when its
elements have them (section 6.2). The walk reads only the argument, which its evaluation
charged, so it charges nothing.
-/
mutual
  def typeLeaves : Value → Bool
    | .type _ => true
    | .tuple ⟨xs⟩ => typeLeavesAll xs
    | .array _ ⟨x :: xs⟩ => typeLeavesAll (x :: xs)
    | _ => false

  def typeLeavesAll : List Value → Bool
    | [] => true
    | x :: xs => typeLeaves x && typeLeavesAll xs
end

/-!
The fix `{h}` of "`@typeInfo` of a value" for the argument `v` (section 6.2). A domain has no
type. A tuple or an array with only type leaves names its type. Each other value takes its type
with `@TypeOf`.
-/
def typeInfoHint : Val → String
  | .handle (.domain _) => "a domain has no type, so remove the `@typeInfo`"
  | .static v@(.tuple _) =>
    if typeLeaves v then "name the tuple type with `type T = (A, B);` and use `@typeInfo(T)`"
    else bindHint
  | .static v@(.array ..) =>
    if typeLeaves v then "name the array type with `type T = [A; N];` and use `@typeInfo(T)`"
    else bindHint
  | _ => bindHint
where
  bindHint := "bind the value with `let x = ...;` and use `@typeInfo(@TypeOf(x))`"

/-!
The argument of `@typeInfo` at the node `pos` after it evaluated (section 6.2, **`@typeInfo`
order**, step 3). A value that is not a `Type` is `S010`, with no copy charge.
-/
def typeInfoArg (pos : Pos) : Val → M Ty
  | .static (.type t) => pure t
  | v => fail .S010 pos s!"`@typeInfo` takes a type, not {v.about}; {typeInfoHint v}"

/-!
The number of fields and the variants of the type `t` at the node `p`, as the type stores them
(section 6.2, **`@typeInfo` order**, step 5). A tuple stores its elements, a struct the fields of
its done entry, and an enum the variants of its done entry. No read walks a part.
-/
def counts (p : Pos) (t : Ty) : M (Nat × Array (Nat × Array Ty)) := do
  match t with
  | .tuple ts => return (ts.size, #[])
  | .struct .. => do
    let some fs := (← get).specs.parts t | fail .S010 p s!"{t.text} has no entry"
    return (fs.size, #[])
  | .enum i .. => do
    let some (.done _ _ _ vs _) := (← get).specs.enums[i]?
      | fail .S010 p s!"{t.text} has no entry"
    return (0, vs)
  | _ => return (0, #[])

/-!
`@typeInfo(t)` at the node `p`, after the use of `TypeInfo` gave `ti` (section 6.2, **`@typeInfo`
order**, steps 5 to 8). The field types of `TypeInfo` give `FieldInfo` and `VariantInfo`. The
call charges 1 for each field and for each variant (`counts`). Then it adds the payload counts of
the variants and charges 1 for each payload type. Only then the parts of the record exist
(`infoOf`). Then the result gets its depth check (`S015`), and its recursive size charges. This
size counts each field type, each payload type, and each name as a string. Only then the record
exists.
-/
def typeInfo (p : Pos) (ti t : Ty) : M Value := do
  let (some (_, Ty.list fi), some (_, Ty.list vi)) :=
      (((← get).specs.parts ti).bind (·[1]?), ((← get).specs.parts ti).bind (·[5]?))
    | fail .S010 p s!"{ti.text} has no entry"
  let (f, vs) ← counts p t
  charge p (f + vs.size)
  charge p (vs.foldl (fun n (_, ps) => n + ps.size) 0)
  let info ← infoOf p t
  let v := info.value ti fi vi
  bounded p v.depth
  charge p v.size
  return v

/-! The prelude struct `FieldInfo` (section 5.6). A user struct with this name is another type. -/
def preludeFieldInfo : Ty → Bool
  | .struct _ "FieldInfo" _ _ .prelude => true
  | _ => false

/-! A user struct with the name `FieldInfo`. It hides the prelude struct (section 6.2). -/
def userFieldInfo : Ty → Bool
  | .struct _ "FieldInfo" _ _ .user => true
  | _ => false

/-! The name and the type of a `FieldInfo` record. -/
def fieldOf : Value → Option (String × Ty)
  | .record _ ⟨[.str x, .type t]⟩ => some (x, t)
  | _ => none

/-!
The fields of the argument `v` of `@Struct` at the argument `pos` (section 6.2, **`@Struct`
order**, step 4). A `List[FieldInfo]` or a `[FieldInfo; N]` of the prelude `FieldInfo` gives the
name and the type of each record. A value of a user `FieldInfo`, also as the element type, is
"User `FieldInfo` in `@Struct`". Each other value is "Argument of `@Struct`". The check reads the
type of `v` and the two parts of each record, and it charges nothing.
-/
def structArg (pos : Pos) (v : Val) : M (List (String × Ty)) := do
  match v with
  | .static (.array t xs) | .static (.list t xs) =>
    if preludeFieldInfo t then
      if let some fs := xs.toList.mapM fieldOf then return fs
  | _ => pure ()
  let user := match v.ty? with
    | some (.array e _) | some (.list e) => userFieldInfo e
    | some t => userFieldInfo t
    | none => false
  if user then
    fail .S010 pos (s!"`@Struct` takes the prelude `FieldInfo`, not {v.about}; a user struct " ++
      "`FieldInfo` hides the prelude one, so rename it, or take the fields from " ++
      "`@typeInfo(T).fields`")
  fail .S010 pos (s!"`@Struct` takes a `List[FieldInfo]` or a `[FieldInfo; N]`, not {v.about}; " ++
    "build each field with the prelude `FieldInfo(name, ty)`")

/-!
The fields `xs` of the argument of `@Struct` at its `@` `p`, after the fields `fs` with the member
map `ms` (section 6.2, **`@Struct` order**, step 5). Each name charges its size as a string, which
counts characters. Then it gets the name rule (`S022`) and its symbol (`symbolOf`). The symbol
goes into the member map, and a symbol that the map holds is `S022` "Second field name", with the
two indices from 0.
-/
def genFields (p : Pos) :
    List (String × Ty) → Std.TreeMap Nat Nat compare → Array (String × Ty) →
      M (Std.TreeMap Nat Nat compare × Array (String × Ty))
  | [], ms, fs => pure (ms, fs)
  | (name, t) :: xs, ms, fs => do
    charge p (Value.str name).size
    nameRule p name "field"
    let y ← symbolOf name
    if let some i := ms[y]? then
      fail .S022 p (s!"the field `{strText name}` occurs at the indices {i} and {fs.size} of " ++
        "`@Struct`; give each field its own name")
    genFields p xs (ms.insert y fs.size) (fs.push (name, t))

/-!
The generated record type of the fields `xs` at the `@` `p` (section 6.2, **`@Struct` order**,
steps 5 to 9). After the fields (`genFields`), the metadata gets its size limit (`S015`), as
for a tuple type. Its depth needs no check: it is less than the depth of the argument, which
passed its own check. Then the size of the new type term charges, then the metadata sums. The
look-up in the table of generated record types comes last (`Specs.generate`), so a hit charges
the same as a miss. The walk reads the stored metadata of each field type, and it never goes
into a field type.
-/
def generated (p : Pos) (xs : List (String × Ty)) : M Ty := do
  let (ms, fs) ← genFields p xs {} #[]
  let fs := fs.toList
  let parts := fs.map (·.2.info)
  if over (sumBits parts) then fail .S015 p metaLimitText
  let m := Meta.struct parts []
  charge p (Ty.struct 0 "" #[] m (.gen fs)).size
  sums p parts m
  let (specs, t) := (← get).specs.generate fs ms
  modify fun s => { s with specs }
  return t

/-!
The fix `{h}` of "Builtin as a type" for the builtin `q` (section 6.2). `@TypeOf` and `@Struct`
always give a `Type`, so only `@typeInfo` and `@field` reach the text.
-/
def builtinTyHint : Builtin → String
  | .typeInfo => "select a `Type` from it, for example `@field(@typeInfo(T), \"element\")`"
  | .typeOf | .struct | .field =>
    "select a part of type `Type`, or write `@TypeOf(@field(x, k))` for the type of the part"

/-!
The type of the value `v` of the builtin `q` in a type position, at its `@` `p` (section 6.2,
**Type position order**, step 3). A value that is not a `Type` is `S010` "Builtin as a type".
-/
def builtinTy (p : Pos) (q : Builtin) : Val → M Ty
  | .static (.type t) => pure t
  | v => do
    let h := builtinTyHint q
    fail .S010 p s!"a type position needs a `Type`, but `@{q.name}` gives {v.about}; {h}"

end Silicon.Source.Eval
