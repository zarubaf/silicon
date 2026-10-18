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
  equality, the sum of the two sizes, and compares the identities. So does a pair of two enum
  types, with the size 1 each. An enum and another type have no join. A pair with a handle type
  charges the sum of the two sizes too. Two handle types join only when they are the same type,
  else `S010` with its own text (section 6.2). A pair of two function types
  charges in the same way and needs two equal types, also in their `mut` marks. Another pair
  charges nothing. A visit that fails stops the walk, so the charge counts the pairs up to that
  visit.
- A `type` item is a constant of type `Type` in the table of constants. Its first use evaluates
  its type expression, and a use while it is in progress is `S019`.
- The key of a struct specialization is its struct item and its static arguments. Each argument
  comes after its typed use at its parameter type: the normalized identity of v0.1. Thus `P[8]`
  and `P[UInt[4](8)]` are one type when the parameter of `P` has the type `UInt[4]`. Each use
  counts toward the nesting depth (`S015`). It evaluates the parameter types in the scope of the
  struct and binds the parameters as typed uses, with their charges and errors. The size of each
  argument charges right after its typed use, before the next parameter type. These charges come
  before the lookup, because the lookup reads the arguments in full. The work of the prelude
  struct `ReadResponse` reports each of its errors at the use (`atUse`). A first use then
  charges the size of the struct type and evaluates the field types. Then it checks the depth of
  the struct type (`S015`) and charges the sums of its metadata. A use in progress is `S019`. A
  use of a done entry charges nothing more. A use of a struct item while its own parameter types
  evaluate is `S019` too, because its key does not exist yet.
- A handle type `Reg[T]`, `Wire[T]`, `Input[T]`, or `Mem[T, N]` checks its evaluated arguments
  with no charge, then its depth, then charges its size (`handleTy`). `Mem` shares the word and
  depth checks of a `mem` statement (`memWord`, `memDepth`). A handle type where a position
  needs hardware data is `S010` with a text that names the data type (`handleData`).
- The table of enums holds each enum by its item (`Specs.enums`). `Eval.enumOf` runs the first
  use of an enum, and a later use reads its done entry.
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
    fail .S015 (c.site.getD pos)
      s!"the depth {d} goes above the nesting depth {c.limit}; raise --depth to at least {d}"

/-!
The text of a handle type `t` where a position needs hardware data, if `t` is a handle type
(section 6.2). It names the data type to use. An instance type has no data type. A container
that holds a handle type is not a handle type, so its position keeps its own text.
-/
def handleData : Ty → Option String
  | t@(.reg d) | t@(.wire d) | t@(.input d) | t@(.mem d _) =>
    some s!"`{t.text}` is a handle type, not hardware data; use its data type `{d.text}`"
  | t@(.inst ..) =>
    some (s!"`{t.text}` is a handle type, not hardware data; an instance has no data type, " ++
      "so read its outputs as `u.q`")
  | _ => none

/-! `S010` at `p` when `t` is a handle type, with the text of `handleData`. -/
def notHandle (p : Pos) (t : Ty) : M Unit := do
  if let some m := handleData t then fail .S010 p m

/-!
The word type of a memory at `p`: its `mem` statement or its use `Mem[T, N]` (section 6.2). It is
hardware data with at least one leaf (`S010`), so an empty word is `S010` and not `S012`. Its
width is at most 65536 bits (`S012`). The metadata gives both, with no walk.
-/
def memWord (p : Pos) (t : Ty) : M Ty := do
  notHandle p t
  if !t.info.data || t.info.leaves = 0 then
    fail .S010 p (s!"a memory word is a nonempty hardware data type, not `{t.text}`; use a " ++
      "type with at least one bit, for example `UInt[8]`")
  if t.info.width > 65536 then
    fail .S012 p (s!"a memory word has at most 65536 bits, not {intText t.info.width}; split " ++
      "the word over more than one memory")
  return t

/-!
The depth of a memory at `p`: its `mem` statement or its use `Mem[T, N]` (section 6.2). It is a
static value (`S011`), an integer (`S010`), and 1 to 16777216 (`S012`). Each error is at `p`.
-/
def memDepth (p : Pos) : Val → M Nat
  | .static (.int k) =>
    if k < 1 || k > 16777216 then
      fail .S012 p s!"a memory depth is 1 to 16777216, not {intText k}; use a depth in this range"
    else pure k.toNat
  | v@(.static _) | v@(.pending ..) =>
    fail .S010 p
      s!"a memory depth is a static integer, not {v.about}; write an integer, for example `16`"
  | v => fail .S011 p
      s!"a memory depth is static, not {v.about}; compute the depth from static values"

/-! The name of a handle type family, its signature, and an example of a use (section 6.2). -/
def familyText : PrimType → String × String × String
  | .reg => ("Reg", "Reg[T]", "Reg[UInt[8]]")
  | .wire => ("Wire", "Wire[T]", "Wire[UInt[8]]")
  | .input => ("Input", "Input[T]", "Input[UInt[8]]")
  | .mem => ("Mem", "Mem[T, N]", "Mem[UInt[8], 16]")
  | .instance => ("Instance", "Instance[M, args]", "Instance[Counter, 8]")
  | .bool | .uint | .sint | .nat | .int | .unit | .type | .string | .list => ("", "", "")

/-! The `S007` text of a type family `x` with the signature `g`, `n` arguments, and `m` uses. -/
def familyArity (x g : String) (n m : Nat) : String :=
  s!"`{x}` takes {n} argument(s), but it has {m}; write `{g}`"

/-!
The use at `p` of the handle type family `k`, `Reg`, `Wire`, `Input`, or `Mem`, with its
evaluated arguments `vs` (section 5.4). Pass 4 checks the number of arguments, so another number
is a defect. The first argument is a type (`S010`). `T` of `Reg`, `Wire`, and `Input` is hardware
data, which can be empty (`S010`). `Mem` runs the word and depth checks of a `mem` statement. Each
check reads the metadata, with no charge. Then the type checks its depth and charges its size.
-/
def handleTy (p : Pos) (k : PrimType) (vs : List Val) : M Ty := do
  let (x, g, e) := familyText k
  let want := if k == .mem then 2 else 1
  if vs.length != want then fail .S007 p (familyArity x g want vs.length)
  let d ← match vs.head? with
    | some (.static (.type d)) => pure d
    | v => fail .S010 p (s!"the first argument of `{x}` is a type, not " ++
        s!"{(v.map Val.about).getD "`[]`"}; write a type, for example `{e}`")
  let t ← match k, vs with
    | .mem, [_, n] => do
      let d ← memWord p d
      pure (Ty.mem d (← memDepth p n))
    | _, _ => do
      notHandle p d
      unless d.info.data do
        fail .S010 p (s!"`{x}` takes a hardware data type, not `{d.text}`; use a fixed-width " ++
          "type, for example `UInt[8]`")
      pure (if k == .reg then Ty.reg d else if k == .wire then Ty.wire d else Ty.input d)
  bounded p t.depth
  charge p t.size
  return t

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
    s!"the fuel cannot pay the joins of the types; {intText left} remain; raise --fuel"
  lift pos r

/-!
Runs `act`, the work of the prelude struct at its use `p`. Each error of `act` reports at `p`,
because the prelude struct has no source position (section 6.2).
-/
def atUse (p : Pos) (act : M α) : M α := fun c s =>
  match act c s with
  | .ok r => .ok r
  | .error e => .error { e with err.pos := p }

def metaLimitText : String :=
  "the metadata of the type can have more than 2^32 bits, the limit of a static Int; " ++
  "use a smaller type"

/-! The largest bit length of the width, the leaf count, and the zero size `+ 1` of `m`. -/
def metaBits (m : Meta) : Nat :=
  max (bitLength m.width) (max (bitLength m.leaves) (bitLength m.zeroSize + 1))

/-!
The bound on the bit lengths of the metadata sums of the parts `parts`, before the sums run. A
sum of `n` numbers below `2^b` is below `2^(b + bitLength n)`. The zero size gets 1 more, by
`metaBits`.
-/
def sumBits (parts : List Meta) : Nat :=
  (parts.map metaBits).foldl max 0 + bitLength parts.length

/-!
The bound on the bit lengths of the metadata of `[T; N]`, from the metadata `m` of `T`. Each
product gets the bound of `*`. The zero size `1 + N * z` gets 1 more (section 5.4).
-/
def arrayBits (m : Meta) (n : Nat) : Nat := bitLength n + metaBits m

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

/-! A handle type: `Reg[T]`, `Wire[T]`, `Input[T]`, `Mem[T, N]`, or `Instance[M, args]`. -/
def handleTy? : Ty → Bool
  | .reg _ | .wire _ | .input _ | .mem .. | .inst .. => true
  | _ => false

/-!
The text "Typed use at a handle type" of section 6.2. It names the handle type `t` of the
position and the value or the leaf `a` at it.
-/
def handleUseText (t : Ty) (a : String) : String :=
  s!"expected `{t.text}`, but the value is {a}; a handle type takes only a handle of exactly " ++
    "this type, so give such a handle or change the type"

/-!
A typed use at `pos` at the type `t` at the static position `s` (section 5.1). `s` is `a module
argument`, `a comptime parameter`, `an argument of a comptime fn`, or `a const`. No value of a
type with the handle flag is static. Thus such a type there is `S011`, with the text "Static
handle type" of section 6.2. The flag decides, so `[Reg[T]; 2]` is `S011` too. The caller
charged the copy first.
-/
def staticHandle (pos : Pos) (s : String) (t : Ty) : M Unit := do
  if t.info.handles then
    fail .S011 pos (s!"{s} takes only static values, so its type cannot be `{t.text}`, a type " ++
      "that holds a handle type; use a data type, for example `UInt[8]`")

/-!
The kind `{k}` and the source name `{r}` of the handle `h` in the text "Handle at a static
position" (section 6.2). A child input names its instance and its port, as in `u.p`. An own
output and a domain have no handle type, so they keep the text of `static`.
-/
def Handle.static? : Handle → Option (String × String)
  | .res .reg _ _ path => some ("register", sourceOf path)
  | .res .wire _ _ path => some ("wire", sourceOf path)
  | .mem _ path .. => some ("memory", sourceOf path)
  | .inst _ path .. => some ("instance", sourceOf path)
  | .input _ path q => some ("input", s!"{sourceOf path}.{q.name}")
  | .res .output .. | .domain _ => none

/-!
The value `v` at the static position `s` at `pos`, before its typed use (sections 5.1 and 5.3).
A handle is `S011` with the text "Handle at a static position". Another value of a type with the
handle flag is `S011` with the text "Handles at a static position", which names its type. The
check reads the kind of the value and the flag of its type, so it walks no value. Each other
value passes, and `static` checks it.
-/
def staticValue (pos : Pos) (s : String) : Val → M Unit
  | .handle h => do
    if let some (k, r) := h.static? then
      fail .S011 pos (s!"{s} holds the {k} handle `{r}`, but it takes only static values; " ++
        "pass the data through a port, or use the handle in the module that declares it")
  | .agg a => do
    if let some t := a.ty? then
      if t.info.handles then
        fail .S011 pos (s!"{s} takes only static values, but a value of `{t.text}` can hold " ++
          "handles; pass the data through a port, or use the handles in the module that " ++
          "declares them")
  | _ => pure ()

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
element types. A pair with a handle type charges as a type equality, then needs one type.
-/
mutual
  def joinTy : Ty → Ty → Walk (Option Ty)
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
    | s@(.struct ..), t@(.struct ..) | s@(.fn ..), t@(.fn ..)
    | s@(.enum ..), t@(.enum ..) => do
      modify (· + (s.size + t.size))
      return if s.same t then some s else none
    | s, t => do
      if handleTy? s || handleTy? t then
        modify (· + (s.size + t.size))
        if handleTy? s && s.same t then return some s
        throw (.S010, s!"`{s.text}` and `{t.text}` have no common type; a handle type joins " ++
          "only with the same handle type, so give both sides one type")
      if containerTy s && containerTy t then modify (· + 1)
      return scalarJoin s t

  def joinAll : List Ty → List Ty → Walk (Option (List Ty))
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
normalized static arguments `args`. `bindParams` charged their sizes before the lookup. The key
of the lookup is the item and the arguments, so its work stays in those charges. The first use runs
`fields`, which evaluates the field types. The caller nests it.
-/
def specialize (p : Pos) (x : String) (i : Nat) (pre : Bool) (args : List Value)
    (fields : M (List (String × Ty))) : M Ty := do
  match (← get).specs.find? i args with
  | some (_, ⟨_, _, .done t _⟩) => return t
  | some (k, ⟨_, _, .inProgress⟩) =>
    let t := Ty.struct k x args.toArray Meta.static pre
    fail .S019 p s!"the specialization {t.text} is in progress"
  | none => do
    let k := (← get).specs.entries.size
    charge p (Ty.struct k x args.toArray Meta.static pre).size
    modify fun s => { s with specs := { s.specs with
      entries := s.specs.entries.push ⟨i, args, .inProgress⟩,
      index := s.specs.index.insert (i, args) k } }
    let fs ← fields
    let ms := fs.map (·.2.info)
    if over (sumBits ms) then fail .S015 p metaLimitText
    let m := Meta.struct ms (args.map Value.depth)
    bounded p m.depth
    sums p ms m
    let t := Ty.struct k x args.toArray m pre
    modify fun s => { s with specs := { s.specs with
      entries := s.specs.entries.set! k ⟨i, args, .done t fs.toArray⟩ } }
    return t

/-! Sets the entry of the enum item `i` in the table of enums. -/
def setEnum (i : Nat) (e : EnumState) : M Unit :=
  modify fun s => { s with specs := { s.specs with enums := s.specs.enums.insert i e } }

/-! The numbered part types of the type `t` (`Specs.parts`), for the offset of a word part. -/
def partsIn (specs : Specs) : Parts := typesOf specs.parts

/-!
The zero of a hardware data type `t` (section 5.6): 0 for each integer leaf and `false` for each
`Bool` leaf. A struct type takes the types of its named parts (`Specs.parts`). An enum gives the
static enum value with the tag 0 and the payload 0, from the widths of its done entry. The bound
`b` is the depth of `t`, because each part of a type is less deep than the type. An array of the
length 0 makes no zero of its element type. That zero can be above the size limit, and no value
holds it.
-/
def zeroOf (specs : Specs) : Nat → Ty → Option Value
  | 0, _ => none
  | b + 1, t =>
    match t with
    | .bool => some (.bool false)
    | .uint w => some (.uint w 0)
    | .sint w => some (.sint w 0)
    | .unit => some .unit
    | .array e 0 => some (.array e #[])
    | .array e k => do return .array e (Array.replicate k (← zeroOf specs b e))
    | .tuple ⟨ts⟩ => do return .tuple (← ts.mapM (zeroOf specs b)).toArray
    | .struct .. => do
      let fs ← specs.parts t
      return .record t (← fs.mapM fun (_, u) => zeroOf specs b u)
    | .enum .. => do
      let (w, p) ← specs.widths t
      return .enum t w 0 p 0
    | .nat | .int | .type | .string | .list _ | .fn .. | .reg _ | .wire _ | .input _ | .mem ..
    | .inst .. => none

/-!
The array type `[e; k]` at `pos`. The length at `q` is a static `Nat`. After the depth check, the
products of its metadata get the size limit. Then it charges its size and the products.
-/
def arrayTy (pos q : Pos) (e : Ty) : Value → M Ty
  | .int k => do
    if k < 0 then fail .S012 q s!"the length {intText k} is not a Nat"
    let t := Ty.array e k.toNat
    bounded pos t.depth
    if over (arrayBits e.info k.toNat) then fail .S015 pos metaLimitText
    charge pos (t.size + e.info.arrayCharge k.toNat)
    return t
  | v => fail .S010 q s!"the length of an array is a static Nat, not {v.text}"

/-!
The tuple type of `ts` at `pos`. The bound of its metadata sums gets the size limit first. Then
it checks its depth and charges its size and the sums of its metadata.
-/
def tupleTy (pos : Pos) (ts : List Ty) : M Ty := do
  if over (sumBits (ts.map Ty.info)) then fail .S015 pos metaLimitText
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
