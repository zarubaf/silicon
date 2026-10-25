-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Container
import Silicon.Source.Lex

/-!
This module holds the parts of the instantiations and of the checks for each instantiation
that need no evaluation. Sections 5.3, 6.1, and 6.2 of the front-end spec define them.
`Eval.hwStmt` runs a module statement and `Eval.instantiate` an instantiation, in the mutual
block of `Eval`, because an expression evaluates in a module statement. `Elab.elaborate` runs the
top selection and each instantiation that it reaches, in the evaluation order that section 5.2
gives. Each instantiation gives a hardware description: its ports, registers, wires, named
bindings, child instances, and `:=` bindings.
`Source.Flatten` lowers the descriptions to core IR.

The table of instantiations is normative. An `instance` statement works in these steps:

1. It evaluates the arguments from left to right. Each argument is static (`S011`).
2. The typed use of the arguments nests one level (`S015`), in the scope of the module with a
   new frame (`Eval.arguments`). Each parameter type evaluates in order, with each earlier
   parameter bound to its converted argument. An error in it is at its own node. A literal with `[]`
   takes this type. The argument converts to it: `S010` or `S012` at the statement. Then the
   recursive size of the converted argument charges, before the next parameter type, also for a
   done instantiation.
3. A clocked child in a combinational module is `S017` at the statement.
4. The serialization charges the square of the size of each integer, and its length in bytes.
   An instantiation in progress is `S019` at the statement. A done one gives its interface.
5. A new one nests one level deeper (`S015`). Its emitted name charges its length in bytes,
   and it must be new (`S019`). Then it goes in progress, runs its body, checks its bindings,
   and is done.

A new instantiation sets the emitted name of its records and starts with no call frames. A done
instantiation does not run its body again, so its records come out once (decision F15).

The `InstantiationId` holds the converted arguments. Thus `C(1)` and `C(UInt[8](1))` give one
instantiation when the parameter of `C` has the type `UInt[8]`. The parameters of a new
instantiation bind to the converted arguments with their types. The types do not evaluate again,
and the child charges nothing for them.

These rules settle the open points of slice 1:

- `Eval.stmt` charges each statement. A module statement then runs in `Eval.hwStmt`. A `let`,
  an assignment, and an expression statement run as in a function body.
- A port has a public name: its binder, or the name of its `as` key (section 5.6). The table of
  public names of the owner holds each one (`publicOf`). A second port with one public name is
  thus `S019`. A scalar port then takes its public name as its core name in the root frame. A
  port after a binding of the module body with that name is thus `S019` too.
- A port, a register, and a wire have a hardware data type (`S010`), also an aggregate type and
  an empty type. Each still needs its binding (`S018`). An empty one lowers to no core node.
- An empty input charges nothing at its declaration. Each read of it charges the zero size of
  its type, then gives its zero (section 5.4).
- A module parameter can be a type, a record, or a function. Such an argument gives the digest
  form of the emitted name (section 7.1). A function serializes as its item, so a struct
  argument and the key of a struct specialization hold the item too. The typed use at the
  parameter needs the exact function type (`S010` at the statement).
- A function type is not hardware data, also inside an aggregate and in `[fn () -> Bool; 0]`.
  A port, a register, and a wire of such a type are thus `S010` at the statement (`dataType`).
- A function value never reaches the lowering. It is always static. A register value and a `:=`
  value conform to the hardware data type of their resource first. A function there is thus
  `S010`.
- A register in a combinational module is `S017` at the statement, before its type. Its text
  and the texts of a memory and a clocked child there name the fix (section 6.2).
- A `mem` statement checks in the order of section 6.2, each error at the statement: a
  combinational module (`S017`), the word type (`memWord`), then the depth (`memDepth`). It
  makes no `[T; N]` type. Its name binds a memory handle, which is never data (`S010`). The
  memory goes into the names of the instantiation (`Naming.mems`), where `Eval.portCall` records
  its requests. A memory without a `read_port` or a `write_port` call is `S018` at its
  statement. A second call of one kind is `S018` at that call.
- A `:=` target is a register, a wire, an own output, or a child input, also through a handle
  alias. As in a place, its indices evaluate first, then one walk from the root selects
  (section 5.2). The static type of each base decides. A field of an `Instance` handle selects
  a child input with no charge. A step on a container of a type with the handle flag selects.
  Each other step is a part of a value: `S017` at the start of the target. So is a selected
  part of another kind. The target is an identity, so it has no window.
- The value of `:=` is a typed use. It copies a reference, as a `let` with a type does. A read
  of an aggregate handle charges the handle, then the zero size of its type (`typedUse`).
- A `:=` binding holds its value as an aggregate part. A static scalar becomes a hardware
  constant. An aggregate or an empty value stays one part, so the lowering makes its leaf
  statements and charges each one before it makes it.
- `S018` errors wait for the end of the body. The second binding of a resource gives one.
  A resource without a binding gives one at its declaration. A child input without a binding
  gives one at the `instance` statement. The error with the lowest position wins. On a tie,
  the first recorded one wins (section 6.2).
- `S016` comes from the guards of `Eval` (section 9.4). The word type and the depth of a `mem`
  statement are structural contexts. A helper declares and binds in the instantiation of its
  caller (section 9.5), so its handles stay in that owner.
- The owner guard of section 9.5 has no check in slice 1. Module arguments are static
  (`S011`), and ports carry data, so a handle cannot reach another owner.
- The units of an instantiation are its charges from the start of its body to the end of its
  binding check. The units of its new children are not part of them. The charges of an
  `instance` statement, with the typed use of its arguments, belong to the parent. The
  arguments of the top selection and their typed use belong to no instantiation.

Each table grows only with charged work: a new instantiation charges its body, and each
declaration, binding, and child charges its statement.
-/
namespace Silicon.Source.Elab

open Resolve Names Eval

def modifyBody (f : Body → Body) : Eval.M Unit :=
  modify fun s => { s with inst.work.body := f s.inst.work.body }

/-!
A port, a register, and a wire have a hardware data type (section 5.1). The metadata gives it,
so a type with a function type at any depth is `S010` with no walk. The type can be empty. A
handle type names its data type (`notHandle`).
-/
def dataType (p : Pos) (t : Ty) : Eval.M Ty := do
  notHandle p t
  if t.info.data then pure t
  else fail .S010 p (s!"a port, a register, and a wire need a hardware data type, not " ++
    s!"`{t.text}`; use a fixed-width type, for example `UInt[8]`")

/-!
A resource that needs one binding, with the key of a family entry. An output with an `as` key
has its `binder` for its `S018` text. The result is its handle.
-/
def resource (k : Kind) (path : Path) (t : Ty) (p : Pos) (x : String) (key : Option Nat := none)
    (binder : Option String := none) : Eval.M Val := do
  let id := (← get).inst.work.needs.size
  let n : Need := { name := x, key, port := k == .output, binder, pos := p, count := 0 }
  modify fun s => { s with inst.work.needs := s.inst.work.needs.push n }
  return .handle (.res k id t path)

/-!
The helper of a second binding or port call at `p` whose first one is at `b` in the call frame
`f`. When both are at `p`, one `:=` or call runs again. When the first one also ran in another
call, the text names the function (section 6.2). A repeat in one call, for example in a
`comptime for` of the function, keeps the plain text.
-/
def again (p : Pos) (b : Pos × Nat) : Eval.M (Option Nat) := do
  let c ← read
  if b.1 == p && b.2 != c.call then return c.helper else return none

/-!
Inserts the public name with the symbol `y` and the form `f` into the table of public names of
the owner (section 5.6). The table keeps its position `p` and the current call frame.
-/
def publish (y : Nat) (f : Public) (p : Pos) : Eval.M Unit := do
  let n := (← read).call
  modify fun s => { s with inst.work.publics := s.inst.work.publics.insert y (f, p, n) }

/-!
The public name with the symbol `y` in the table of public names of the owner (section 5.6). It
has its form, its first position, and the call frame of that declaration. The table holds each
family of the module body from the start, at its first indexed declaration, in the frame 0.
These families are in the static `Syms.families`. Thus the look-up reads `publics` and then
them, with no copy for each instantiation. Each is one map operation.
-/
def publicOf (y : Nat) : Eval.M (Option (Public × Pos × Nat)) := do
  let w := (← get).inst.work
  if let some e := w.publics[y]? then return some e
  let fams := (← read).syms.families[w.owner]?
  return (fams.bind (·[y]?)).map fun (i, p) => (.family i, p, 0)

/-!
Reserves the core name with the symbol `y` in the root frame, as the bindings of the name count
it. The result is `true` when a declaration took the name before.
-/
def reserve (y : Nat) : Eval.M Bool := do
  let s ← get
  let key := (0, Tag.sym y)
  let v := s.naming.versions.getD key 0
  set { s with naming.versions := s.naming.versions.insert key (v + 1) }
  return v != 0

/-! The position `b` of an earlier declaration in a message. -/
def atText (b : Pos) : String := s!"{b.line}:{b.col}"

/-! The `S019` text "Public name twice" of section 6.2, for the public name `x`. -/
def publicTwiceText (x : String) (b : Pos) : String :=
  s!"the port name `{strText x}` is declared here and at {atText b}; give one of them another " ++
    "key with `as`, for example from a parameter"

/-!
The `S019` text "Public name twice in a helper" of section 6.2, for the public name `x` and the
function `h`.
-/
def publicAgainText (h x : String) : String :=
  s!"`{h}` declares the port `{strText x}` again in a second call; give each call its own port " ++
    "name, for example from a parameter in the `as` key"

/-! The `S019` text "Scalar port and port family" of section 6.2, for the public name `x`. -/
def scalarFamilyText (x : String) (b : Pos) : String :=
  s!"`{strText x}` names a scalar port and a port family, here and at {atText b}; give one of " ++
    "them another key with `as`"

/-! The `S019` text "Public family with two directions" of section 6.2, for the family `x`. -/
def directionsText (x : String) (b : Pos) : String :=
  s!"the port family `{strText x}` has an input entry and an output entry, here and at " ++
    s!"{atText b}; give the entries of one direction another key with `as`"

/-! The `S019` text "Port name taken" of section 6.2, for the public name `x`. -/
def takenText (x : String) : String :=
  s!"the port name `{strText x}` is already the core name of a hardware `let`, a resource, or " ++
    "an instance of this module; rename that declaration or the port"

/-!
The port at `p` with the public name `x` of the symbol `y` (section 6.2, steps 9 to 11 of the
port order). The table of public names of the owner holds no other port of the name. A scalar
port there is "Public name twice". When one statement of a function runs again in another call,
it is "Public name twice in a helper" (`again`). A family there is "Scalar port and port
family". Then the name
takes its core name in the root frame. An earlier binding of the module body with the name
gives "Port name taken". The port has no call frame (section 7.3). An output with an `as` key
has its `binder` for its `S018` text.
-/
def port (p : Pos) (input : Bool) (x : String) (y : Nat) (t : Ty) (binder : Option String) :
    Eval.M Val := do
  match ← publicOf y with
  | some (.scalar, b, n) =>
    match ← again p (b, n) with
    | some h => fail .S019 p (publicAgainText ((← read).itemName h) x)
    | none => fail .S019 p (publicTwiceText x b)
  | some (.family _, b, _) => fail .S019 p (scalarFamilyText x b)
  | none => publish y .scalar p
  if ← reserve y then fail .S019 p (takenText x)
  modifyBody fun d => { d with ports := d.ports.push ⟨x, y, none, input, t, p⟩ }
  -- An input refers to its name: a scalar is hardware, and an aggregate a lazy reference. An
  -- empty input stays a reference too, so only a read of it pays its zero (`Eval.name`).
  if !input then resource .output ⟨x, []⟩ t p x none binder
  else if t.info.leaves = 0 then pure (.agg (.ref (.name ⟨x, []⟩) t))
  else normalize p (.ref (.name ⟨x, []⟩) t)

/-! The `S010` text "Port key type" of section 6.2, for the key `a`. -/
def portKeyText (a : String) : String :=
  s!"an `as` key is a static `String` or `PortKey`, not {a}; write the public name as a " ++
    "string, for example `as \"req_0\"`"

/-! The `S022` text "Scalar key index" of section 6.2, for the index `k`. -/
def scalarIndexText (k : Int) : String :=
  s!"a scalar `PortKey` has the index 0, but it has {intText k}; set `indexed` to `true`, or " ++
    "the index to 0"

/-! The `S022` text "Name rule" of section 6.2, for the name `s` of the kind `kind`. -/
def nameRuleText (s kind : String) : String :=
  s!"`{strText s}` is not a valid {kind} name; use an ASCII letter or `_`, then letters, " ++
    "digits, or `_`"

/-! The `S022` text "Keyword name" of section 6.2, for the name `s` of the kind `kind`. -/
def keywordText (s kind : String) : String :=
  s!"`{strText s}` is a keyword, so it cannot be a {kind} name; choose another name"

/-! The `S010` text "Family as a value" of section 6.2, for the family `x`. -/
def familyValueText (x : String) : String :=
  s!"`{x}` is a port family, not a value; select one port with `{x}[k]`"

/-! The `S010` text "Family key type" of section 6.2, for the key `a`. -/
def keyTypeText (a : String) : String :=
  s!"a family key is a static `Nat`, not {a}; compute the key from static integers, for " ++
    "example a loop value"

/-! The `S012` text "Family key range" of section 6.2, for the key `i`. -/
def keyRangeText (i : Int) : String :=
  s!"a family key is 0 to 4294967295, not {intText i}; use a key in this range"

/-! The `S013` text "Undeclared family key" of section 6.2, for the key `k` of the family `x`. -/
def undeclaredText (x : String) (k : Nat) : String :=
  s!"the port family `{x}` has no key {k} here; declare `{x}[{k}]` before this use"

/-!
The `S013` text "Child family key" of section 6.2, for the key `k` of the family `x` of a child
of the instance type `m`.
-/
def childKeyText (m x : String) (k : Nat) : String :=
  let x := strText x
  s!"the child `{m}` has no entry `{x}[{k}]`; select a key that `{m}` declares"

/-!
The typed use of the static family key `v` at `Nat`, at the key `p` (section 5.6). A key below 0
or of 2^32 or more is `S012` "Family key range", and a key of another type is `S010` "Family key
type". A static `UInt` is such a type. The key fits 32 bits, so each later compare and name of it
takes constant work.
-/
def familyKey (p : Pos) : Value → Eval.M Nat
  | .int i =>
    if 0 ≤ i && i < 2 ^ 32 then pure i.toNat
    else fail .S012 p (keyRangeText i)
  | v => fail .S010 p (keyTypeText (Val.static v).about)

/-!
The `S019` text "Family key twice" of section 6.2, for the key `k` of the family `x` with the
earlier declaration at `b`.
-/
def keyTwiceText (x : String) (k : Nat) (b : Pos) : String :=
  let x := strText x
  s!"the port `{x}[{k}]` is declared here and at {atText b}; declare each key of `{x}` once"

/-!
The entry `k` of the family `x` with the symbol `y`, of the type `t`, declared at `p` (section
6.2, steps 7 and 8 of the entry order). The table of public names of the owner holds the name.
A scalar port there is "Scalar port and port family". A family of the other direction is
"Public family with two directions". A key that the family has already is "Family key twice". A
new
family enters the table. The entry is one whole port with the core name `<x>$<k>f`. It goes into
the table of entries (`Work.entries`) by its public identity, not into a frame slot. The field
`<k>f` keeps its name apart from each other name (section 7.2), so it takes no version. An
output with an `as` key has its `binder` for its `S018` text. The result is the value of the
entry.
-/
def entry (p : Pos) (input : Bool) (x : String) (y k : Nat) (t : Ty) (binder : Option String) :
    Eval.M Val := do
  match ← publicOf y with
  | some (.scalar, b, _) => fail .S019 p (scalarFamilyText x b)
  | some (.family i, b, _) => if i != input then fail .S019 p (directionsText x b)
  | none => publish y (.family input) p
  if let some (_, q) := (← get).inst.work.entries[(y, k)]? then
    fail .S019 p (keyTwiceText x k q)
  modifyBody fun d => { d with ports := d.ports.push ⟨x, y, some k, input, t, p⟩ }
  let path : Path := ⟨x, [.family k]⟩
  -- An input entry refers to its name as a scalar input does (`port`).
  let v ← if !input then resource .output path t p x (some k) binder
    else if t.info.leaves = 0 then pure (.agg (.ref (.name path) t))
    else normalize p (.ref (.name path) t)
  modify fun s => { s with inst.work.entries := s.inst.work.entries.insert (y, k) (v, p) }
  return v

/-!
The public name and the family key of the static `as` key (section 6.2, steps 6 and 7 of the
port order). A `String` is a scalar name. A record of the prelude struct `PortKey` is a
scalar name with the index 0, or an entry with an index below 2^32. A user struct named
`PortKey` is another type. Each other value is `S010` "Port key type". The index check reads
the bit length, so it takes constant work, and the index renders only in an error.
-/
def portKey : Value → Except Fault (String × Option Nat)
  | .str x => .ok (x, none)
  | .record (.struct _ "PortKey" _ _ true) #[.str x, .bool false, .int k] =>
    if k == 0 then .ok (x, none) else .error (.S022, scalarIndexText k)
  | .record (.struct _ "PortKey" _ _ true) #[.str x, .bool true, .int k] =>
    if k < 2 ^ 32 then .ok (x, some k.toNat) else .error (.S012, keyRangeText k)
  | v => .error (.S010, portKeyText (Val.static v).about)

/-!
The port at `p` with the binder `b`, the type `t`, and the static `as` key `v` at `kp` (section
6.2, steps 6 to 11 of the port order). The key gives the public name and the key of an entry
(`portKey`). The name charges its size, 1 plus its characters (section 5.4). This charge comes
before the scan of the name rule and the look-up of the symbol. A name that is not an identifier
is `S022` "Name rule", and a keyword is `S022` "Keyword name". Then the port exists by its public
name, as a scalar port (`port`) or a family entry (`entry`). The binder refers to it. The port
keeps the name with no copy.
-/
def keyed (p : Pos) (input : Bool) (b : Binder) (t : Ty) (kp : Pos) (v : Value) :
    Eval.M Unit := do
  let (x, key) ← lift kp (portKey v)
  charge kp (1 + x.length)
  let kind := "port"
  unless Lex.identifier x do fail .S022 kp (nameRuleText x kind)
  if Lex.keywords.contains x then fail .S022 kp (keywordText x kind)
  let y ← symbolOf x
  let binder := some b.name.name
  let w ← match key with
    | none => port p input x y t binder
    | some k => entry p input x y k t binder
  bindLocal b.id ⟨some t, false, w, true⟩

/-! The target of a `:=` binding: an own resource, or the input `port` of the child `inst`. -/
inductive Target where
  | own (kind : Kind) (id : Nat) (ty : Ty) (path : Path)
  | child (inst : Nat) (path : Path) (port : Port)

/-! The `S017` text "Part as a `:=` target" of section 6.2. -/
def partText : String :=
  "a `:=` target is a whole resource, not a part of a value; bind the whole resource, for " ++
    "example `r := P(a, b);`"

/-! The `S017` text "`:=` target kind" of section 6.2, with the selected value `a`. -/
def kindText (a : String) : String :=
  s!"a `:=` target is a wire, a register, an own output, or a child input, not {a}; select one " ++
    "of these, or assign a local with `=`"

/-!
The `S017` text "Child output as a `:=` target" of section 6.2, for the output `f`. An entry is
`f` with its key, for example `req[3]`.
-/
def outputText (f : String) : String :=
  let f := strText f
  s!"`{f}` is an output of the child, not a target; the child drives its outputs, so bind an " ++
    "input of the child"

/-!
The step `sel` of a `:=` target that starts at `s`, on the base `v`, with the index `k` of
`targetKeys` (sections 5.2 and 9.4). The static type of the base decides. A field of an
`Instance` handle selects the child port with no charge, and an output there is `S017`. On a
container of a type with the handle flag, a field and a selector charge 1, and an index step
charged with its index. Then the step selects the part with its checks (`S010` and `S013`).
Each other base, also another handle, is `S017` at `s`.
-/
def targetStep (s : Pos) (v : Val) (step : Sel × Option Value) : Eval.M Val := do
  let (sel, key) := step
  match v, sel with
  | .handle (.inst k path iface _), .field q f =>
    match (← read).field f.pos >>= fun y => iface.ports[((y, none) : PortId)]? with
    | some port =>
      if port.input then return .handle (.input k path port)
      else fail .S017 s (outputText port.text)
    | none => fail .S010 q s!"the instance has no port `{f.name}`"
  | .agg a, sel =>
    unless a.ty?.any (·.info.handles) do fail .S017 s partText
    match sel, key with
    | .index q [i], some k => return (← pickKey q i.pos v k).2
    | .index q _, _ => fail .S010 q "an index of a value has one argument"
    | .select q r i, _ =>
      charge q 1
      return (← selectKey q r i v).2
    | .field q f, _ =>
      charge q 1
      return (← fieldKey q f v).2.1
  | _, _ => fail .S017 s partText

/-!
The family of the child that the field `f` of the base `v` names, when `v` is an `Instance`
handle (section 5.6). The interface of the child holds its families.
-/
def childFamily (v : Val) (f : Ident) : Eval.M Bool := do
  let .handle (.inst _ _ iface _) := v | return false
  match (← read).field f.pos with
  | some y => return iface.families.contains y
  | none => return false

/-!
The entry of the family `f` of the child behind the `Instance` handle `v`, with the static key
`k` at `kp`, in a `:=` target that starts at `s` (section 5.2). The key gets the type and range
checks of a family selection (`familyKey`). A key that the child did not declare is `S013`
"Child family key". An input entry gives its handle, and an output entry is `S017`.
-/
def childTarget (s : Pos) (v : Val) (f : Ident) (kp : Pos) (k : Value) : Eval.M Val := do
  let key ← familyKey kp k
  let .handle (.inst id path iface ty) := v | fail .S017 s partText
  let y := ((← read).field f.pos).getD 0
  match iface.ports[((y, some key) : PortId)]? with
  | some port =>
    if port.input then return .handle (.input id path port)
    else fail .S017 s (outputText port.text)
  | none => fail .S013 kp (childKeyText ty.text f.name key)

/-!
One step of the walk of a `:=` target that starts at `s`, on the base `v` (section 5.2). `fam`
holds a family of the child behind `v` that the step before named. A field that names a family
of a child keeps it for the next step, so the walk does not start again from the root. That step
is an index, and its key selects the entry (`childTarget`). Else it is `S010` "Family as a
value" at `s`. Each other step selects in `targetStep`.
-/
def walkStep (s : Pos) (v : Val) (fam : Option Ident) (step : Sel × Option Value) :
    Eval.M (Val × Option Ident) := do
  match fam, step with
  | some f, (.index _ [i], some k) => return (← childTarget s v f i.pos k, none)
  | some f, _ => fail .S010 s (familyValueText f.name)
  | none, (.field _ f, _) =>
    if ← childFamily v f then return (v, some f) else return (← targetStep s v step, none)
  | none, _ => return (← targetStep s v step, none)

/-!
The walk of the steps `steps` of a `:=` target that starts at `s`, from the base `v` outward,
with a pending family `fam` of a child (`walkStep`). A family without its key at the end is
`S010` "Family as a value" at `s`.
-/
def targetWalk (s : Pos) (v : Val) (fam : Option Ident) :
    List (Sel × Option Value) → Eval.M Val
  | [] => match fam with
    | some f => fail .S010 s (familyValueText f.name)
    | none => pure v
  | step :: rest => do
    let (w, fam) ← walkStep s v fam step
    targetWalk s w fam rest

/-! Records the `S018` data `x` at `p`. The first by position wins (section 6.2). -/
def breach (p : Pos) (x : Breach) : Eval.M Unit :=
  modify fun s => { s with inst.work.dup := firstBreach s.inst.work.dup p x }

/-!
The `S018` data of a second binding at `p` of `r`, with the first binding at `b` in the call
frame of `b.2` and its declaration at `d`.
-/
def second (p : Pos) (r : Res) (b : Pos × Nat) (d : Pos) : Eval.M Breach := do
  match ← again p b with
  | some h => return .secondIn r h
  | none => return .second r b.1 d

/-!
Records the binding of `t` to `h` at `p`. The second binding of one target is an `S018`, and
the first binding keeps its position for its text.
-/
def bindTarget (p : Pos) (t : Target) (h : Agg) : Eval.M Unit := do
  let w := (← get).inst.work
  let here := (p, (← read).call)
  match t with
  | .own r k t path =>
    if let some n := w.needs[k]? then
      if n.count == 1 then
        breach p (← second p (.own n.name n.key n.port) (n.first.getD here) n.pos)
      modify fun s => { s with inst.work.needs := s.inst.work.needs.modify k fun r =>
        { r with count := n.count + 1, first := r.first <|> some here } }
    modifyBody fun b => { b with binds := b.binds.push ⟨.own r t path, h, p⟩ }
  | .child k path q =>
    let (c, b) := w.inputs.getD (k, q.id) (0, here)
    if c == 0 then
      modify fun s => { s with inst.work.bound := s.inst.work.bound.modify k (· + 1) }
    if c == 1 then
      let (u, d) := ((w.body.children[k]?).map fun c => (c.name, c.pos)).getD ("", p)
      breach p (← second p (.input u q.name q.key) b d)
    modify fun s => { s with inst.work.inputs := s.inst.work.inputs.insert (k, q.id) (c + 1, b) }
    modifyBody fun b =>
      { b with binds := b.binds.push ⟨.child k path q.core q.ty, h, p⟩ }

/-!
The binding rule at the end of a body. A missing binding of an own resource is at its
declaration, and one of a child input is at the `instance` statement. The counts select the
first child with a free input, so only the interface of that child is searched. The name is
that of its free input with the first source position. The records compete by position, and the
text of the winner renders once (section 6.2).
-/
def bindings : Eval.M Unit := do
  let w := (← get).inst.work
  let mems := (← get).naming.mems
  let mut err := w.dup
  for r in w.needs do
    if r.count == 0 then
      err := firstBreach err r.pos (.unbound (.own r.name r.key r.port) r.binder)
  for m in mems do
    if m.read.isNone then err := firstBreach err m.pos (.noPort m.name false)
    else if m.write.isNone then err := firstBreach err m.pos (.noPort m.name true)
  let mut first : Option (ChildDecl × Nat) := none
  for (c, k) in w.body.children.zipIdx do
    if w.bound.getD k 0 < c.iface.inputs then
      if first.all fun (d, _) => before c.pos d.pos then first := some (c, k)
  if let some (c, k) := first then
    -- Entries of one declaration have one position, so the declaration order decides.
    let earlier (q f : Port) := before q.pos f.pos || (q.pos == f.pos && q.order < f.order)
    let free := c.iface.ports.fold (init := none) fun f _ q =>
      if q.input && !w.inputs.contains (k, q.id) && f.all (earlier q ·) then some q else f
    err := firstBreach err c.pos <| match free with
      | some q => .input c.name q.name q.key
      | none => .input c.name "" none
  if let some (p, x) := err then fail .S018 p (x.text (← read).itemName)

/-!
The interface of a done instantiation with the port families `fams` of its module and the table
of public names `pub` of its body (section 5.6). It holds the entries that the body declared at
run time, and each family of `fams` or of `pub`.
-/
def iface (name : Name) (b : Body) (fams : Std.HashMap Nat (Bool × Pos))
    (pub : Std.HashMap Nat (Public × Pos × Nat)) : Iface :=
  ⟨name,
   b.ports.zipIdx.foldl (fun m (q, j) =>
     m.insert (q.sym, q.key) ⟨q.name, q.sym, q.key, q.input, q.ty, q.pos, j⟩) {},
   (b.ports.filter (·.input)).size, b.domain,
   pub.fold (init := fams) fun m y (f, p, _) => match f with
     | .family i => m.insert y (i, p)
     | .scalar => m⟩

/-!
The serialization of an `InstantiationId` at the statement `pos`. It charges the walk that
measures it, then its length in bytes, before it makes the text (section 5.4).
-/
def serialize (pos : Pos) (m : String) (vs : List Value) : Eval.M String := do
  charge pos (vs.map Value.measureCharge).sum
  let parts := vs.map Value.serialize
  charge pos (InstantiationId.renderSize m parts)
  return InstantiationId.render m parts

end Silicon.Source.Elab
