-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Container

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
- A port keeps its source name. The root frame counts it with the other bindings of its name.
  A second port with one name thus fails, and so does a port after a binding of its name.
  The code is `S019`.
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
  else fail .S010 p s!"a port, a register, and a wire need a hardware data type, not {t.text}"

/-! A resource that needs one binding. The result is its handle. -/
def resource (k : Kind) (path : Path) (t : Ty) (p : Pos) (x : String) : Eval.M Val := do
  let id := (← get).inst.work.needs.size
  modify fun s =>
    { s with inst.work.needs := s.inst.work.needs.push { name := x, pos := p, count := 0 } }
  return .handle (.res k id t path)

/-!
The port `x`. Its core name is its source name. The root frame counts it with the bindings of
its name, so a name that is taken is `S019`.
-/
def port (p : Pos) (input : Bool) (b : Binder) (t : Ty) : Eval.M Val := do
  let x := b.name.name
  let sym := (← readThe Ctx).binder b.id
  let taken ← (do
    let s ← get
    let key := (0, Tag.sym sym)
    let v := s.naming.versions.getD key 0
    set { s with naming.versions := s.naming.versions.insert key (v + 1) }
    return v != 0 : Eval.M Bool)
  if taken then fail .S019 p s!"two declarations have the core name `{x}`"
  modifyBody fun d => { d with ports := d.ports.push ⟨x, sym, input, t, p⟩ }
  -- An input refers to its name: a scalar is hardware, and an aggregate a lazy reference. An
  -- empty input stays a reference too, so only a read of it pays its zero (`Eval.name`).
  if !input then resource .output ⟨x, []⟩ t p x
  else if t.info.leaves = 0 then pure (.agg (.ref (.name ⟨x, []⟩) t))
  else normalize p (.ref (.name ⟨x, []⟩) t)

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

/-! The `S017` text "Child output as a `:=` target" of section 6.2, for the output `f`. -/
def outputText (f : String) : String :=
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
    match (← read).field f.pos >>= (iface.ports[·]?) with
    | some port =>
      if port.input then return .handle (.input k path port)
      else fail .S017 s (outputText f.name)
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

/-! Records the `S018` data `x` at `p`. The first by position wins (section 6.2). -/
def breach (p : Pos) (x : Breach) : Eval.M Unit :=
  modify fun s => { s with inst.work.dup := firstBreach s.inst.work.dup p x }

/-!
The helper of a second binding or port call at `p` whose first one is at `b`. When both are at
`p`, one `:=` or call runs again, and in a function body its text names the function (section
6.2).
-/
def again (p b : Pos) : Eval.M (Option Nat) := do
  if b == p then return (← read).helper else return none

/-! The `S018` data of a second binding at `p` of `r`, with its declaration at `d`. -/
def second (p : Pos) (r : Res) (b d : Pos) : Eval.M Breach := do
  match ← again p b with
  | some h => return .secondIn r h
  | none => return .second r b d

/-!
Records the binding of `t` to `h` at `p`. The second binding of one target is an `S018`, and
the first binding keeps its position for its text.
-/
def bindTarget (p : Pos) (t : Target) (h : Agg) : Eval.M Unit := do
  let w := (← get).inst.work
  match t with
  | .own r k t path =>
    if let some n := w.needs[k]? then
      if n.count == 1 then breach p (← second p (.own n.name) (n.first.getD p) n.pos)
      modify fun s => { s with inst.work.needs := s.inst.work.needs.modify k fun r =>
        { r with count := n.count + 1, first := r.first <|> some p } }
    modifyBody fun b => { b with binds := b.binds.push ⟨.own r t path, h, p⟩ }
  | .child k path q =>
    let (c, b) := w.inputs.getD (k, q.sym) (0, p)
    if c == 0 then
      modify fun s => { s with inst.work.bound := s.inst.work.bound.modify k (· + 1) }
    if c == 1 then
      let (u, d) := ((w.body.children[k]?).map fun c => (c.name, c.pos)).getD ("", p)
      breach p (← second p (.input u q.name) b d)
    modify fun s => { s with inst.work.inputs := s.inst.work.inputs.insert (k, q.sym) (c + 1, b) }
    modifyBody fun b =>
      { b with binds := b.binds.push ⟨.child k path (portName q.name) q.ty, h, p⟩ }

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
    if r.count == 0 then err := firstBreach err r.pos (.unbound r.name)
  for m in mems do
    if m.read.isNone then err := firstBreach err m.pos (.noPort m.name false)
    else if m.write.isNone then err := firstBreach err m.pos (.noPort m.name true)
  let mut first : Option (ChildDecl × Nat) := none
  for (c, k) in w.body.children.zipIdx do
    if w.bound.getD k 0 < c.iface.inputs then
      if first.all fun (d, _) => before c.pos d.pos then first := some (c, k)
  if let some (c, k) := first then
    let free := c.iface.ports.fold (init := none) fun f _ q =>
      if q.input && !w.inputs.contains (k, q.sym) && f.all (before q.pos ·.pos) then some q else f
    err := firstBreach err c.pos (.input c.name ((free.map (·.name)).getD ""))
  if let some (p, x) := err then fail .S018 p (x.text (← read).itemName)

/-! The interface of a done instantiation. -/
def iface (name : Name) (b : Body) : Iface :=
  ⟨name, b.ports.foldl (fun m q => m.insert q.sym ⟨q.name, q.sym, q.input, q.ty, q.pos⟩) {},
   (b.ports.filter (·.input)).size, b.domain⟩

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
