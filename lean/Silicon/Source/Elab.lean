-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval

/-!
This module holds the instantiations of slice 1 and the checks for each instantiation.
Sections 5.3, 6.1, and 6.2 of the front-end spec define them. `elaborate` runs the top
selection and each instantiation that it reaches, in the evaluation order that section 5.2
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

- A module statement runs in the walk of this module. A `let`, an assignment, and an
  expression statement run in `Eval`, as in a function body.
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
- A register in a combinational module is `S017` at the statement, before its type.
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
  gives one at the `instance` statement. The error with the lowest position wins.
- `S016` comes from the guards of `Eval` (section 9.4). The word type and the depth of a `mem`
  statement are structural contexts. A function declares no resource and binds nothing.
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
  modify fun s => { s with inst.work.needs := s.inst.work.needs.push ⟨x, p, 0⟩ }
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
The index of each step of `sels` of a `:=` target, in source order (section 5.2). An index step
charges 1, then its index evaluates and is static (`S011`). Another step has no index here.
-/
def targetKeys (n : Nat) (sels : List Sel) : Eval.M (List (Sel × Option Value)) := do
  let mut keys : Array (Sel × Option Value) := #[]
  for sel in sels do
    match sel with
    | .index q [i] =>
      charge q 1
      keys := keys.push (sel, some (← static i.pos (← need i (← eval n i)).value))
    | .index q _ =>
      charge q 1
      fail .S010 q "an index of a value has one argument"
    | _ => keys := keys.push (sel, none)
  return keys.toList

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

/-! The value of the root `root` of a `:=` target. A local gives its value with no charge. -/
def targetRoot (n : Nat) (root : Resolve.Expr) : Eval.M Val := do
  match root with
  | .name _ _ (.local id) => do
    match (← get).frame[id]? with
    | some sl => pure sl.value
    | none => pure (← need root (← eval n root)).value
  | _ => pure (← need root (← eval n root)).value

/-!
The part that the `:=` target `e` selects. A root that is not a local evaluates first. Then
the indices evaluate (`targetKeys`), and a local root gives its value after them. One walk then
runs the steps from the root outward (`targetStep`). Another root has no slot, and its value
names it in the text of `S017`. The target is an identity, so it opens no window and charges
no held root.
-/
def targetPart (n : Nat) (e : Resolve.Expr) : Eval.M Val := do
  let (root, sels) := (chain e).getD (e, [])
  let early ← match root with
    | .name _ _ (.local _) => pure none
    | _ => do pure (some (← targetRoot n root))
  let keys ← targetKeys n sels
  let mut v ← match early with
    | some v => pure v
    | none => targetRoot n root
  for key in keys do
    v ← targetStep e.pos v key
  return v

/-!
The target of a `:=` binding: a register, a wire, an own output, or a child input. A handle
alias and the steps of `targetPart` can select it. Each other part is `S017` at the start of
the target. `S018` counts the target by its resource.
-/
def target (n : Nat) (e : Resolve.Expr) : Eval.M Target := do
  match ← targetPart n e with
  | .handle (.res r k t path) => return .own r k t path
  | .handle (.input k path q) => return .child k path q
  | v => fail .S017 e.pos (kindText v.about)

/-! Records the binding of `t` to `h`. The second binding of one target is an `S018`. -/
def bindTarget (p : Pos) (t : Target) (h : Agg) : Eval.M Unit := do
  let second : Error := ⟨.S018, p, "a second binding of one target"⟩
  let w := (← get).inst.work
  match t with
  | .own r k t path =>
    let c := (w.needs[k]?.map (·.count)).getD 0
    if c == 1 then modify fun s => { s with inst.work.dup := earlier s.inst.work.dup second }
    modify fun s =>
      { s with inst.work.needs := s.inst.work.needs.modify k fun r => { r with count := c + 1 } }
    modifyBody fun b => { b with binds := b.binds.push ⟨.own r t path, h, p⟩ }
  | .child k path q =>
    let c := w.inputs.getD (k, q.sym) 0
    if c == 0 then
      modify fun s => { s with inst.work.bound := s.inst.work.bound.modify k (· + 1) }
    if c == 1 then modify fun s => { s with inst.work.dup := earlier s.inst.work.dup second }
    modify fun s => { s with inst.work.inputs := s.inst.work.inputs.insert (k, q.sym) (c + 1) }
    modifyBody fun b =>
      { b with binds := b.binds.push ⟨.child k path (portName q.name) q.ty, h, p⟩ }

/-!
The value of a `:=` binding of the type `t` at `p`, after its typed use. A static scalar becomes
a hardware constant. A static value of another type is empty or has only static leaves, so it
stays static. A hardware value and a hardware aggregate stay as they are.
-/
def sinkValue (p : Pos) (t : Ty) : Val → Eval.M Agg
  | .static v =>
    match t with
    | .bool | .uint _ | .sint _ => do return .hw (← lit p v)
    | _ => pure (.static v)
  | .hw h => pure (.hw h)
  | .agg a => pure a
  | v => fail .S010 p s!"{v.text} is not data"

/-!
The binding rule at the end of a body. A missing binding of an own resource is at its
declaration, and one of a child input is at the `instance` statement. The counts select the
first child with a free input, so only the interface of that child is searched. The name is
that of its free input with the first source position.
-/
def bindings : Eval.M Unit := do
  let w := (← get).inst.work
  let mems := (← get).naming.mems
  let mut err := w.dup
  for r in w.needs do
    if r.count == 0 then err := earlier err ⟨.S018, r.pos, s!"`{r.name}` has no binding"⟩
  for m in mems do
    if let some e := m.dup then err := earlier err e
    if m.read.isNone then
      err := earlier err ⟨.S018, m.pos, s!"the memory `{m.name}` has no `read_port`"⟩
    else if m.write.isNone then
      err := earlier err ⟨.S018, m.pos, s!"the memory `{m.name}` has no `write_port`"⟩
  let mut first : Option (ChildDecl × Nat) := none
  for (c, k) in w.body.children.zipIdx do
    if w.bound.getD k 0 < c.iface.inputs then
      if first.all fun (d, _) => before c.pos d.pos then first := some (c, k)
  if let some (c, k) := first then
    let free := c.iface.ports.fold (init := none) fun f _ q =>
      if q.input && !w.inputs.contains (k, q.sym) && f.all (before q.pos ·.pos) then some q else f
    let x := (free.map (·.name)).getD ""
    let msg := s!"the input `{x}` of the instance `{c.name}` has no binding; "
    err := earlier err ⟨.S018, c.pos, msg ++ s!"bind it with `{c.name}.{x} := ...;`"⟩
  if let some e := err then fail e.code e.pos e.msg

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

/-!
The walk of a module body. `stmt` and `block` are entry functions as in `Eval`. A `let`, an
assignment, a `return`, and an expression statement run in `Eval.stmt`, which charges them.
-/
mutual
  def stmt (b : Nat) (s : Resolve.Stmt) : Eval.M Unit :=
    match s with
    | .local .. | .assign .. | .ret .. | .expr .. | .alias .. => do let _ ← Eval.stmt b s
    | _ =>
      match b with
      | 0 => exhausted s.pos
      | n + 1 => do
        charge s.pos 1
        match s with
        | .input p x ty | .output p x ty => do
          let t ← dataType p (← typeExpr n ty)
          let v ← port p (s matches .input ..) x t
          bindLocal x.id ⟨some t, false, v⟩
        | .reg p x ty init => do
          if (← get).inst.work.body.domain.isNone then
            fail .S017 p "a combinational module has no register"
          let t ← dataType p (← typeExpr n ty)
          let o ← need init (← eval n init)
          copy p o
          let v ← conform p t (← static p (← settle p t o.value))
          let path ← fresh x.id x.name.name
          modifyBody fun b => { b with regs := b.regs.push ⟨path, t, v, p⟩ }
          bindLocal x.id ⟨some t, false, ← resource .reg path t p x.name.name⟩
        | .wire p x ty => do
          let t ← dataType p (← typeExpr n ty)
          let path ← fresh x.id x.name.name
          modifyBody fun b => { b with wires := b.wires.push ⟨path, t, p⟩ }
          bindLocal x.id ⟨some t, false, ← resource .wire path t p x.name.name⟩
        | .mem p x w d => do
          if (← get).inst.work.body.domain.isNone then
            fail .S017 p "a combinational module has no memory"
          let t ← memWord p (← typeExpr n w)
          let k ← memDepth p (← structural do return (← need d (← eval n d)).value)
          let path ← fresh x.id x.name.name
          let id := (← get).naming.mems.size
          let m : Mem := { name := x.name.name, path := path, word := t, depth := k, pos := p }
          modify fun s => { s with naming.mems := s.naming.mems.push m }
          bindLocal x.id ⟨none, false, .handle (.mem id path t k)⟩
        | .connect p tgt v => do
          let t ← target n tgt
          let o ← need v (← eval n v)
          let ty := match t with
            | .own _ _ ty _ => ty
            | .child _ _ q => q.ty
          bindTarget p t (← sinkValue p ty (← typedUse p ty o.ref o.value .value))
        | .inst p u _ i xs => do
          let tvs ← arguments (eval n) (typeExpr n) p i xs
          let some (.module _ m _ ds _) := (← read).items[i]?
            | fail .S010 p "an instance needs a module"
          if (← get).inst.work.body.domain.isNone && !ds.isEmpty then
            fail .S017 p s!"a combinational module has no clocked child `{m.name}`"
          let (c, _) ← instantiate n p i tvs
          let path ← fresh u.id u.name.name
          let k := (← get).inst.work.body.children.size
          modifyBody fun b => { b with children := b.children.push ⟨path, c, p, u.name.name⟩ }
          modify fun s => { s with inst.work.bound := s.inst.work.bound.push 0 }
          -- The converted arguments paid for their sizes, so the type adds no charge.
          let t := Ty.inst i m.name (tvs.map (·.2)).toArray
          bindLocal u.id ⟨none, false, .handle (.inst k path c t)⟩
        | .ctIf p c yes no => do
          if ← test p (← need c (← eval n c)).value then block n p yes
          else if let some ss := no then block n p ss
        | .ctFor p i lo hi body => do
          let o ← need lo (← eval n lo)
          let a ← int p o.value
          hold o
          let z ← int p (← need hi (← eval n hi)).value
          release o
          let count ← range p a z
          let mut v := a
          for _ in [0:count] do
            iteration p i v (block n p body)
            v := v + 1
        | .block _ ss => for s in ss do stmt n s
        | .local .. | .assign .. | .ret .. | .expr .. | .alias .. => pure ()
  termination_by (b, 1)

  /-- A block at `pos`. It charges as a statement. -/
  def block (b : Nat) (pos : Pos) (ss : List Resolve.Stmt) : Eval.M Unit :=
    match b with
    | 0 => exhausted pos
    | n + 1 => do
      charge pos 1
      for s in ss do stmt n s
  termination_by (b, 1)

  /--
  The instantiation of the module item `i` with the converted arguments `tvs` and their
  parameter types, for the statement at `pos`. The parameters bind to them with no charge. The
  result is its interface and its index among the done instantiations.
  -/
  def instantiate (n : Nat) (pos : Pos) (i : Nat) (tvs : List (Ty × Value)) :
      Eval.M (Iface × Nat) := do
    let some (.module mp m ps ds body) := (← read).items[i]?
      | fail .S010 pos "an instance needs a module"
    let vs := tvs.map (·.2)
    let id : InstantiationId := ⟨m.name, vs⟩
    let key ← serialize pos m.name vs
    let s := (← get).inst
    match s.table[key]? with
    | some .inProgress =>
      fail .S019 pos s!"the instantiation of `{m.name}` depends on itself"
    | some (.done k) =>
      match s.done[k]? with
      | some d => return (d.iface, k)
      | none => fail .S019 pos s!"the instantiation of `{m.name}` is not in the table"
    | none => nested pos do
      let name := moduleName (← read).digest id key
      charge pos (byteSize name)
      let text := encode name
      if s.names.contains text then
        fail .S019 pos s!"two instantiations have the emitted name `{text}`"
      let parent := s.work
      let naming := (← get).naming
      modify fun t => { t with
        inst.table := t.inst.table.insert key .inProgress,
        inst.names := t.inst.names.insert text,
        inst.work := { body := { domain := ds.head?.map fun (d : Binder) => d.name.name } },
        naming := {} }
      let (made, used) ← measure do
        inFrame none <| withTheReader Ctx (fun c =>
            { c with item := i, frame := ⟨none, 0⟩, inst := text, calls := [] }) do
          for (q, t, v) in ps.zip tvs do
            bindLocal q.name.id ⟨some t, false, .static v⟩
          for d in ds do
            bindLocal d.id ⟨none, false, .handle (.domain d.name.name)⟩
          block n mp body
        bindings
        let made := (← get).naming
        modify fun t => { t with naming }
        return made
      let w := (← get).inst.work
      let body := { w.body with lets := made.lets, mems := made.mems }
      let c := iface name body
      let k := (← get).inst.done.size
      modify fun t => { t with
        inst.table := t.inst.table.insert key (.done k),
        inst.done := t.inst.done.push ⟨id, c, body, used - w.spent, mp⟩,
        inst.work := { parent with spent := parent.spent + used } }
      return (c, k)
  termination_by (n + 1, 0)
end

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
