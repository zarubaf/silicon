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

1. It evaluates the arguments from left to right. Each argument is static (`S011`). A literal
   with `[]` takes the type of its parameter (`arguments`).
2. It charges the recursive size of the arguments, also for a done instantiation. Then the
   serialization charges the square of the size of each integer, and its length in bytes.
3. A clocked child in a combinational module is `S017` at the statement.
4. An instantiation in progress is `S019` at the statement. A done one gives its interface.
5. A new one nests one level deeper (`S015`). Its emitted name charges its length in bytes,
   and it must be new (`S019`). Then it goes in progress, runs its body, checks its bindings,
   and is done.

The `InstantiationId` holds the arguments as they evaluate, before the typed use at the
parameters. The parameters then bind in the body of the new instantiation, as a typed use.

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
- A `:=` target resolves without a charge. A register, a wire, an own output, and a child input
  are targets, also through a handle alias. Each other target fails with `S017` (rule). A
  target with an index or a selector `.N` is a part of a resource: `S017` at the target.
- The value of `:=` is a typed use. It copies a reference, as a `let` with a type does. A read
  of an aggregate handle charges the handle, then the zero size of its type (`copyUse`).
- A `:=` binding holds its value as an aggregate part. A static scalar becomes a hardware
  constant. An aggregate or an empty value stays one part, so the lowering makes its leaf
  statements and charges each one before it makes it.
- `S018` errors wait for the end of the body. The second binding of a resource gives one.
  A resource without a binding gives one at its declaration. A child input without a binding
  gives one at the `instance` statement. The error with the lowest position wins.
- `S016` cannot occur in slice 1. An arm of a hardware `if` is an expression. A function of
  slice 1 declares no resource and binds nothing.
- The owner guard of section 9.5 has no check in slice 1. Module arguments are static
  (`S011`), and ports carry data, so a handle cannot reach another owner.
- The units of an instantiation are its charges from the start of its parameters to the end
  of its binding check. The units of its new children are not part of them. The charges of
  an `instance` statement belong to the parent. The arguments of the top selection belong to
  no instantiation.

Each table grows only with charged work: a new instantiation charges its body, and each
declaration, binding, and child charges its statement.
-/
namespace Silicon.Source.Elab

open Resolve Names Eval

/-! A port declaration. A port keeps its source name. -/
structure PortDecl where
  name : String
  sym : Nat
  input : Bool
  ty : Ty
  pos : Pos

structure RegDecl where
  path : Path
  ty : Ty
  init : Value
  pos : Pos

structure WireDecl where
  path : Path
  ty : Ty
  pos : Pos

/-! A child instance: its path, the interface of its instantiation, and its statement. -/
structure ChildDecl where
  path : Path
  iface : Iface
  pos : Pos

/-!
The target of a `:=` binding: an own resource, or an input of the child number `index`. The
input names its port by its core name, and `ty` gives its leaves.
-/
inductive Sink where
  | own (kind : Kind) (ty : Ty) (path : Path)
  | child (index : Nat) (inst : Path) (port : Name) (ty : Ty)

/-! A `:=` binding. Its value has the type of the sink, and the lowering takes it leaf by leaf. -/
structure Bind where
  sink : Sink
  value : Agg
  pos : Pos

/-!
The hardware description of one instantiation, in evaluation order. A combinational module
has no domain.
-/
structure Body where
  domain : Option String
  ports : Array PortDecl := #[]
  regs : Array RegDecl := #[]
  wires : Array WireDecl := #[]
  lets : Array Let := #[]
  children : Array ChildDecl := #[]
  binds : Array Bind := #[]

/-! A resource that needs one binding, by its number: its declaration and its bindings. -/
structure Need where
  name : String
  pos : Pos
  count : Nat

/-!
The work of the current instantiation. The resource number indexes `needs`, and the instance
number indexes `bound`. `inputs` counts the bindings of each child input. `dup` holds the first
`S018` of a second binding by position. `spent` is the fuel of the new children.
-/
structure Work where
  body : Body
  needs : Array Need := #[]
  bound : Array Nat := #[]
  inputs : Std.HashMap (Nat × Nat) Nat := {}
  dup : Option Error := none
  spent : Nat := 0

/-! The state of an `InstantiationId` in the table of instantiations. -/
inductive Status where
  | inProgress
  | done (index : Nat)

/-!
A done instantiation: its identity, its interface, its description, its units, and the position
of its module item.
-/
structure Inst where
  id : InstantiationId
  iface : Iface
  body : Body
  units : Nat
  pos : Pos

/-!
The state of an elaboration. `table` maps the serialization of each `InstantiationId` to its
state, and `names` holds the emitted name of each instantiation that is in progress or done.
`digest` makes the digest of an emitted name, so a test can replace it.
-/
structure St where
  digest : String → String
  table : Std.HashMap String Status := {}
  names : Std.HashSet String := {}
  done : Array Inst := #[]
  work : Work

abbrev EM := StateT St Eval.M

instance : Runs EM := {}

/-!
A design: the done instantiations in the order they finish, and the top among them. `fields`
gives the fields with a leaf of each struct type of the design: the number, the name, and the
type of each, in declaration order. The lowering thus names the leaves of a record, and it skips
an empty field with no step.
-/
structure Design where
  insts : Array Inst
  top : Nat
  fields : Ty → Option (Array (Nat × String × Ty))

/-!
The fields with a leaf of each done struct specialization, by its number. `elaborate` makes the
table once, from the fields that each specialization paid for when it completed.
-/
def leafFields (items : Array Resolve.Item) (specs : Specs) :
    Array (Option (Array (Nat × String × Ty))) :=
  specs.entries.map fun e => do
    let .done _ fs := e.state | none
    let some (.struct _ _ _ ds) := items[e.item]? | none
    return ((ds.toArray.map (·.name.name)).zip fs).zipIdx.filterMap fun ((x, t), k) =>
      if t.info.leaves = 0 then none else some (k, x, t)

/-! The fields with a leaf of the struct type `t` in the table `table`. -/
def fieldsOf (table : Array (Option (Array (Nat × String × Ty)))) :
    Ty → Option (Array (Nat × String × Ty))
  | .struct k .. => table[k]?.join
  | _ => none

def modifyBody (f : Body → Body) : EM Unit :=
  modify fun s => { s with work.body := f s.work.body }

def slot (id : Nat) : EM (Option Slot) := monadLift (do return (← get).frame[id]? : Eval.M _)

/-!
A port, a register, and a wire have a hardware data type (section 5.1). The metadata gives it,
so a type with a function type at any depth is `S010` with no walk. The type can be empty.
-/
def dataType (p : Pos) (t : Ty) : EM Ty :=
  if t.info.data then pure t
  else fail .S010 p s!"a port, a register, and a wire need a hardware data type, not {t.text}"

/-! A resource that needs one binding. The result is its handle. -/
def resource (k : Kind) (path : Path) (t : Ty) (p : Pos) (x : String) : EM Val := do
  let id := (← get).work.needs.size
  modify fun s => { s with work.needs := s.work.needs.push ⟨x, p, 0⟩ }
  return .handle (.res k id t path)

/-!
The port `x`. Its core name is its source name. The root frame counts it with the bindings of
its name, so a name that is taken is `S019`.
-/
def port (p : Pos) (input : Bool) (b : Binder) (t : Ty) : EM Val := do
  let x := b.name.name
  let sym := (← readThe Ctx).binder b.id
  let taken ← monadLift (do
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
  else monadLift (normalize p (.ref (.name ⟨x, []⟩) t) : Eval.M Val)

/-! The target of a `:=` binding. It refers, so it charges nothing. -/
inductive Target where
  | own (kind : Kind) (id : Nat) (ty : Ty) (path : Path)
  | child (inst : Nat) (path : Path) (port : Port)

def target (p : Pos) (e : Resolve.Expr) : EM Target := do
  let bad : EM Target :=
    fail .S017 p "a `:=` target is a wire, a register, an own output, or a child input"
  match e with
  | .name _ _ (.local id) =>
    match ← slot id with
    | some ⟨_, _, .handle (.res r k t path)⟩ => return .own r k t path
    | some ⟨_, _, .handle (.input k path q)⟩ => return .child k path q
    | _ => bad
  | .field _ (.name _ _ (.local id)) f =>
    match ← slot id with
    | some ⟨_, _, .handle (.inst k path iface)⟩ =>
      match (← readThe Ctx).field f.pos >>= (iface.ports[·]?) with
      | some q =>
        if q.input then return .child k path q
        else fail .S017 p s!"`{f.name}` is an output of the child, not a target"
      | none => fail .S010 p s!"the instance has no port `{f.name}`"
    | _ => bad
  | .index q .. | .select q .. => fail .S017 q "a `:=` target is a whole resource, not a part"
  | _ => bad

/-! Records the binding of `t` to `h`. The second binding of one target is an `S018`. -/
def bindTarget (p : Pos) (t : Target) (h : Agg) : EM Unit := do
  let second : Error := ⟨.S018, p, "a second binding of one target"⟩
  let w := (← get).work
  match t with
  | .own r k t path =>
    let c := (w.needs[k]?.map (·.count)).getD 0
    if c == 1 then modify fun s => { s with work.dup := earlier s.work.dup second }
    modify fun s =>
      { s with work.needs := s.work.needs.modify k fun r => { r with count := c + 1 } }
    modifyBody fun b => { b with binds := b.binds.push ⟨.own r t path, h, p⟩ }
  | .child k path q =>
    let c := w.inputs.getD (k, q.sym) 0
    if c == 0 then modify fun s => { s with work.bound := s.work.bound.modify k (· + 1) }
    if c == 1 then modify fun s => { s with work.dup := earlier s.work.dup second }
    modify fun s => { s with work.inputs := s.work.inputs.insert (k, q.sym) (c + 1) }
    modifyBody fun b =>
      { b with binds := b.binds.push ⟨.child k path (portName q.name) q.ty, h, p⟩ }

/-!
The value of a `:=` binding of the type `t` at `p`, after its typed use. A static scalar becomes
a hardware constant. A static value of another type is empty or has only static leaves, so it
stays static. A hardware value and a hardware aggregate stay as they are.
-/
def sinkValue (p : Pos) (t : Ty) : Val → EM Agg
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
that of its free input with the least symbol.
-/
def bindings : EM Unit := do
  let w := (← get).work
  let mut err := w.dup
  for r in w.needs do
    if r.count == 0 then err := earlier err ⟨.S018, r.pos, s!"`{r.name}` has no binding"⟩
  let mut first : Option (ChildDecl × Nat) := none
  for (c, k) in w.body.children.zipIdx do
    if w.bound.getD k 0 < c.iface.inputs then
      if first.all fun (d, _) => before c.pos d.pos then first := some (c, k)
  if let some (c, k) := first then
    let free := c.iface.ports.fold (init := none) fun f _ q =>
      if q.input && !w.inputs.contains (k, q.sym) && f.all (q.sym < ·.sym) then some q else f
    let x := (free.map (·.name)).getD ""
    err := earlier err ⟨.S018, c.pos, s!"the input `{x}` of the child has no binding"⟩
  if let some e := err then throw e

/-! The interface of a done instantiation. -/
def iface (name : Name) (b : Body) : Iface :=
  ⟨name, b.ports.foldl (fun m q => m.insert q.sym ⟨q.name, q.sym, q.input, q.ty⟩) {},
   (b.ports.filter (·.input)).size, b.domain⟩

/-!
The serialization of an `InstantiationId` at the statement `pos`. It charges the walk that
measures it, then its length in bytes, before it makes the text (section 5.4).
-/
def serialize (pos : Pos) (m : String) (vs : List Value) : EM String := do
  charge pos (vs.map Value.measureCharge).sum
  let parts := vs.map Value.serialize
  charge pos (InstantiationId.renderSize m parts)
  return InstantiationId.render m parts

/-!
The arguments of an instantiation of the item `i` at `pos`, from left to right. Each argument is
static (`S011`) when it evaluates. A literal with `[]` takes the type of its parameter, as the
argument of a call does. Its parameter type then evaluates in the scope of the module, with each
earlier parameter bound to its argument. The parent pays this work.
-/
def arguments (n : Nat) (pos : Pos) (i : Nat) (xs : List Resolve.Expr) : EM (List Value) := do
  let os ← xs.mapM fun x => do
    let o ← need x (← eval n x)
    let v ← match o.value with
      | v@(.pending ..) => pure v
      | v => pure (.static (← static pos v))
    hold o
    return (v, o)
  for (_, o) in os do release o
  let vs := os.map (·.1)
  match (← read).items[i]? with
  | some (.module _ _ ps _ _) =>
    if vs.any (· matches .pending ..) && ps.length == vs.length then
      inFrame none <| withTheReader Ctx (fun c => { c with item := i, frame := ⟨none, 0⟩ }) do
        (ps.zip vs).mapM fun (q, v) => do
          let x ← match v with
            | .pending .. => do static pos (← settle pos (← typeExpr n q.ty) v)
            | v => static pos v
          bindLocal q.name.id ⟨x.ty?, false, .static x⟩
          return x
    else vs.mapM fun v => do static pos v
  | _ => vs.mapM fun v => do static pos v

/-! Runs `act` and gives the fuel that it uses. The result reads only a difference of fuel. -/
def measure (act : EM α) : EM (α × Nat) := do
  let fuel : EM Nat := monadLift (do return (← get).fuel : Eval.M Nat)
  let start ← fuel
  let a ← act
  return (a, start - (← fuel))

/-!
The walk of a module body. `stmt` and `block` are entry functions as in `Eval`. A `let`, an
assignment, a `return`, and an expression statement run in `Eval.stmt`, which charges them.
-/
mutual
  def stmt (b : Nat) (s : Resolve.Stmt) : EM Unit :=
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
          if (← get).work.body.domain.isNone then
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
        | .connect p tgt v => do
          let t ← target p tgt
          let o ← need v (← eval n v)
          let ty := match t with
            | .own _ _ ty _ => ty
            | .child _ _ q => q.ty
          bindTarget p t (← sinkValue p ty (← copyUse p ty o.ref o.value))
        | .inst p u _ i xs => do
          let vs ← arguments n p i xs
          charge p (vs.map Value.size).sum
          if let some (.module _ m _ ds _) := (← read).items[i]? then
            if (← get).work.body.domain.isNone && !ds.isEmpty then
              fail .S017 p s!"a combinational module has no clocked child `{m.name}`"
          let (c, _) ← instantiate n p i vs
          let path ← fresh u.id u.name.name
          let k := (← get).work.body.children.size
          modifyBody fun b => { b with children := b.children.push ⟨path, c, p⟩ }
          modify fun s => { s with work.bound := s.work.bound.push 0 }
          bindLocal u.id ⟨none, false, .handle (.inst k path c)⟩
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
  def block (b : Nat) (pos : Pos) (ss : List Resolve.Stmt) : EM Unit :=
    match b with
    | 0 => exhausted pos
    | n + 1 => do
      charge pos 1
      for s in ss do stmt n s
  termination_by (b, 1)

  /--
  The instantiation of the module item `i` with the arguments `vs`, for the statement at `pos`.
  The result is its interface and its index among the done instantiations.
  -/
  def instantiate (n : Nat) (pos : Pos) (i : Nat) (vs : List Value) : EM (Iface × Nat) := do
    let some (.module mp m ps ds body) := (← read).items[i]?
      | fail .S010 pos "an instance needs a module"
    let id : InstantiationId := ⟨m.name, vs⟩
    let key ← serialize pos m.name vs
    let s ← get
    match s.table[key]? with
    | some .inProgress =>
      fail .S019 pos s!"the instantiation of `{m.name}` depends on itself"
    | some (.done k) =>
      match s.done[k]? with
      | some d => return (d.iface, k)
      | none => fail .S019 pos s!"the instantiation of `{m.name}` is not in the table"
    | none => nested pos do
      let name := moduleName s.digest id key
      charge pos (byteSize name)
      let text := encode name
      if s.names.contains text then
        fail .S019 pos s!"two instantiations have the emitted name `{text}`"
      let parent := s.work
      let naming ← monadLift (do return (← get).naming : Eval.M Naming)
      set { s with table := s.table.insert key .inProgress, names := s.names.insert text,
                   work := { body := { domain := ds.head?.map fun (d : Binder) => d.name.name } } }
      monadLift (modify fun t => { t with naming := {} } : Eval.M Unit)
      let (lets, used) ← measure do
        inFrame none <| withTheReader Ctx (fun c => { c with item := i, frame := ⟨none, 0⟩ }) do
          for (q, v) in ps.zip vs do
            let t ← typeExpr n q.ty
            bindLocal q.name.id ⟨some t, false, .static (← conform pos t v)⟩
          for d in ds do
            bindLocal d.id ⟨none, false, .handle (.domain d.name.name)⟩
          block n mp body
        bindings
        let lets ← monadLift (do return (← get).naming.lets : Eval.M (Array Let))
        monadLift (modify fun t => { t with naming } : Eval.M Unit)
        return lets
      let w := (← get).work
      let body := { w.body with lets }
      let c := iface name body
      let k := (← get).done.size
      modify fun t => { t with
        table := t.table.insert key (.done k),
        done := t.done.push ⟨id, c, body, used - w.spent, mp⟩,
        work := { parent with spent := parent.spent + used } }
      return (c, k)
  termination_by (n + 1, 0)
end

/-!
The elaboration of the top selection at `pos`: the module item `top` with the literal
arguments `xs`. The arguments charge as those of an `instance` statement. The result is the
design and the used fuel.
-/
def elaborate (budget : Budget) (items : Array Resolve.Item) (digest : String → String)
    (pos : Pos) (top : Nat) (xs : List Resolve.Expr) : Except Error (Design × Nat) :=
  Eval.run budget items fun n => do
    let go : EM Nat := do
      let vs ← arguments n pos top xs
      charge pos (vs.map Value.size).sum
      return (← instantiate n pos top vs).2
    let (k, s) ← go.run { digest, work := { body := { domain := none } } }
    let table := leafFields items (← get).specs
    return ⟨s.done, k, fieldsOf table⟩

/-! The output of `cost` (section 8): the total, then the units of each instantiation by name. -/
def costLines (d : Design) (total : Nat) : String :=
  let lines := d.insts.map fun i => (encode i.iface.name, i.units)
  let sorted := lines.qsort fun a b => a.1 < b.1
  sorted.foldl (fun s (x, u) => s ++ s!"{x} {u}\n") s!"total {total}\n"

end Silicon.Source.Elab
