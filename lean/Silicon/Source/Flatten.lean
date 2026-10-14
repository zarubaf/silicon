-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Check
import Silicon.Source.Layout

/-!
The lowering of section 7 of the front-end spec. `flatten` maps the hardware descriptions of
`Source.Elab` to a `Core.Design`. `checkDesign` then runs `Core.check` on it, as pass 6.

Each instantiation gives one core module with its emitted name. Each name of a description is
its structural path, encoded by `Source.Names`. The expressions follow the table of section 7.4,
and the statements, the ports, and the domain follow section 7.5.

The lowering charges the fuel that elaboration leaves (section 5.4). A core node is one form of
the text: the design, a module, a port, a statement, a reset, a connection, or an expression
node. Each core node charges 1 unit. Each field of a core name charges its length in bytes, at
each place where it occurs. A charge comes before the node or the name that it pays. Above the
fuel, the result is `S015` at the source position of the node.

These rules settle the open points of the spec:

- A made field that holds an integer charges the square of the size of the integer, at least 1.
  A call site, a version, and a temporary are such fields. Their bytes are at most 20 times
  this charge.
- The fields of an emitted module name charge as those of each other core name.
- The height of a hardware value counts its nodes: a leaf has the height 1. A reference to a
  named binding is a leaf. The value of a statement never binds for its height.
- Each core node takes the position of the source node that made it. A statement of a `:=`
  binding takes the position of the binding. A temporary takes the position of its operand. A
  port takes its declaration, and a domain port takes the module.
- An operand that a rule uses twice is bound to a temporary unless it lowers to a name, a child
  output, or a constant. Such a leaf is copied, and the copy charges as a new node.
- The temporaries of one node bind after its operands lower, in operand order. Inner nodes thus
  bind first. Each binding with `:=` is its own statement, also a connection of a child input.
- A shared operand (`Op.share`) binds to a temporary at its first lowering in the module. That
  statement gives it its next number, after the temporaries of the operand itself. Each later
  use, also in another statement, refers to it, as a use of a temporary does.
- The lowering runs the instantiations in the order they finish. In one module, it lowers the
  module, the domain ports, and the ports in declaration order. Then it lowers the registers,
  the named bindings, the `:=` bindings, and the instances. A connection lowers with its `:=`
  binding.
- A port, a register, and a `:=` binding lower one leaf at a time, in packing order
  (`Layout.foldLeaves`). Each leaf charges its node and its name before it exists, so no list
  of leaves comes before its charges. An empty one lowers to nothing. A leaf statement of a `:=`
  binding has the leaf name as its target, so its temporaries count from 0.
- A static leaf of a bound value lowers to a constant. A leaf of a reference refers to its core
  name, or to its child output, at the position of the statement.
- The left spine of a chain of binary nodes lowers in a loop, in the order of the recursion. The
  chain of `==` on an aggregate is as long as its leaf count. The recursion only enters the
  operands of the chain, so its depth does not grow with the chain.
- The charges of a module belong to the units of its instantiation. The design node and the name
  of the top belong to no instantiation.
- A core `E008` becomes `S020` at its position. `Core.check` reports the cycle node with the
  lowest position over all modules. Each other core error is a defect of this elaborator.
-/
namespace Silicon.Source.Flatten

open Names Eval Elab

/-! The failure of a lowering: a source error, or a defect of the reference elaborator. -/
inductive Failure where
  | source (e : Error)
  | defect (msg : String)

/-!
The fuel, the temporaries of the current module, and the number of the next temporary of the
current statement. `shares` holds the temporary of each shared operand (`Op.share`) of the
current module that a statement already bound.
-/
structure St where
  fuel : Nat
  temps : Array Core.Stmt := #[]
  count : Nat := 0
  shares : Std.HashMap Nat Path := {}

abbrev FM := StateT St (Except Failure)

def charge (pos : Pos) (units : Nat) : FM Unit := do
  let s ← get
  if units ≤ s.fuel then set { s with fuel := s.fuel - units }
  else throw (.source ⟨.S015, pos, s!"the fuel cannot pay {intText units} unit(s) of the " ++
    s!"lowering; {intText s.fuel} remain"⟩)

def defect (msg : String) : FM α := throw (.defect msg)

def cpos (p : Pos) : Core.Pos := ⟨p.line, p.col, []⟩

/-!
The charge of a field: its length in bytes, at least 1. A made field that holds an integer
charges the square of the size of the integer instead, at least 1, before its decimal form.
-/
def fieldUnits : Field → Nat
  | .user x => max 1 x.utf8ByteSize
  | .int v => (Value.int v).measureCharge
  | .call k | .version k | .temp k | .elem k => (Value.int k).measureCharge
  | .bool _ => 2
  | .digest h => 2 + h.utf8ByteSize
  | .role r => r.text.utf8ByteSize

/-! The charge of a name: the charge of each field of `encode p`, with the field `0k`. -/
def nameUnits (p : Name) : Nat :=
  let head := fieldUnits (.user p.head)
  if keyword p then head + 2 else p.rest.foldl (fun n f => n + fieldUnits f) head

/-! The charge of the name of a path, from its fields in any order. -/
def pathUnits (p : Path) : Nat :=
  if p.inner.isEmpty then nameUnits ⟨p.outer, []⟩
  else p.inner.foldl (fun n f => n + fieldUnits f) (fieldUnits (.user p.outer))

/-! The core name of a path. It charges the fields first. -/
def pathText (pos : Pos) (p : Path) : FM String := do
  charge pos (pathUnits p)
  return encode p.name

def nameText (pos : Pos) (p : Name) : FM String := do
  charge pos (nameUnits p)
  return encode p

/-! The width of a hardware type. -/
def width : Ty → Nat
  | .uint w | .sint w => w
  | _ => 1

/-!
The constant of a static value at a hardware use: its value modulo `2^w`. Elaboration gives
only a Boolean or a finite value there, so another value is a defect.
-/
def constOf (p : Core.Pos) : Value → FM Core.Expr
  | .bool b => pure (.const p 1 (if b then 1 else 0))
  | .uint w x | .sint w x => pure (.const p w x.toNat)
  | v => defect s!"a hardware constant of {v.text}"

/-!
A lowered expression and its effective height. A leaf and a reference to a temporary have the
height 1 and the charge of a copy of them.
-/
structure Low where
  expr : Core.Expr
  copy : Option Nat
  height : Nat

/-! Binds `e` of width `w` to the next temporary `<target>$<k>t` at `opPos`. -/
def bindTemp (pos : Pos) (target : Path) (w : Nat) (opPos : Pos) (e : Core.Expr) : FM Path := do
  let path := target.push (.temp (← get).count)
  modify fun s => { s with count := s.count + 1 }
  charge pos 1
  let name ← pathText pos path
  modify fun s => { s with temps := s.temps.push (.let_ (cpos opPos) name w e) }
  return path

/-! A reference to the temporary `path`. -/
def tempRef (pos : Pos) (path : Path) : FM Core.Expr := do
  charge pos 1
  return .ref (cpos pos) (← pathText pos path)

/-!
The operand `lo` of width `w` for a rule that uses it twice, and its effective height. A leaf is
copied. Another operand is bound to a temporary at the position `opPos`, both uses refer to it,
and its effective height is 1.
-/
def twice (pos : Pos) (target : Path) (w : Nat) (opPos : Pos) (lo : Low) :
    FM (Core.Expr × Core.Expr × Nat) := do
  match lo.copy with
  | some u =>
    charge pos u
    return (lo.expr, lo.expr, lo.height)
  | none =>
    let path ← bindTemp pos target w opPos lo.expr
    return (← tempRef pos path, ← tempRef pos path, 1)

/-!
A node whose effective height reaches 64 binds to a temporary, unless it is the value of the
statement. Its operands have effective heights below 64. Each inline expression is thus at most
64 nodes high, and a core expression nests at most 256 levels.
-/
def deep (pos : Pos) (target : Path) (w : Nat) (root : Bool) (lo : Low) : FM Low := do
  if root || lo.height < 64 then return lo
  let path ← bindTemp pos target w pos lo.expr
  return ⟨← tempRef pos path, some (1 + pathUnits path), 1⟩

/-! The core operation of a binary node that is not a shift, or its predicate. -/
def binOp (op : BinOp) (signed : Bool) : Option (Core.BinOp ⊕ Core.Pred) :=
  match op with
  | .addw => some (.inl .add) | .subw => some (.inl .sub) | .mulw => some (.inl .mul)
  | .and | .land => some (.inl .and) | .or | .lor => some (.inl .or)
  | .xor => some (.inl .xor)
  | .eq => some (.inr .eq) | .ne => some (.inr .ne)
  | .lt | .le | .gt | .ge => some (.inr (pred op signed))
  | _ => none

def signed : Ty → Bool
  | .sint _ => true
  | _ => false

/-! The core node of a binary operation or of a predicate. -/
def binExpr (c : Core.Pos) : Core.BinOp ⊕ Core.Pred → Core.Expr → Core.Expr → Core.Expr
  | .inl k, a, b => .bin c k a b
  | .inr k, a, b => .icmp c k a b

/-!
A link of the left spine of a chain of binary nodes below a node of the measure `b`. It holds the
position and the type of the node, its core operation, and its right operand.
-/
structure Link (b : Nat) where
  pos : Pos
  ty : Ty
  op : Core.BinOp ⊕ Core.Pred
  right : { x : Hw // sizeOf x < b }

/-!
The lowering of a hardware value for the statement of `target`. Each case charges its own core
nodes, then lowers its operands from left to right. `root` marks the value of the statement.

The left spine of a chain of binary nodes lowers in a loop, in the order of the recursion. Each
node charges before its left operand, and each node binds after its right operand. The chain of
`==` on an aggregate is as long as its leaf count, so the recursion never follows the spine.
-/
def lower (target : Path) (root : Bool) : Hw → FM Low
  | .node p t sz op args => do
    let c := cpos p
    let up (h : Nat) := h + 1
    let lo ← match op, args with
    | .ref path, [] =>
      let u := 1 + pathUnits path
      charge p 1
      pure ⟨.ref c (← pathText p path), some u, 1⟩
    | .out inst q, [] =>
      let u := 1 + pathUnits inst + nameUnits q
      charge p 1
      let i ← pathText p inst
      pure ⟨.port c i (← nameText p q), some u, 1⟩
    | .lit v, [] =>
      charge p 1
      pure ⟨← constOf c v, some 1, 1⟩
    | .un .not, [a] =>
      charge p 2
      let a ← lower target false a
      pure ⟨.bin c .xor a.expr (.const c 1 1), none, up a.height⟩
    | .un .inv, [a] =>
      charge p 1
      let a ← lower target false a
      pure ⟨.un c .not a.expr, none, up a.height⟩
    | .un .neg, [a] =>
      charge p 2
      let a ← lower target false a
      pure ⟨.bin c .sub (.const c (width t) 0) a.expr, none, up a.height⟩
    | .bin op, [a, n] =>
      if op == .shl || op == .shr then
        let w := width t
        let k : Core.BinOp := if op == .shl then .shl else if signed t then .shrs else .shru
        match _hn : n with
        | .node _ _ _ (.lit (.int v)) [] =>
          charge p 2
          let a ← lower target false a
          pure ⟨.bin c k a.expr (.const c w (min v.toNat w)), none, up a.height⟩
        | _ =>
          let wc := width n.ty
          if wc == w then
            charge p 1
            let a ← lower target false a
            let n ← lower target false n
            pure ⟨.bin c k a.expr n.expr, none, up (max a.height n.height)⟩
          else if wc < w then
            charge p 3
            let a ← lower target false a
            let n ← lower target false n
            let e := Core.Expr.bin c k a.expr (.bin c .concat (.const c (w - wc) 0) n.expr)
            pure ⟨e, none, up (max a.height n.height)⟩
          else
            charge p (if k == .shrs then 7 else 6)
            let la ← lower target false a
            let ln ← lower target false n
            let (a1, a2, ha) ← if k == .shrs then twice p target w a.pos la
              else pure (la.expr, la.expr, la.height)
            let (n1, n2, hn) ← twice p target wc n.pos ln
            let fill := if k == .shrs then .bin c .shrs a1 (.const c w (w - 1))
              else .const c w 0
            let over := Core.Expr.icmp c .uge n1 (.const c wc w)
            let e := Core.Expr.mux c over fill (.bin c k a2 (.extract c n2 0 w))
            pure ⟨e, none, up (max ha hn)⟩
      else
        match binOp op (signed a.ty) with
        | some k =>
          charge p 1
          let b := sizeOf (Hw.node p t sz (.bin op) [a, n])
          let mut links : List (Link b) := []
          let mut cur : { x : Hw // sizeOf x < b } := ⟨a, by
            simp only [b, Hw.node.sizeOf_spec, List.cons.sizeOf_spec]; omega⟩
          for _ in [0:sz] do
            match cur with
            | ⟨.node q u _ (.bin o) [l, r], hc⟩ =>
              match binOp o (signed l.ty) with
              | some j =>
                charge q 1
                links := ⟨q, u, j, ⟨r, by
                  simp only [Hw.node.sizeOf_spec, List.cons.sizeOf_spec] at hc; omega⟩⟩ :: links
                cur := ⟨l, by simp only [Hw.node.sizeOf_spec, List.cons.sizeOf_spec] at hc; omega⟩
              | none => break
            | _ => break
          let mut lo ← lower target false cur.1
          for l in links do
            let r ← lower target false l.right.1
            let e := binExpr (cpos l.pos) l.op lo.expr r.expr
            lo ← deep l.pos target (width l.ty) false ⟨e, none, up (max lo.height r.height)⟩
          let r ← lower target false n
          pure ⟨binExpr c k lo.expr r.expr, none, up (max lo.height r.height)⟩
        | none => defect s!"no hardware node for `{op.text}`"
    | .mux, [s, a, b] =>
      charge p 1
      let s ← lower target false s
      let a ← lower target false a
      let b ← lower target false b
      pure ⟨.mux c s.expr a.expr b.expr, none, up (max s.height (max a.height b.height))⟩
    | .resize, [a] =>
      let n := width t
      let w := width a.ty
      if n == w then
        let a ← lower target false a
        pure { a with height := up a.height }
      else if n < w then
        charge p 1
        let a ← lower target false a
        pure ⟨.extract c a.expr 0 n, none, up a.height⟩
      else if signed t then
        charge p 3
        let la ← lower target false a
        let (a1, a2, ha) ← twice p target w a.pos la
        let e := Core.Expr.bin c .concat (.replicate c (.extract c a1 (w - 1) 1) (n - w)) a2
        pure ⟨e, none, up ha⟩
      else
        charge p 2
        let a ← lower target false a
        pure ⟨.bin c .concat (.const c (n - w) 0) a.expr, none, up a.height⟩
    | .reinterpret, [a] =>
      let a ← lower target false a
      pure { a with height := up a.height }
    | .share k, [a] =>
      let path ← match (← get).shares[k]? with
        | some path => pure path
        | none =>
          let la ← lower target false a
          let path ← bindTemp p target (width a.ty) a.pos la.expr
          modify fun s => { s with shares := s.shares.insert k path }
          pure path
      pure ⟨← tempRef p path, some (1 + pathUnits path), 1⟩
    | _, _ => defect "a hardware node has the wrong number of operands"
    deep p target (width t) root lo
termination_by h => sizeOf h
decreasing_by
  all_goals first
    | exact Subtype.property (p := fun x => sizeOf x < b) _
    | (simp_all only [Hw.node.sizeOf_spec, List.cons.sizeOf_spec]; omega)

/-! The value of one statement with the target `target`. Its temporaries count from 0. -/
def value (target : Path) (h : Hw) : FM Core.Expr := do
  modify fun s => { s with count := 0 }
  return (← lower target true h).expr

/-!
The source of the element `k` of the type `t` with the leaf field `f`, for the statement at `pos`
(`Agg.child`). Elaboration gives each bound value the type of its sink, so a missing part is a
defect at its leaf. `fs` gives the fields with a leaf of a struct type, for a word part.
-/
def sub (fs : Layout.Fields) (pos : Pos) (a : Option Agg) (f : Field) (k : Nat) (t : Ty) :
    Option Agg :=
  a.bind (Agg.child (fun u => (fs u).map (·.map fun (k, _, v) => (k, v))) pos k f t)

/-!
The hardware value of a leaf of the type `t` with the source `a`. A static leaf is a constant,
and a leaf of a reference refers to its name or to its child output.
-/
def leafHw (pos : Pos) (t : Ty) : Option Agg → FM Hw
  | some (.hw h) => pure h
  | some (.static v) => pure (.mk pos t (.lit v) [])
  | _ => defect s!"a bound value has no leaf of {t.text}"

/-! The reset constant of a leaf of a register with the source `a`. -/
def leafConst (p : Core.Pos) : Option Agg → FM Core.Expr
  | some (.static v) => constOf p v
  | _ => defect "a register value has no constant leaf"

/-! A struct type without its fields in the design. -/
def noFields (_ : β) (t : Ty) : FM β := defect s!"{t.text} has no fields in the design"

/-! The domain ports `d$0clk` and `d$0rst`. -/
def clockName (d : String) : Name := ⟨d, [.role .clk]⟩
def resetName (d : String) : Name := ⟨d, [.role .rst]⟩

/-! A reference to a domain port of the domain `d`. -/
def domainRef (pos : Pos) (n : Name) : FM Core.Expr := do
  charge pos 1
  return .ref (cpos pos) (← nameText pos n)

/-! The connections of the domain of a child with the domain `c` in a parent with `d`. -/
def domainConns (pos : Pos) (c d : Option String) : FM (List (String × Core.Expr)) := do
  match c, d with
  | some c, some d =>
    charge pos 1
    let clk ← nameText pos (clockName c)
    let x ← domainRef pos (clockName d)
    charge pos 1
    let rst ← nameText pos (resetName c)
    let y ← domainRef pos (resetName d)
    return [(clk, x), (rst, y)]
  | none, _ => return []
  | some _, none => defect "a clocked child in a combinational module"

/-!
The core module of one instantiation. `fs` names the fields of each struct type. Each port,
register, and `:=` binding lowers one leaf at a time in packing order, and each leaf charges
before it exists. An empty one lowers to nothing.
-/
def lowerInst (fs : Layout.Fields) (i : Inst) : FM Core.Module := do
  let b := i.body
  let mp := cpos i.pos
  charge i.pos 1
  let name ← nameText i.pos i.iface.name
  modify fun s => { s with temps := #[], shares := {} }
  let mut domain : List Core.Port := []
  if let some d := b.domain then
    charge i.pos 1
    let clk ← nameText i.pos (clockName d)
    charge i.pos 1
    let rst ← nameText i.pos (resetName d)
    domain := [⟨mp, .input, clk, .clock⟩, ⟨mp, .input, rst, .bits 1⟩]
  let mut ports : Array (PortDecl × Array Core.Port) := #[]
  for q in b.ports do
    let dir : Core.PortDir := if q.input then .input else .output
    let leaves ← Layout.foldPort fs q #[] (fun acc l => do
      charge q.pos 1
      let x ← nameText q.pos l.name
      pure (acc.push ⟨cpos q.pos, dir, x, .bits (width l.ty)⟩)) noFields
    ports := ports.push (q, leaves)
  let layout := Layout.arrange domain ports
  let mut body : Array Core.Stmt := #[]
  for r in b.regs do
    let some d := b.domain | defect "a register in a combinational module"
    body ← Layout.foldLeaves fs (sub fs r.pos) (fun body l x => do
      charge r.pos 2
      let y ← pathText r.pos l.path
      let clk ← nameText r.pos (clockName d)
      let sig ← domainRef r.pos (resetName d)
      charge r.pos 1
      let reset : Core.Reset := ⟨.sync, sig, ← leafConst (cpos r.pos) x⟩
      return body.push (.reg (cpos r.pos) y (width l.ty) clk (some reset)))
      noFields r.ty.depth r.path r.ty (some (.static r.init)) body
  for l in b.lets do
    charge l.pos 1
    let x ← pathText l.pos l.path
    body := body.push (.let_ (cpos l.pos) x (width l.value.ty) (← value l.path l.value))
  let mut conns : Array (Array (String × Core.Expr)) := Array.replicate b.children.size #[]
  for bd in b.binds do
    let p := cpos bd.pos
    match bd.sink with
    | .own k t path =>
      body ← Layout.foldLeaves fs (sub fs bd.pos) (fun body l x => do
        charge bd.pos 1
        let y ← pathText bd.pos l.path
        let e ← value l.path (← leafHw bd.pos l.ty x)
        return body.push <| match k with
          | .reg => .next p y e
          | .wire => .let_ p y (width l.ty) e
          | .output => .assign p y e)
        noFields t.depth path t (some bd.value) body
    | .child k inst q t =>
      -- The leaf `l` names the port with its leaf fields. Its target is the instance, then it.
      conns ← Layout.foldLeaves fs (sub fs bd.pos) (fun conns l x => do
        charge bd.pos 1
        let y ← nameText bd.pos l.name
        let target : Path := ⟨inst.outer, l.path.inner ++ .user q.head :: inst.inner⟩
        let e ← value target (← leafHw bd.pos l.ty x)
        return conns.modify k (·.push (y, e)))
        noFields t.depth ⟨q.head, q.rest.reverse⟩ t (some bd.value) conns
  for (c, k) in b.children.zipIdx do
    charge c.pos 1
    let x ← pathText c.pos c.path
    let m ← nameText c.pos c.iface.name
    let ds ← domainConns c.pos c.iface.domain b.domain
    body := body.push (.inst (cpos c.pos) x m (ds ++ (conns.getD k #[]).toList))
  let temps := (← get).temps
  return ⟨mp, name, layout.inputs ++ layout.outputs, (body ++ temps).toList⟩

/-! The value of `act` and the fuel that it uses. -/
def measure (act : FM α) : FM (α × Nat) := do
  let start := (← get).fuel
  let a ← act
  return (a, start - (← get).fuel)

/-! The result of a lowering: the core design and the units of each instantiation. -/
structure Lowered where
  design : Core.Design
  units : Array Nat

/-!
The lowering of the design `d` with the top selection at `pos` and the fuel `fuel`. The result
has the fuel that remains.
-/
def lowerDesign (pos : Pos) (d : Elab.Design) : FM Lowered := do
  let mut items : Array Core.Item := #[]
  let mut units : Array Nat := #[]
  for i in d.insts do
    let (m, u) ← measure (lowerInst d.fields i)
    items := items.push (.module m)
    units := units.push (i.units + u)
  charge pos 1
  let some t := d.insts[d.top]? | defect "the top is not a done instantiation"
  let top ← nameText pos t.iface.name
  return ⟨⟨top, items.toList, cpos pos⟩, units⟩

/-!
The check of pass 6. The result is the typed design with its proof. A core `E008` is `S020`, and
each other core error is a defect.
-/
def checkDesign (d : Core.Design) : Except Failure { t // Core.check d = .ok t } :=
  go (Core.check d) rfl
where
  go : (r : Except Core.Error Core.Typed.Design) → Core.check d = r →
      Except Failure { t // Core.check d = .ok t }
  | .ok t, h => .ok ⟨t, h⟩
  | .error e, _ =>
    if e.code == .E008 then
      let msg := "the lowered design has a combinational cycle"
      .error (.source ⟨.S020, ⟨e.pos.line, e.pos.col⟩, msg⟩)
    else .error (.defect s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}")

/-! Lowers `d` with the fuel `fuel`. The result has the used fuel. -/
def flatten (fuel : Nat) (pos : Pos) (d : Elab.Design) : Except Failure (Lowered × Nat) := do
  let (l, s) ← (lowerDesign pos d).run { fuel }
  return (l, fuel - s.fuel)

end Silicon.Source.Flatten
