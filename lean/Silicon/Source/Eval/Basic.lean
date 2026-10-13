-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Resolve
import Silicon.Source.Names
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
The values, the state, and the scalar operations of the evaluator. `Source.Eval.Container` adds
the static containers, and `Source.Eval` the evaluator with the cost model of its module doc.
-/
namespace Silicon.Source.Eval

open Resolve Names

/-! Position order: the lower line, then the lower column. -/
def Pos.compare (a b : Pos) : Ordering :=
  (Ord.compare a.line b.line).then (Ord.compare a.col b.col)

/-! The budgets of section 5.4 with their normative defaults. -/
structure Budget where
  fuel : Nat := 100000000
  depth : Nat := 1000
  deriving Repr, Inhabited

/-! The state of a constant in the table of constants. -/
inductive Entry where
  | notStarted
  | inProgress
  | done (value : Value)
  deriving Repr, Inhabited

/-!
A struct specialization in the table of specializations (section 5.6): the struct item, its
static arguments as they evaluate, and its state. A done entry holds its struct type and its
field types. A specialization that is not started has no entry.
-/
inductive SpecState where
  | inProgress
  | done (ty : Ty) (fields : List Ty)

structure Spec where
  item : Nat
  args : List Value
  state : SpecState

/-! A node of a hardware value. Section 7.4 lowers each node to core operations. -/
inductive Op where
  | ref (name : Path)
  | out (inst : Path) (port : String)
  | lit (value : Value)
  | un (op : UnOp)
  | bin (op : BinOp)
  | mux
  | resize
  | reinterpret
  deriving Repr, Inhabited

/-!
A hardware value: a typed tree of operations over core names. Each node keeps the position of
the source node that made it, and its recursive size, so a charge reads the size in one step.
-/
inductive Hw where
  | node (pos : Pos) (ty : Ty) (size : Nat) (op : Op) (args : List Hw)
  deriving Repr, Inhabited

def Hw.pos : Hw → Pos | .node p .. => p
def Hw.ty : Hw → Ty | .node _ t .. => t
def Hw.size : Hw → Nat | .node _ _ s .. => s

/-! A name or a child output has the size 1. A constant has the size of its value. -/
def Op.size : Op → Nat
  | .lit v => v.size
  | _ => 1

def Hw.mk (pos : Pos) (ty : Ty) (op : Op) (args : List Hw) : Hw :=
  .node pos ty (op.size + (args.map Hw.size).sum) op args

/-! A port of an instantiation, as its parent sees it. `sym` is the symbol of its name. -/
structure Port where
  name : String
  sym : Nat
  input : Bool
  ty : Ty
  deriving Repr, Inhabited

/-!
The interface of a done instantiation: its emitted name, its ports by the symbol of their
name, its number of inputs, and its domain. A combinational module has no domain.
-/
structure Iface where
  name : Names.Name
  ports : Std.HashMap Nat Port
  inputs : Nat
  domain : Option String

/-! The resources that need one binding with `:=`. -/
inductive Kind where
  | reg | wire | output
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
A handle. Its number indexes the resources or the instances of its instantiation. A child
input holds the number of its instance.
-/
inductive Handle where
  | res (kind : Kind) (id : Nat) (ty : Ty) (path : Path)
  | inst (id : Nat) (path : Path) (iface : Iface)
  | input (inst : Nat) (path : Path) (port : Port)
  | domain (name : String)

/-!
A part of a literal that waits for its type. It is a value, the literal `[]` at `pos`, or an
array or a tuple literal at `pos`. Such a literal has at least one part that waits.
-/
inductive Part where
  | value (v : Value)
  | empty (pos : Pos)
  | array (pos : Pos) (elems : List Part)
  | tuple (pos : Pos) (elems : List Part)

/-! The size of a part: 1 for `[]`, and 1 more than its elements for a literal. -/
mutual
  def Part.size : Part → Nat
    | .value v => v.size
    | .empty _ => 1
    | .array _ ps | .tuple _ ps => 1 + Part.sizeAll ps

  def Part.sizeAll : List Part → Nat
    | [] => 0
    | p :: ps => p.size + Part.sizeAll ps
end

def Part.text : Part → String
  | .value v => v.text
  | .empty _ => "`[]`"
  | .array .. => "an array literal with `[]`"
  | .tuple .. => "a tuple literal with `[]`"

/-!
A value of the evaluator: a static value, a hardware value, or a handle (section 5.1).
`pending` is a literal with `[]` before a typed use gives it its type. `first` is the position
of its first `[]`.
-/
inductive Val where
  | static (v : Value)
  | hw (h : Hw)
  | handle (h : Handle)
  | pending (first : Pos) (part : Part)

/-! A handle has the size 1. A literal that waits has the size of its parts. -/
def Val.size : Val → Nat
  | .static v => v.size
  | .hw h => h.size
  | .handle _ => 1
  | .pending _ p => p.size

def Val.ty? : Val → Option Ty
  | .static v => v.ty?
  | .hw h => some h.ty
  | .handle _ | .pending .. => none

def Val.text : Val → String
  | .static v => v.text
  | .hw h => s!"hardware {h.ty.text}"
  | .handle (.res .reg ..) => "a register"
  | .handle (.res .wire ..) => "a wire"
  | .handle (.res .output ..) => "an output"
  | .handle (.inst ..) => "an instance"
  | .handle (.input ..) => "an input of a child"
  | .handle (.domain _) => "a domain"
  | .pending _ p => s!"{p.text} without a type"

/-! A local. A string, a type, and a handle have no `Ty`, so their `ty` is `none`. -/
structure Slot where
  ty : Option Ty
  mutable : Bool
  value : Val

/-! A frame of section 7.3: its path, and its number in the table of frames. The root is 0. -/
structure Frame where
  path : Option Path
  id : Nat

/-!
The symbols of a file. Each distinct identifier gets one number, so a lookup or a key compares
numbers and not text. `binders` gives the symbol of each local number of each item. `fields`
gives the symbol of each field name by its position in each item. `items` gives the symbol of
each item name.
-/
structure Syms where
  binders : Array (Array Nat)
  fields : Array (Std.TreeMap Pos Nat Pos.compare)
  items : Array Nat

/-!
The items, the depth limit, the current depth, and the return type of the current call. The
item whose body runs, its symbols, and the current frame name the hardware. `binding` holds
the struct items whose parameter types evaluate now. `arm` is the nesting depth at the start of
the innermost hardware arm (section 9.4).
-/
structure Ctx where
  items : Array Resolve.Item
  limit : Nat
  depth : Nat
  ret : Option Ty
  item : Nat
  syms : Syms
  frame : Frame
  binding : List Nat
  arm : Option Nat

/-! The symbol of the local number `id` in the current item. Each binder has one. -/
def Ctx.binder (c : Ctx) (id : Nat) : Nat := ((c.syms.binders[c.item]?).bind (·[id]?)).getD 0

/-! The symbol of the field name at `p` in the current item. -/
def Ctx.field (c : Ctx) (p : Pos) : Option Nat := (c.syms.fields[c.item]?).bind (·[p]?)

/-! The key of a binding in a frame: the symbol of its source name, or the result role. -/
inductive Tag where
  | sym (n : Nat)
  | ret
  deriving DecidableEq, BEq, Hashable

/-! A named hardware binding: its core name, its value, and the position of the binding. -/
structure Let where
  path : Path
  value : Hw
  pos : Pos

/-!
The names of one instantiation. `frames` numbers each frame by its parent and its field pair.
`versions` counts the bindings of each tag in each frame. `lets` holds the named bindings in
evaluation order. Each table grows only with the bindings that run.
-/
structure Naming where
  frames : Std.HashMap (Nat × Nat × Field) Nat := {}
  versions : Std.HashMap (Nat × Tag) Nat := {}
  lets : Array Let := #[]

/-!
The state holds the fuel, the table of constants by item index, and the table of struct
specializations. It also holds the locals of the current frame and the names of the current
instantiation. `holds` counts the waiting results that hold each local of the frame (section
5.4).
-/
structure St where
  fuel : Nat
  consts : Array Entry
  specs : Array Spec
  frame : Std.HashMap Nat Slot
  holds : Std.HashMap Nat Nat
  naming : Naming

abbrev M := ReaderT Ctx (StateT St (Except Error))

/-! An error without a position. The caller adds the position of its node. -/
abbrev Fault := ErrorCode × String

/-! The charge of an operation and the operation itself. The charge comes first. -/
structure Step where
  charge : Nat
  run : Unit → Except Fault Value

/-!
An integer in a message: decimal up to 256 bits, else its bit length. The bit length needs no
decimal conversion, so a message stays small and cheap for any computed integer.
-/
def intText (n : Int) : String :=
  let bits := n.natAbs.log2 + 1
  if bits ≤ 256 then toString n
  else s!"{if n < 0 then "a negative" else "an"} integer of {bits} bits"

/-! A string in a message: at most 64 characters, then a note of the full length. -/
def strText (m : String) : String :=
  if m.length ≤ 64 then m else s!"{(m.take 64).toString}... ({m.length} characters)"

def fail (code : ErrorCode) (pos : Pos) (msg : String) : M α := throw ⟨code, pos, msg⟩

def lift (pos : Pos) : Except Fault α → M α
  | .ok a => pure a
  | .error (c, m) => fail c pos m

def typeError (msg : String) : Except Fault α := .error (.S010, msg)

def charge (pos : Pos) (units : Nat) : M Unit := do
  let s ← get
  if units ≤ s.fuel then set { s with fuel := s.fuel - units }
  else fail .S015 pos s!"the fuel cannot pay {intText units} unit(s); {intText s.fuel} remain"

/-! The charge of an entry function at the bound 0. The fuel is 0 there, so it fails. -/
def exhausted (pos : Pos) : M α := do
  charge pos 1
  fail .S015 pos "the fuel is exhausted"

/-! A monad that runs `M` and changes its context. `Elab` runs its walk in such a monad. -/
class Runs (m : Type → Type) extends Monad m, MonadLiftT M m, MonadReaderOf Ctx m,
  MonadWithReaderOf Ctx m

instance : Runs M := {}

/-! Runs `act` one level deeper, or gives `S015` at `pos` above the limit. -/
def nested [Runs m] (pos : Pos) (act : m α) : m α := do
  let c ← readThe Ctx
  if c.limit ≤ c.depth then
    monadLift (fail .S015 pos s!"the nesting depth goes above {c.limit}" : M Unit)
  withTheReader Ctx (fun c => { c with depth := c.depth + 1 }) act

/-!
A mutation at `pos` of a binding of the current frame of locals (section 9.4). Each call, each
constant, and each struct use nests one level deeper with a new frame. Thus the binding is
older than the innermost hardware arm when that arm started at the current depth: `S016`.
-/
def mutation (pos : Pos) : M Unit := do
  let c ← read
  if c.arm == some c.depth then
    fail .S016 pos "a hardware arm changes a binding from before the arm"

/-!
Runs `act` with an empty frame of locals and the return type `ret`. A waiting result of the
caller holds no local of the new frame.
-/
def inFrame [Runs m] (ret : Option Ty) (act : m α) : m α := do
  let saved ← monadLift (do let s ← get; return (s.frame, s.holds) : M _)
  monadLift (modify fun s => { s with frame := {}, holds := {} } : M Unit)
  let r ← withTheReader Ctx (fun c => { c with ret }) act
  monadLift (modify fun s => { s with frame := saved.1, holds := saved.2 } : M Unit)
  return r

/-!
Local numbers are dense over the whole item, also in branches that do not run. The frame thus
holds only the bindings that run, and each of them pays its charge.
-/
def bindLocal (id : Nat) (slot : Slot) : M Unit :=
  modify fun s => { s with frame := s.frame.insert id slot }

def setConst (i : Nat) (e : Entry) : M Unit :=
  modify fun s => { s with consts := s.consts.set! i e }

/-! The finite value of a signedness and a width. -/
def finite (signed : Bool) (w : Nat) (x : BitVec w) : Value :=
  if signed then .sint w x else .uint w x

/-! Two finite operands of one type: the signedness, the width, and both bit vectors. -/
def finitePair : Value → Value → Option (Bool × (w : Nat) × BitVec w × BitVec w)
  | .uint w x, .uint v y => if h : v = w then some (false, ⟨w, x, h ▸ y⟩) else none
  | .sint w x, .sint v y => if h : v = w then some (true, ⟨w, x, h ▸ y⟩) else none
  | _, _ => none

/-! `&`, `|`, and `^` on `Int` in infinite two's complement. `negSucc x` is `~x`. -/
def intAnd : Int → Int → Int
  | .ofNat p, .ofNat q => .ofNat (p &&& q)
  | .ofNat p, .negSucc x | .negSucc x, .ofNat p => .ofNat (p - (p &&& x))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)

def intOr : Int → Int → Int
  | .ofNat p, .ofNat q => .ofNat (p ||| q)
  | .ofNat p, .negSucc x | .negSucc x, .ofNat p => .negSucc (x - (x &&& p))
  | .negSucc x, .negSucc y => .negSucc (x &&& y)

def intXor : Int → Int → Int
  | .ofNat p, .ofNat q => .ofNat (p ^^^ q)
  | .ofNat p, .negSucc x | .negSucc x, .ofNat p => .negSucc (p ^^^ x)
  | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

/-! `floor (a / 2^k)`. A count above the bit length gives 0 or -1 without a large shift. -/
def intShr (a : Int) (k : Nat) : Int :=
  if a.natAbs.log2 < k then (if a < 0 then -1 else 0) else a >>> k

/-! The size of `a * 2^k`, from the bit length of `a`, before the shift runs. -/
def shlSize (a : Int) (k : Nat) : Nat :=
  if a == 0 then 1 else (a.natAbs.log2 + k) / 64 + 1

/-!
`a * 2^k` without the power `2^k`. The shift makes no value above the result, and a zero
operand makes no value at all. Thus the work stays in the charge `shlSize a k`.
-/
def intShl (a : Int) (k : Nat) : Int :=
  if a == 0 then 0 else a <<< k

theorem intShl_eq (a : Int) (k : Nat) : intShl a k = a * 2 ^ k := by
  unfold intShl
  split
  · simp_all
  · exact Int.shiftLeft_eq a k

/-! A count of a finite shift. The amount `min k w` fits `w` bits, because `w < 2^w`. -/
def amount (w k : Nat) : BitVec w := BitVec.ofNat w (min k w)

/-! The range of a finite type, for the fit rule. -/
def fits (t : Ty) (n : Int) : Bool :=
  match t with
  | .uint w => 0 ≤ n && n < 2 ^ w
  | .sint w => -(2 ^ (w - 1) : Int) ≤ n && n < 2 ^ (w - 1)
  | .nat => 0 ≤ n
  | _ => true

/-!
A typed use of a scalar, `()`, a record, or a function at `t`. Only a static integer at a finite
type converts. A `()` part of a container comes here, because it has no elements. A record needs
its own struct type, because a struct type is nominal. A function needs its exact function type,
also in the `mut` marks, and charges nothing.
-/
def convertLeaf (t : Ty) (v : Value) : Except Fault Step :=
  let same := Except.ok ⟨0, fun _ => .ok v⟩
  let wrong := typeError s!"expected {t.text}, but the value is {v.text}"
  match t, v with
  | .unit, .unit | .bool, .bool _ | .int, .int _ | .type, .type _ | .string, .str _ => same
  | .struct .., .record s _ => if s = t then same else wrong
  | .fn .., .function _ ps r => if Ty.fn ps r = t then same else wrong
  | .nat, .int n => if 0 ≤ n then same else .error (.S012, s!"{intText n} is not a Nat")
  | .uint w, .uint u _ | .sint w, .sint u _ => if u == w then same else wrong
  | .uint w, .int n | .sint w, .int n =>
    .ok ⟨(Value.int n).size + widthSize w, fun _ =>
      if fits t n then .ok (finite (t matches .sint _) w (BitVec.ofInt w n))
      else .error (.S012, s!"{intText n} does not fit {t.text}")⟩
  | _, _ => wrong

/-! The size of a scalar `v` after its typed use at `t`. -/
def leafSize (t : Ty) (v : Value) : Nat :=
  match t with
  | .uint w | .sint w => widthSize w
  | _ => v.size

/-! An operation runs in its step after the charge, so each result is a thunk. -/
def unary (op : UnOp) (a : Value) : Except Fault Step :=
  let step (r : Unit → Value) : Except Fault Step := .ok ⟨a.size, fun u => .ok (r u)⟩
  match op, a with
  | .not, .bool b => step fun _ => .bool !b
  | .inv, .int n => step fun _ => .int (Int.not n)
  | .neg, .int n => step fun _ => .int (-n)
  | .inv, .uint w x => step fun _ => .uint w (~~~x)
  | .inv, .sint w x => step fun _ => .sint w (~~~x)
  | .neg, .uint w x => step fun _ => .uint w (Core.Semantics.evalOp .sub (by decide) 0 x)
  | .neg, .sint w x => step fun _ => .sint w (Core.Semantics.evalOp .sub (by decide) 0 x)
  | _, _ => typeError s!"`{op.text}` does not accept {a.text}"

/-! The ordinary operators on `Int`. They do not wrap. -/
def intArith (op : BinOp) (x y : Int) : Except Fault Value :=
  match op with
  | .add => .ok (.int (x + y))
  | .sub => .ok (.int (x - y))
  | .mul => .ok (.int (x * y))
  | .div => if y == 0 then .error (.S013, "division by zero") else .ok (.int (x.tdiv y))
  | .rem => if y == 0 then .error (.S013, "remainder by zero") else .ok (.int (x.tmod y))
  | _ => typeError s!"`{op.text}` is not an ordinary operator"

/-! The core operation of a wrapping or bitwise operator. -/
def coreOp : BinOp → Option Core.BinOp
  | .addw => some .add | .subw => some .sub | .mulw => some .mul
  | .and => some .and | .or => some .or | .xor => some .xor
  | _ => none

def finiteOp (op : Core.BinOp) (s : Bool) (w : Nat) (x y : BitVec w) : Value :=
  if h : op = .concat then finite s w x else finite s w (Core.Semantics.evalOp op h x y)

/-! The core predicate of an ordering, by signedness. -/
def pred (op : BinOp) (signed : Bool) : Core.Pred :=
  match op, signed with
  | .lt, false => .ult | .le, false => .ule | .gt, false => .ugt | .ge, false => .uge
  | .lt, true => .slt | .le, true => .sle | .gt, true => .sgt | _, true => .sge
  | _, false => .uge

def shift (op : BinOp) (a b : Value) : Except Fault Step := do
  let count : Except Fault Nat := match b with
    | .int k =>
      if k < 0 then .error (.S013, s!"the shift count {intText k} is negative") else .ok k.toNat
    | .uint _ x => .ok x.toNat
    | _ => typeError s!"a shift count is UInt or a static Int, not {b.text}"
  match a with
  | .int x =>
    unless b matches .int _ do typeError "an Int shift needs a static Int count"
    let k ← count
    if op == .shl then .ok ⟨shlSize x k, fun _ => .ok (.int (intShl x k))⟩
    else .ok ⟨a.size, fun _ => .ok (.int (intShr x k))⟩
  | .uint w x | .sint w x =>
    let k ← count
    let s := a matches .sint ..
    let c : Core.BinOp := if op == .shl then .shl else if s then .shrs else .shru
    .ok ⟨widthSize w, fun _ => .ok (finiteOp c s w x (amount w k))⟩
  | _ => typeError s!"`{op.text}` does not accept {a.text}"

/-! The type check of `==`, and the comparison as a thunk for the step after the charge. -/
def equal (a b : Value) : Except Fault (Unit → Bool) :=
  match a, b with
  | .int x, .int y => .ok fun _ => x == y
  | .bool x, .bool y => .ok fun _ => x == y
  | .str x, .str y => .ok fun _ => x == y
  | .type x, .type y => .ok fun _ => x == y
  | _, _ =>
    match finitePair a b with
    | some (_, ⟨_, x, y⟩) => .ok fun _ => x == y
    | none => typeError s!"`==` compares values of one type, not {a.text} and {b.text}"

def order (op : BinOp) (a b : Value) : Except Fault (Unit → Bool) :=
  match a, b with
  | .int x, .int y =>
    .ok fun _ => match op with | .lt => x < y | .le => x ≤ y | .gt => x > y | _ => x ≥ y
  | _, _ =>
    match finitePair a b with
    | some (s, ⟨_, x, y⟩) => .ok fun _ => Core.Semantics.evalPred (pred op s) x y == 1
    | none => typeError s!"`{op.text}` orders integers of one type, not {a.text} and {b.text}"

def apply (pos : Pos) (s : Except Fault Step) : M Value := do
  let s ← lift pos s
  charge pos s.charge
  lift pos (s.run ())

/-!
The data of a value at a use that reads it. A register, a wire, and an own output give a
reference to their name: the implicit read. A child input is never read (`S017`). An instance
and a domain are not data.
-/
def data (pos : Pos) : Val → M Val
  | .pending q _ => fail .S010 q "`[]` needs the type [T; 0] from its context"
  | .handle (.res _ _ ty path) => pure (.hw (.mk pos ty (.ref path) []))
  | .handle (.input ..) => fail .S017 pos "an input of a child is a target; it is never read"
  | .handle h => fail .S010 pos s!"{(Val.handle h).text} is not data"
  | v => pure v

end Silicon.Source.Eval
