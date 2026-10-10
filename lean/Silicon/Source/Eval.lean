import Silicon.Source.Resolve
import Silicon.Source.Names
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
The evaluator of slice 1 with the budgets and the cost model of section 5.4 of the front-end
spec. It reads the resolved AST after the pre-check. It evaluates expressions, the bodies of
`comptime fn` and `fn` items, and top-level constants. A value is static, hardware, or a handle
(section 5.1). `Source.Elab` runs the module statements and the instantiations.

The operators follow v0.1 section 3. These rules settle the open points of slice 1:

- A static `Int` or `Nat` value takes a finite type at a typed use, if it fits (`S012`). The
  typed uses are an annotation, an assignment, an argument, a return, a constant, `T(n)`, and
  an operand of `+%`, `-%`, `*%`, `&`, `|`, `^`, or a comparison with a finite operand.
- A `Nat` is an `int` value. Only an annotation checks that it is not negative. A `let`
  without an annotation gets the type `Int` for an integer.
- Strings are values for messages. Only `==` and `!=` accept them. Types compare the same way.
- Slice 1 has no function values: a function name is only a callee (`S010`).
- `resize` keeps the signedness. `reinterpret` keeps the width.
- A typed-use error is at the node of the typed use: the statement, the call, or the operator.
  A function without `return` at its end is `S010` at the call.
- A port, a resource, or an instance in a function body is `S011`. The parser rejects them
  first, so only a module body has them.
- A static position needs a static value, else `S011` at the node that uses the value. The
  index arguments, the conditions, and the loop bounds are static positions. The arguments at
  a `comptime` parameter, of `static_assert`, of `error`, and of a constructor `T(x)` are too.
  So is the type of `resize` and `reinterpret`.

Hardware values follow v0.1 sections 1 and 3:

- A use that reads a value reads a register, a wire, or an own output by its name. An input of
  a child is never read (`S017`). An instance and a domain are not data (`S010`).
- An operator with a hardware operand makes a hardware node. A static operand becomes a
  constant node: a static integer first takes the finite type of the other operand.
- A static `&&` or `||` that does not decide gives its right operand, also a hardware one.
- A hardware condition makes a mux of both arms. A static arm takes the type of the other arm.
- A shift count is a hardware `UInt`, or a static count that becomes an `Int` constant node.
- A `let`, an assignment, and a hardware argument of a function bind a hardware value to a
  core name of section 7.3. The hardware result of a function gets the role `0ret` in the call
  frame. A static value and a handle alias get no core name.
- The call site `k` of a call frame `<fn>$<k>c` counts the call nodes of the body of the
  enclosing item in position order. A call outside a body has only static values, so it
  never names hardware.

The cost model. Elaboration charges these units, in evaluation order. A charge is known before
its operation runs. When the fuel cannot pay it, the result is `S015` at the node of the charge.

1. One unit before each expression node, each type node, and each statement. A block is a
   statement: the body of a function, each branch of `comptime if`, each loop iteration, and
   a block statement `{ ... }`. Each block charges its one unit once.
2. A literal makes a value: it charges the size of its value.
3. A unary operator charges the size of its operand. A binary operator charges the sum of the
   sizes of its operands. `*`, `/`, `%`, and `*%` charge their product. A left shift charges
   the size of its result. A right shift reads its operand in full, so it charges the size of
   its operand. `&&`, `||`, and a conditional select a value, so they charge no size.
4. A conversion charges the size of its operand plus the size of its result: `resize`,
   `reinterpret`, and a typed use that makes a finite value from an `Int`.
5. `UInt[w]` and `SInt[w]` charge the size of the type that they make.
6. A copy charges the size of the copied value: each argument, each return, and a binding of a
   reference. The arguments of a function, a prelude function, and a constructor `T(x)` are
   copies. Each charges after all arguments of the call run. A binding is a `let`, an
   assignment, or a constant. A reference is a name, or a conditional that selects a
   reference. The copy comes before the typed use.
7. The target of an assignment is a place, not an expression, so it charges nothing.
8. A `comptime for` charges the sum of the sizes of its two bounds for the range. Each
   iteration charges the size of its loop value before it binds it.
9. A hardware operation charges the size of the node that it makes: 1, plus the sizes of its
   operands. A name in a hardware value has the size 1, and a constant node has the size of its
   static value. A read of a handle and a lift of a static operand only refer, so they charge
   nothing.

The nesting depth counts the active calls, the constants in progress, and the top selection.
A call checks it after its arguments, and a constant before it starts. Above the limit, the
result is `S015` at the call or at the use of the constant.

`Eval` is total by the fuel alone. Each recursive function takes a bound, and the first call
gets the fuel as the bound. Each entry function charges one unit before it calls deeper with a
lower bound. Thus the fuel is never above the bound. At the bound 0 the fuel is 0, and the
charge of the entry fails as it does with more bound.
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
  ports : Std.TreeMap Nat Port compare
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

/-! A value of the evaluator: a static value, a hardware value, or a handle (section 5.1). -/
inductive Val where
  | static (v : Value)
  | hw (h : Hw)
  | handle (h : Handle)

/-! A handle has the size 1. -/
def Val.size : Val → Nat
  | .static v => v.size
  | .hw h => h.size
  | .handle _ => 1

def Val.ty? : Val → Option Ty
  | .static v => v.ty?
  | .hw h => some h.ty
  | .handle _ => none

def Val.text : Val → String
  | .static v => v.text
  | .hw h => s!"hardware {h.ty.text}"
  | .handle (.res .reg ..) => "a register"
  | .handle (.res .wire ..) => "a wire"
  | .handle (.res .output ..) => "an output"
  | .handle (.inst ..) => "an instance"
  | .handle (.input ..) => "an input of a child"
  | .handle (.domain _) => "a domain"

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
item whose body runs, its call sites by position, its symbols, and the current frame name the
hardware.
-/
structure Ctx where
  items : Array Resolve.Item
  limit : Nat
  depth : Nat
  ret : Option Ty
  item : Nat
  calls : Array (Std.TreeMap Pos Nat Pos.compare)
  syms : Syms
  frame : Frame

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
The fuel, the table of constants by item index, the locals of the current frame, and the
names of the current instantiation.
-/
structure St where
  fuel : Nat
  consts : Array Entry
  frame : Std.HashMap Nat Slot
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

/-! Runs `act` with an empty frame of locals and the return type `ret`. -/
def inFrame [Runs m] (ret : Option Ty) (act : m α) : m α := do
  let saved ← monadLift (do return (← get).frame : M _)
  monadLift (modify fun s => { s with frame := {} } : M Unit)
  let r ← withTheReader Ctx (fun c => { c with ret }) act
  monadLift (modify fun s => { s with frame := saved } : M Unit)
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
  | .bool | .int => true

/-! A typed use of `v` at the type `t`. Only a static integer at a finite type converts. -/
def convert (t : Ty) (v : Value) : Except Fault Step :=
  let same := Except.ok ⟨0, fun _ => .ok v⟩
  let wrong := typeError s!"expected {t.text}, but the value is {v.text}"
  match t, v with
  | .bool, .bool _ | .int, .int _ => same
  | .nat, .int n => if 0 ≤ n then same else .error (.S012, s!"{intText n} is not a Nat")
  | .uint w, .uint u _ | .sint w, .sint u _ => if u == w then same else wrong
  | .uint w, .int n | .sint w, .int n =>
    .ok ⟨(Value.int n).size + widthSize w, fun _ =>
      if fits t n then .ok (finite (t matches .sint _) w (BitVec.ofInt w n))
      else .error (.S012, s!"{intText n} does not fit {t.text}")⟩
  | _, _ => wrong

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

/-! A binary operator other than `&&` and `||`, after its operands and the typed uses. -/
def binary (op : BinOp) (a b : Value) : Except Fault Step :=
  let sum := a.size + b.size
  let product := a.size * b.size
  match op with
  | .add | .sub | .mul | .div | .rem =>
    match a, b with
    | .int x, .int y =>
      .ok ⟨if op == .add || op == .sub then sum else product, fun _ => intArith op x y⟩
    | _, _ => typeError s!"`{op.text}` accepts only Int and Nat, not {a.text} and {b.text}"
  | .addw | .subw | .mulw | .and | .or | .xor =>
    let c := (coreOp op).getD .add
    match a, b, finitePair a b with
    | _, _, some (s, ⟨w, x, y⟩) =>
      .ok ⟨if op == .mulw then product else sum, fun _ => .ok (finiteOp c s w x y)⟩
    | .int x, .int y, _ =>
      let f := match op with | .and => intAnd | .or => intOr | _ => intXor
      if op == .and || op == .or || op == .xor then .ok ⟨sum, fun _ => .ok (.int (f x y))⟩
      else typeError s!"`{op.text}` needs a finite operand"
    | _, _, _ => typeError s!"`{op.text}` needs integers of one type, not {a.text} and {b.text}"
  | .eq | .ne => do
    let r ← equal a b
    .ok ⟨sum, fun u => .ok (.bool (if op == .eq then r u else !r u))⟩
  | .lt | .le | .gt | .ge => do
    let r ← order op a b
    .ok ⟨sum, fun u => .ok (.bool (r u))⟩
  | .shl | .shr => shift op a b
  | .land | .lor => typeError s!"`{op.text}` selects; it has no step"

/-! The operators at which a static integer takes the finite type of the other operand. -/
def unifies : BinOp → Bool
  | .addw | .subw | .mulw | .and | .or | .xor | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def resize (t : Ty) (v : Value) : Except Fault Step :=
  match t, v with
  | .uint w, .uint _ x => .ok ⟨v.size + widthSize w, fun _ => .ok (.uint w (x.setWidth w))⟩
  | .sint w, .sint _ x => .ok ⟨v.size + widthSize w, fun _ => .ok (.sint w (x.signExtend w))⟩
  | _, _ => typeError s!"`resize` needs finite types of one signedness, not {v.text}"

def reinterpret (t : Ty) (v : Value) : Except Fault Step :=
  let flip (s : Bool) (w : Nat) (x : BitVec w) : Except Fault Step :=
    .ok ⟨v.size + widthSize w, fun _ => .ok (finite s w x)⟩
  match t, v with
  | .uint w, .uint u x | .uint w, .sint u x =>
    if h : u = w then flip false w (h ▸ x) else typeError "`reinterpret` keeps the width"
  | .sint w, .uint u x | .sint w, .sint u x =>
    if h : u = w then flip true w (h ▸ x) else typeError "`reinterpret` keeps the width"
  | _, _ => typeError s!"`reinterpret` needs finite types, not {v.text}"

/-! `UInt[w]` or `SInt[w]`. The width is 1 to 65536. The charge is the size of the type. -/
def family (t : PrimType) (args : List Value) : Except Fault Ty := do
  match t, args with
  | .uint, [.int w] | .sint, [.int w] =>
    unless 1 ≤ w && w ≤ 65536 do .error (.S012, s!"the width {intText w} is not 1 to 65536")
    .ok (if t == .uint then .uint w.toNat else .sint w.toNat)
  | .uint, [v] | .sint, [v] => typeError s!"a width is a static Int, not {v.text}"
  | _, _ => .error (.S007, "a type family takes one index argument")

def prim (pos : Pos) (x : String) : PrimType → M Ty
  | .bool => pure .bool
  | .nat => pure .nat
  | .int => pure .int
  | .uint | .sint => fail .S007 pos s!"`{x}` takes 1 argument(s), but it has 0"

/-! A string, a type, and a handle have no `Ty`, so an assignment keeps their form. -/
def sameForm : Val → Val → Bool
  | .static (.str _), .static (.str _) | .static (.type _), .static (.type _) => true
  | .handle (.res k _ t _), .handle (.res k' _ t' _) => k == k' && t == t'
  | _, _ => false

/-! The result of an expression, and whether it is a reference to an existing value. -/
structure Out where
  value : Val
  ref : Bool

/-! The value of `e`. Only `static_assert` and `error` give no value. -/
def need (e : Resolve.Expr) : Option Out → M Out
  | some o => pure o
  | none => fail .S010 e.pos "`static_assert` gives no value"

def apply (pos : Pos) (s : Except Fault Step) : M Value := do
  let s ← lift pos s
  charge pos s.charge
  lift pos (s.run ())

def conform (pos : Pos) (t : Ty) (v : Value) : M Value := apply pos (convert t v)

/-! A binding copies a reference. -/
def copy (pos : Pos) (o : Out) : M Unit := if o.ref then charge pos o.value.size else pure ()

/-! The value of a static position at the node `pos`. Another value there is `S011`. -/
def static (pos : Pos) : Val → M Value
  | .static v => pure v
  | v => fail .S011 pos s!"a static position needs a static value, not {v.text}"

/-!
The data of a value at a use that reads it. A register, a wire, and an own output give a
reference to their name: the implicit read. A child input is never read (`S017`). An instance
and a domain are not data.
-/
def data (pos : Pos) : Val → M Val
  | .handle (.res _ _ ty path) => pure (.hw (.mk pos ty (.ref path) []))
  | .handle (.input ..) => fail .S017 pos "an input of a child is a target; it is never read"
  | .handle h => fail .S010 pos s!"{(Val.handle h).text} is not data"
  | v => pure v

/-! A static condition. -/
def test (pos : Pos) : Val → M Bool
  | .static (.bool b) => pure b
  | .static v => fail .S010 pos s!"a condition is a Bool, not {v.text}"
  | v => fail .S011 pos s!"a static condition needs a static Bool, not {v.text}"

/-! The local of an assignment target and its source name, if it is a `let mut` local. -/
def place : Resolve.Expr → M (Option (Nat × Slot × String))
  | .name _ x (.local id) => do
    match (← get).frame[id]? with
    | some s => return if s.mutable then some (id, s, x) else none
    | _ => return none
  | _ => return none

def int (pos : Pos) : Val → M Int
  | .static (.int n) => pure n
  | .static v => fail .S010 pos s!"a loop bound is a static Int, not {v.text}"
  | v => fail .S011 pos s!"a loop bound is a static Int, not {v.text}"

/-! A static integer next to a finite operand takes the type of that operand. -/
def unify (pos : Pos) (op : BinOp) (a b : Value) : M (Value × Value) := do
  if !unifies op then return (a, b)
  match a, b, a.finiteTy?, b.finiteTy? with
  | .int _, _, _, some t => return (← conform pos t a, b)
  | _, .int _, some t, _ => return (a, ← conform pos t b)
  | _, _, _, _ => return (a, b)

/-! The range of a `comptime for` from `a` to `z`: it charges the sizes of both bounds. -/
def range (pos : Pos) (a z : Int) : M Nat := do
  charge pos ((Value.int a).size + (Value.int z).size)
  return (z - a).toNat

/-! Makes a hardware node. It charges the size of the node, as each value that it makes. -/
def node (pos : Pos) (ty : Ty) (op : Op) (args : List Hw) : M Val := do
  let h := Hw.mk pos ty op args
  charge pos h.size
  return .hw h

/-! A static value at a hardware use. Only a Boolean and a finite value have a hardware type. -/
def lit (pos : Pos) : Value → M Hw
  | .bool b => pure (.mk pos .bool (.lit (.bool b)) [])
  | .uint w x => pure (.mk pos (.uint w) (.lit (.uint w x)) [])
  | .sint w x => pure (.mk pos (.sint w) (.lit (.sint w x)) [])
  | v => fail .S010 pos s!"hardware needs a Bool or a finite value, not {v.text}"

/-! A static operand next to a hardware operand of the type `t`. An integer takes the type `t`. -/
def litAt (pos : Pos) (t : Ty) (v : Value) : M Hw := do
  if v matches .int _ && t.finite then lit pos (← conform pos t v) else lit pos v

/-! Two data operands as hardware. At least one of them is hardware. -/
def hwPair (pos : Pos) : Val → Val → M (Hw × Hw)
  | .hw x, .hw y => pure (x, y)
  | .hw x, .static v => do return (x, ← litAt pos x.ty v)
  | .static v, .hw y => do return (← litAt pos y.ty v, y)
  | a, b => fail .S010 pos s!"expected data operands, not {a.text} and {b.text}"

def hwUnary (pos : Pos) (op : UnOp) (a : Hw) : M Val :=
  match op, a.ty with
  | .not, .bool => node pos .bool (.un op) [a]
  | .inv, t | .neg, t =>
    if t.finite then node pos t (.un op) [a]
    else fail .S010 pos s!"`{op.text}` does not accept {t.text}"
  | _, t => fail .S010 pos s!"`{op.text}` does not accept {t.text}"

/-!
A shift with a hardware operand. A static count becomes an `Int` constant of the node, so the
lowering can use the row "Shift by a static count" of section 7.4.
-/
def hwShift (pos : Pos) (op : BinOp) (a b : Val) : M Val := do
  let count ← match b with
    | .static (.int k) =>
      if k < 0 then fail .S013 pos s!"the shift count {intText k} is negative"
      else pure (Hw.mk pos .int (.lit (.int k)) [])
    | .static (.uint _ x) => pure (Hw.mk pos .int (.lit (.int x.toNat)) [])
    | .hw c =>
      if c.ty matches .uint _ then pure c
      else fail .S010 pos s!"a shift count is UInt or a static Int, not {c.ty.text}"
    | v => fail .S010 pos s!"a shift count is UInt or a static Int, not {v.text}"
  let left ← match a with
    | .hw x => pure x
    | .static v => litAt pos .bool v
    | v => fail .S010 pos s!"`{op.text}` does not accept {v.text}"
  if left.ty.finite then node pos left.ty (.bin op) [left, count]
  else fail .S010 pos s!"`{op.text}` does not accept {left.ty.text}"

/-! A binary operator with at least one hardware operand. Both operands are data. -/
def hwBinary (pos : Pos) (op : BinOp) (a b : Val) : M Val := do
  match op with
  | .shl | .shr => hwShift pos op a b
  | .add | .sub | .mul | .div | .rem =>
    fail .S010 pos s!"`{op.text}` accepts only Int and Nat; hardware has `+%`, `-%`, and `*%`"
  | _ =>
    let (x, y) ← hwPair pos a b
    let t := x.ty
    let bad : M Val := fail .S010 pos s!"`{op.text}` does not accept {t.text} and {y.ty.text}"
    if t != y.ty then bad
    else match op with
      | .eq | .ne => node pos .bool (.bin op) [x, y]
      | .land | .lor => if t == .bool then node pos .bool (.bin op) [x, y] else bad
      | .lt | .le | .gt | .ge => if t.finite then node pos .bool (.bin op) [x, y] else bad
      | _ => if t.finite then node pos t (.bin op) [x, y] else bad

/-!
A hardware `if` with the condition `c`. A static arm takes the type of the other arm. Both arms
have one type.
-/
def mux (pos : Pos) (c : Hw) (a b : Val) : M Val := do
  let (x, y) ← match a, b with
    | .static v, .static w =>
      match v.finiteTy?, w.finiteTy? with
      | some t, _ => do pure (← lit pos v, ← litAt pos t w)
      | _, some t => do pure (← litAt pos t v, ← lit pos w)
      | _, _ => do pure (← lit pos v, ← lit pos w)
    | a, b => hwPair pos a b
  if x.ty == y.ty then node pos x.ty .mux [c, x, y]
  else fail .S010 pos s!"the arms of an `if` have one type, not {x.ty.text} and {y.ty.text}"

def hwConvert (pos : Pos) (f : PrimFn) (t : Ty) (x : Hw) : M Val :=
  let bad : M Val := fail .S010 pos s!"no conversion of {x.ty.text} to {t.text} here"
  match f, t, x.ty with
  | .resize, .uint _, .uint _ | .resize, .sint _, .sint _ => node pos t .resize [x]
  | .reinterpret, .uint w, .uint u | .reinterpret, .uint w, .sint u
  | .reinterpret, .sint w, .uint u | .reinterpret, .sint w, .sint u =>
    if u == w then node pos t .reinterpret [x] else bad
  | _, _, _ => bad

/-! A typed use of `v` at the type `t`. It reads a handle. A hardware value needs the type `t`. -/
def conformVal (pos : Pos) (t : Ty) (v : Val) : M Val := do
  match ← data pos v with
  | .static x => return .static (← conform pos t x)
  | .hw h =>
    if h.ty == t then return .hw h
    else fail .S010 pos s!"expected {t.text}, but the value is {h.ty.text}"
  | v => fail .S010 pos s!"{v.text} is not data"

/-!
The frame of the field pair `u` and `f` inside the current frame, with its path. Two frames
with one path get one number, so their bindings share the versions.
-/
def frameOf (u : String) (sym : Nat) (f : Field) : M (Path × Frame) := do
  let c ← read
  let key := (c.frame.id, sym, f)
  let path := (Path.child c.frame.path u).push f
  let s ← get
  match s.naming.frames[key]? with
  | some id => return (path, ⟨some path, id⟩)
  | none =>
    let id := s.naming.frames.size + 1
    set { s with naming.frames := s.naming.frames.insert key id }
    return (path, ⟨some path, id⟩)

def inFrameOf [Runs m] (fr : Frame) (act : m α) : m α :=
  withTheReader Ctx (fun c => { c with frame := fr }) act

/-! The core name `base` of the tag `key` in the current frame, or a version of it. -/
def version (key : Tag) (base : Path) : M Path := do
  let k := (← read).frame.id
  let v := (← get).naming.versions.getD (k, key) 0
  modify fun s => { s with naming.versions := s.naming.versions.insert (k, key) (v + 1) }
  return if v == 0 then base else base.push (.version v)

/-! The core name of the local `id` with the source name `u` in the current frame. -/
def fresh (id : Nat) (u : String) : M Path := do
  let c ← read
  version (.sym (c.binder id)) (Path.child c.frame.path u)

/-! Binds the hardware value `h` to the core name `path`. The result refers to the name. -/
def bindHw (pos : Pos) (path : Path) (h : Hw) : M Val := do
  modify fun s => { s with naming.lets := s.naming.lets.push ⟨path, h, pos⟩ }
  return .hw (.mk pos h.ty (.ref path) [])

/-! A binding of the local `id` with the source name `u`. Only hardware gets a core name. -/
def named (pos : Pos) (id : Nat) (u : String) : Val → M Val
  | .hw h => do bindHw pos (← fresh id u) h
  | v => pure v

/-!
One iteration of a `comptime for` with the loop value `v`. It charges the size of `v`, then
binds `i` in the loop frame `i$v` and runs `act`.
-/
def iteration [Runs m] (pos : Pos) (i : Binder) (v : Int) (act : m α) : m α := do
  monadLift (charge pos (Value.int v).size : M Unit)
  let (_, fr) ← monadLift (do frameOf i.name.name ((← read).binder i.id) (.int v) : M _)
  inFrameOf fr do
    monadLift (bindLocal i.id ⟨some .int, false, .static (.int v)⟩ : M Unit)
    act

/-!
The evaluator. `eval`, `typeExpr`, `stmt`, and `block` are the entry functions. Each charges
one unit, then calls deeper with the bound `n`. The helpers `name`, `call`, and `index` get
the bound `n` of their caller after its charge. They call only entry functions.
-/
mutual
  def eval (b : Nat) (e : Resolve.Expr) : M (Option Out) :=
    match b with
    | 0 => exhausted e.pos
    | n + 1 => do
      charge e.pos 1
      match e with
      | .num p v => let x : Value := .int v; charge p x.size; return some ⟨.static x, false⟩
      | .bool p v => let x : Value := .bool v; charge p x.size; return some ⟨.static x, false⟩
      | .str p v => let x : Value := .str v; charge p x.size; return some ⟨.static x, false⟩
      | .name p x r => return some (← name n p x r)
      | .unary p op a => do
        match ← data p (← need a (← eval n a)).value with
        | .static a => return some ⟨.static (← apply p (unary op a)), false⟩
        | .hw a => return some ⟨← hwUnary p op a, false⟩
        | v => fail .S010 p s!"`{op.text}` does not accept {v.text}"
      | .binary p .land l r | .binary p .lor l r => do
        let op : BinOp := if e matches .binary _ .lor .. then .lor else .land
        match ← data p (← need l (← eval n l)).value with
        | .static a => do
          let a ← test p (.static a)
          if a == (op == .lor) then return some ⟨.static (.bool a), false⟩
          match ← data p (← need r (← eval n r)).value with
          | .hw h =>
            if h.ty == .bool then return some ⟨.hw h, false⟩
            else fail .S010 p s!"a condition is a Bool, not {h.ty.text}"
          | v => return some ⟨.static (.bool (← test p v)), false⟩
        | a => do
          let b ← data p (← need r (← eval n r)).value
          return some ⟨← hwBinary p op a b, false⟩
      | .binary p op l r => do
        let a ← data p (← need l (← eval n l)).value
        let b ← data p (← need r (← eval n r)).value
        match a, b with
        | .static a, .static b =>
          let (a, b) ← unify p op a b
          return some ⟨.static (← apply p (binary op a b)), false⟩
        | a, b => return some ⟨← hwBinary p op a b, false⟩
      | .cond p c y no => do
        match ← data p (← need c (← eval n c)).value with
        | .hw h =>
          unless h.ty == .bool do fail .S010 p s!"a condition is a Bool, not {h.ty.text}"
          let a ← data p (← need y (← eval n y)).value
          let b ← data p (← need no (← eval n no)).value
          return some ⟨← mux p h a b, false⟩
        | v => if ← test p v then eval n y else eval n no
      | .call p f xs => call n p f xs
      | .index p (.name bp _ (.type k)) xs => do
        charge bp 1
        return some ⟨.static (.type (← index n p k xs)), false⟩
      | .index p .. => fail .S010 p "slice 1 indexes only `UInt` and `SInt`"
      | .field p b f => do
        match (← need b (← eval n b)).value with
        | .handle (.inst id path iface) =>
          match (← read).field f.pos >>= (iface.ports[·]?) with
          | some q =>
            if q.input then return some ⟨.handle (.input id path q), true⟩
            else return some ⟨.hw (.mk p q.ty (.out path q.name) []), true⟩
          | none => fail .S010 p s!"the instance has no port `{f.name}`"
        | v => fail .S010 p s!"{v.text} has no field `{f.name}`"
  termination_by (b, 1)

  def typeExpr (b : Nat) (t : Resolve.TypeExpr) : M Ty :=
    match b with
    | 0 => exhausted t.pos
    | n + 1 => do
      charge t.pos 1
      match t with
      | .name p x k => prim p x k
      | .index p (.name bp _ k) xs => do
        charge bp 1
        index n p k xs
      | .index p .. => fail .S007 p "a complete type takes no more index"
  termination_by (b, 1)

  /-- `UInt[e]` or `SInt[e]` in a type or an expression. The base charged its node. -/
  def index (n : Nat) (p : Pos) (k : PrimType) (xs : List Resolve.Expr) : M Ty := do
    let args ← xs.mapM fun x => do static p (← need x (← eval n x)).value
    let t ← lift p (family k args)
    charge p (Value.type t).size
    return t
  termination_by (n + 1, 0)

  /-- A name. A constant evaluates at its first use, in the table of constants. -/
  def name (n : Nat) (p : Pos) (x : String) : Ref → M Out
    | .local id => do
      match (← get).frame[id]? with
      | some s => return ⟨s.value, true⟩
      | _ => fail .S011 p s!"`{x}` is not a static value"
    | .type k => do return ⟨.static (.type (← prim p x k)), true⟩
    | .fn _ => fail .S010 p s!"`{x}` is a function; slice 1 has no function values"
    | .item i => do
      match (← read).items[i]? with
      | some (.const cp _ ty v) =>
        match (← get).consts[i]? with
        | some (.done c) => return ⟨.static c, true⟩
        | some .inProgress => fail .S019 p s!"the constant `{x}` depends on itself"
        | _ => nested p do
          setConst i .inProgress
          let c ← inFrame none do
            let t ← typeExpr n ty
            let o ← need v (← eval n v)
            copy cp o
            conform cp t (← static cp o.value)
          setConst i (.done c)
          return ⟨.static c, true⟩
      | _ => fail .S010 p s!"`{x}` is a function; slice 1 has no function values"
  termination_by (n + 1, 0)

  /--
  A call of a function item, a prelude function, or a type. A function item runs in the call
  frame `<fn>$<k>c`. A hardware argument and a hardware result get a core name in that frame.
  -/
  def call (n : Nat) (p : Pos) (f : Resolve.Expr) (xs : List Resolve.Expr) : M (Option Out) := do
    let args (xs : List Resolve.Expr) : M (List Val) :=
      xs.mapM fun x => do return (← need x (← eval n x)).value
    match f with
    | .name fp g (.item i) =>
      charge fp 1
      let some (.fn ip c fname ps ret body) := (← read).items[i]?
        | fail .S010 fp s!"`{g}` is not a function"
      let vs ← args xs
      if ps.length != vs.length then
        fail .S007 p s!"`{g}` takes {ps.length} argument(s), but it has {vs.length}"
      let ctx ← read
      -- A call outside a body runs on static values only, so its site never names hardware.
      let site := ((ctx.calls[ctx.item]?).bind (·[p]?)).getD 0
      nested p <| inFrame none do
        let (path, fr) ← frameOf fname.name (ctx.syms.items.getD i 0) (.call site)
        withReader (fun c => { c with item := i, frame := fr }) do
          for (q, v) in ps.zip vs do
            let t ← typeExpr n q.ty
            charge p v.size
            let x ← if c || q.comptime then do pure (.static (← conform p t (← static p v)))
              else conformVal p t v
            bindLocal q.name.id ⟨some t, false, ← named p q.name.id q.name.name.name x⟩
          let rt ← typeExpr n ret
          match ← withReader (fun c => { c with ret := some rt }) (block n ip body) with
          | some (.hw h) =>
            let ret ← version .ret (path.push (.role .ret))
            return some ⟨← bindHw p ret h, false⟩
          | some v => return some ⟨v, false⟩
          | none => fail .S010 p s!"`{fname.name}` ends without `return`"
    | .name fp g (.fn h) =>
      charge fp 1
      let vs ← args xs
      charge p (vs.map Val.size).sum
      match h, vs with
      | .resize, [t, v] | .reinterpret, [t, v] =>
        let t ← match ← static p t with
          | .type t => pure t
          | t => fail .S010 p s!"`{g}` needs a type, not {t.text}"
        match ← data p v with
        | .static v =>
          let s := if h == .resize then resize t v else reinterpret t v
          return some ⟨.static (← apply p s), false⟩
        | .hw x => return some ⟨← hwConvert p h t x, false⟩
        | v => fail .S010 p s!"{v.text} is not data"
      | .staticAssert, [c, m] =>
        match ← static p c, ← static p m with
        | .bool c, .str m =>
          if c then return none else fail .S014 p s!"static assertion failed: {strText m}"
        | c, m => fail .S010 p s!"`{g}` does not accept {[c.text, m.text]}"
      | .error, [m] =>
        match ← static p m with
        | .str m => fail .S014 p s!"error: {strText m}"
        | m => fail .S010 p s!"`{g}` does not accept {m.text}"
      | _, vs => fail .S010 p s!"`{g}` does not accept {vs.map Val.text}"
    | _ =>
      let t ← need f (← eval n f)
      match t.value, xs with
      | .static (.type t), [x] =>
        let a ← need x (← eval n x)
        charge p a.value.size
        return some ⟨.static (← conform p t (← static p a.value)), false⟩
      | .static (.type _), _ => fail .S007 p "a constructor takes 1 argument"
      | v, _ => fail .S010 p s!"{v.text} is not a function"
  termination_by (n + 1, 0)

  /-- A statement. The result is the value of a `return`. -/
  def stmt (b : Nat) (s : Resolve.Stmt) : M (Option Val) :=
    match b with
    | 0 => exhausted (s.pos)
    | n + 1 => do
      charge (s.pos) 1
      match s with
      | .local p m b ty v => do
        let t ← ty.mapM (typeExpr n)
        let o ← need v (← eval n v)
        copy p o
        let x ← match t with
          | some t => conformVal p t o.value
          | none => pure o.value
        let x ← named p b.id b.name.name x
        bindLocal b.id ⟨t <|> x.ty?, m, x⟩
        return none
      | .assign p target v => do
        let some (id, slot, x) := ← place target
          | fail .S010 p "an assignment target is a `let mut` local"
        let o ← need v (← eval n v)
        copy p o
        let y ← match slot.ty with
          | some t => conformVal p t o.value
          | none =>
            if sameForm slot.value o.value then pure o.value
            else fail .S010 p s!"expected {slot.value.text}, but the value is {o.value.text}"
        bindLocal id { slot with value := ← named p id x y }
        return none
      | .ret p v => do
        let some rt := (← read).ret | fail .S006 p "only a function has `return`"
        let some v := v | fail .S010 p s!"`return` needs a value of {rt.text}"
        let o ← need v (← eval n v)
        charge p o.value.size
        return some (← conformVal p rt o.value)
      | .ctIf p c yes no => do
        if ← test p (← need c (← eval n c)).value then block n p yes
        else match no with
          | some ss => block n p ss
          | none => return none
      | .ctFor p i lo hi body => do
        let a ← int p (← need lo (← eval n lo)).value
        let z ← int p (← need hi (← eval n hi)).value
        let count ← range p a z
        -- The charge of the loop value `v` also pays the work of the next value `v + 1`.
        let mut v := a
        for _ in [0:count] do
          if let some r ← iteration p i v (block n p body) then return some r
          v := v + 1
        return none
      | .block _ ss => do
        for s in ss do
          if let some r ← stmt n s then return some r
        return none
      | .expr _ v => do let _ ← eval n v; return none
      | .connect p .. | .reg p .. | .wire p .. | .input p .. | .output p .. | .inst p .. =>
        fail .S011 p "a static evaluation makes no hardware"
  termination_by (b, 1)

  /-- A block at `pos`. It charges as a statement. -/
  def block (b : Nat) (pos : Pos) (ss : List Resolve.Stmt) : M (Option Val) :=
    match b with
    | 0 => exhausted pos
    | n + 1 => do
      charge pos 1
      for s in ss do
        if let some r ← stmt n s then return some r
      return none
  termination_by (b, 1)
end

/-!
The scan of a body holds the names that elaboration looks up. These are the positions of the
call nodes, the binders with their local numbers, and the field names with their positions.
-/
structure Scan where
  calls : List Pos := []
  binders : List (Nat × String) := []
  fields : List (Pos × String) := []

abbrev ScanM := StateM Scan

def scanBinder (b : Binder) : ScanM Unit :=
  modify fun s => { s with binders := (b.id, b.name.name) :: s.binders }

def scanExpr : Resolve.Expr → ScanM Unit
  | .call p f xs => do
    modify fun s => { s with calls := p :: s.calls }
    scanExpr f
    for x in xs do scanExpr x
  | .field _ a f => do
    modify fun s => { s with fields := (f.pos, f.name) :: s.fields }
    scanExpr a
  | .unary _ _ a => scanExpr a
  | .binary _ _ l r => do scanExpr l; scanExpr r
  | .cond _ c y n => do scanExpr c; scanExpr y; scanExpr n
  | .index _ b xs => do
    scanExpr b
    for x in xs do scanExpr x
  | .num .. | .bool .. | .str .. | .name .. => pure ()

def scanType : Resolve.TypeExpr → ScanM Unit
  | .name .. => pure ()
  | .index _ b xs => do
    scanType b
    for x in xs do scanExpr x

mutual
  def scanStmt : Resolve.Stmt → ScanM Unit
    | .local _ _ b ty v => do
      if let some t := ty then scanType t
      scanExpr v
      scanBinder b
    | .assign _ t v | .connect _ t v => do scanExpr t; scanExpr v
    | .reg _ b ty i => do scanType ty; scanExpr i; scanBinder b
    | .wire _ b ty | .input _ b ty | .output _ b ty => do scanType ty; scanBinder b
    | .inst _ b _ _ xs => do
      for x in xs do scanExpr x
      scanBinder b
    | .ret _ v => v.forM scanExpr
    | .ctIf _ c y n => do
      scanExpr c
      scanStmts y
      if let some n := n then scanStmts n
    | .ctFor _ i lo hi b => do scanExpr lo; scanExpr hi; scanBinder i; scanStmts b
    | .block _ b => scanStmts b
    | .expr _ v => scanExpr v

  def scanStmts (ss : List Resolve.Stmt) : ScanM Unit := do
    for s in ss do scanStmt s
end

/-! The scan of an item. Only the call sites of the body count for the call frames. -/
def scanItem (it : Resolve.Item) : Scan :=
  let go : ScanM Unit := match it with
    | .fn _ _ _ ps _ b => do
      scanStmts b
      let calls := (← get).calls
      for q in ps do
        scanBinder q.name
        scanType q.ty
      modify fun s => { s with calls }
    | .module _ _ ps ds b => do
      scanStmts b
      let calls := (← get).calls
      for q in ps do
        scanBinder q.name
        scanType q.ty
      for d in ds do scanBinder d
      modify fun s => { s with calls }
    | .const .. => pure ()
  (go.run {}).2

/-!
The number `k` of each call node in the body of an item: its index among the call nodes of
the body, in position order. Section 7.3 names a call frame with it.
-/
def callSites (sc : Scan) : Std.TreeMap Pos Nat Pos.compare :=
  let sorted : Std.TreeMap Pos Unit Pos.compare := sc.calls.foldl (fun m p => m.insert p ()) {}
  sorted.keys.zipIdx.foldl (fun m (p, k) => m.insert p k) {}

def itemName : Resolve.Item → String
  | .const _ n .. | .fn _ _ n .. | .module _ n .. => n.name

/-!
The symbols of the items. The text table runs once for each elaboration, in time linear in
the source up to a logarithmic factor, before the fuel counts.
-/
def symbols (items : Array Resolve.Item) (scans : Array Scan) : Syms := Id.run do
  let mut table : Std.HashMap String Nat := {}
  let intern := fun (t : Std.HashMap String Nat) (x : String) =>
    match t[x]? with
    | some k => (t, k)
    | none => (t.insert x t.size, t.size)
  let mut names := #[]
  for it in items do
    let (t, k) := intern table (itemName it)
    table := t
    names := names.push k
  let mut binders := #[]
  let mut fields := #[]
  for sc in scans do
    let size := sc.binders.foldl (fun m (id, _) => max m (id + 1)) 0
    let mut arr := Array.replicate size 0
    for (id, x) in sc.binders do
      let (t, k) := intern table x
      table := t
      arr := arr.set! id k
    let mut fm : Std.TreeMap Pos Nat Pos.compare := {}
    for (p, x) in sc.fields do
      let (t, k) := intern table x
      table := t
      fm := fm.insert p k
    binders := binders.push arr
    fields := fields.push fm
  return ⟨binders, fields, names⟩

/-! The context and the state of an elaboration with the budget `budget`. -/
def start (budget : Budget) (items : Array Resolve.Item) : Ctx × St :=
  let scans := items.map scanItem
  (⟨items, budget.depth, 0, none, 0, scans.map callSites, symbols items scans, ⟨none, 0⟩⟩,
   ⟨budget.fuel, Array.replicate items.size .notStarted, {}, {}⟩)

/-! Runs `act` with the budget. The result has the used fuel. -/
def run (budget : Budget) (items : Array Resolve.Item) (act : Nat → M α) :
    Except Error (α × Nat) := do
  let (ctx, st) := start budget items
  let (a, s) ← ((act budget.fuel).run ctx).run st
  return (a, budget.fuel - s.fuel)

/-! The value of a static expression in the file scope, and the used fuel. -/
def evalExpr (budget : Budget) (items : Array Resolve.Item) (e : Resolve.Expr) :
    Except Error (Value × Nat) :=
  run budget items fun n => do static e.pos (← need e (← eval n e)).value

end Silicon.Source.Eval
