import Silicon.Source.Resolve
import Silicon.Source.Value
import Std.Data.HashMap

/-!
The static evaluator of slice 1 with the budgets and the cost model of section 5.4 of the
front-end spec. It reads the resolved AST after the pre-check. It evaluates static expressions,
the bodies of `comptime fn` and `fn` items with static arguments, and top-level constants. The
elaboration of hardware comes with `Source.Elab`.

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
- A statement that makes hardware is `S011`: a static evaluation makes no hardware.

The cost model. Elaboration charges these units, in evaluation order. A charge is known before
its operation runs. When the fuel cannot pay it, the result is `S015` at the node of the charge.

1. One unit before each expression node, each type node, and each statement. A block is a
   statement: the body of a function, each branch of `comptime if`, and each loop iteration.
2. A literal makes a value: it charges the size of its value.
3. A unary operator charges the size of its operand. A binary operator charges the sum of the
   sizes of its operands. `*`, `/`, `%`, and `*%` charge their product. A left shift charges
   the size of its result. A right shift reads its operand in full, so it charges the size of
   its operand. `&&`, `||`, and a conditional select a value, so they charge no size.
4. A conversion charges the size of its operand plus the size of its result: `resize`,
   `reinterpret`, and a typed use that makes a finite value from an `Int`.
5. `UInt[w]` and `SInt[w]` charge the size of the type that they make.
6. A copy charges the size of the copied value: each argument, each return, and a binding of a
   reference. A binding is a `let`, an assignment, or a constant. A reference is a name, or a
   conditional that selects a reference. The copy comes before the typed use.
7. The target of an assignment is a place, not an expression, so it charges nothing.
8. A `comptime for` charges the sum of the sizes of its two bounds for the range. Each
   iteration charges the size of its loop value before it binds it.

The nesting depth counts the active calls, the constants in progress, and the top selection.
A call checks it after its arguments, and a constant before it starts. Above the limit, the
result is `S015` at the call or at the use of the constant.

`Eval` is total by the fuel alone. Each recursive function takes a bound, and the first call
gets the fuel as the bound. Each entry function charges one unit before it calls deeper with a
lower bound. Thus the fuel is never above the bound. At the bound 0 the fuel is 0, and the
charge of the entry fails as it does with more bound.
-/
namespace Silicon.Source.Eval

open Resolve

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

/-! A local. A string or a type has no `Ty`, so its `ty` is `none`. -/
structure Slot where
  ty : Option Ty
  mutable : Bool
  value : Value

/-! The items, the depth limit, the current depth, and the return type of the current call. -/
structure Ctx where
  items : Array Resolve.Item
  limit : Nat
  depth : Nat
  ret : Option Ty

/-! The fuel, the table of constants by item index, and the locals of the current frame. -/
structure St where
  fuel : Nat
  consts : Array Entry
  frame : Std.HashMap Nat Slot

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

/-! Runs `act` one level deeper, or gives `S015` at `pos` above the limit. -/
def nested (pos : Pos) (act : M α) : M α := do
  let c ← read
  if c.limit ≤ c.depth then fail .S015 pos s!"the nesting depth goes above {c.limit}"
  withReader (fun c => { c with depth := c.depth + 1 }) act

/-! Runs `act` with an empty frame and the return type `ret`. -/
def inFrame (ret : Option Ty) (act : M α) : M α := do
  let saved := (← get).frame
  modify fun s => { s with frame := {} }
  let r ← withReader (fun c => { c with ret }) act
  modify fun s => { s with frame := saved }
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

/-! A string and a type have no `Ty`, so an assignment keeps their form. -/
def sameForm : Value → Value → Bool
  | .str _, .str _ | .type _, .type _ => true
  | _, _ => false

/-! The result of an expression, and whether it is a reference to an existing value. -/
structure Out where
  value : Value
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

def test (pos : Pos) (o : Out) : M Bool :=
  match o.value with
  | .bool b => pure b
  | v => fail .S010 pos s!"a condition is a Bool, not {v.text}"

/-! The local of an assignment target, if it is a `let mut` local. -/
def place : Resolve.Expr → M (Option (Nat × Slot))
  | .name _ _ (.local id) => do
    match (← get).frame[id]? with
    | some s => return if s.mutable then some (id, s) else none
    | _ => return none
  | _ => return none

def int (pos : Pos) (o : Out) : M Int :=
  match o.value with
  | .int n => pure n
  | v => fail .S010 pos s!"a loop bound is a static Int, not {v.text}"

/-! A static integer next to a finite operand takes the type of that operand. -/
def unify (pos : Pos) (op : BinOp) (a b : Value) : M (Value × Value) := do
  if !unifies op then return (a, b)
  match a, b, a.finiteTy?, b.finiteTy? with
  | .int _, _, _, some t => return (← conform pos t a, b)
  | _, .int _, some t, _ => return (a, ← conform pos t b)
  | _, _, _, _ => return (a, b)

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
      | .num p v => let x : Value := .int v; charge p x.size; return some ⟨x, false⟩
      | .bool p v => let x : Value := .bool v; charge p x.size; return some ⟨x, false⟩
      | .str p v => let x : Value := .str v; charge p x.size; return some ⟨x, false⟩
      | .name p x r => return some (← name n p x r)
      | .unary p op a => do
        let a ← need a (← eval n a)
        return some ⟨← apply p (unary op a.value), false⟩
      | .binary p .land l r | .binary p .lor l r => do
        let a ← test p (← need l (← eval n l))
        if a == (e matches .binary _ .lor ..) then return some ⟨.bool a, false⟩
        return some ⟨.bool (← test p (← need r (← eval n r))), false⟩
      | .binary p op l r => do
        let a ← need l (← eval n l)
        let b ← need r (← eval n r)
        let (a, b) ← unify p op a.value b.value
        return some ⟨← apply p (binary op a b), false⟩
      | .cond p c y no => do
        if ← test p (← need c (← eval n c)) then eval n y else eval n no
      | .call p f xs => call n p f xs
      | .index p (.name bp _ (.type k)) xs => do
        charge bp 1
        return some ⟨.type (← index n p k xs), false⟩
      | .index p .. => fail .S010 p "slice 1 indexes only `UInt` and `SInt`"
      | .field p _ f => fail .S010 p s!"slice 1 has no static value with the field `{f.name}`"
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
    let args ← xs.mapM fun x => do return (← need x (← eval n x)).value
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
    | .type k => do return ⟨.type (← prim p x k), true⟩
    | .fn _ => fail .S010 p s!"`{x}` is a function; slice 1 has no function values"
    | .item i => do
      match (← read).items[i]? with
      | some (.const cp _ ty v) =>
        match (← get).consts[i]? with
        | some (.done c) => return ⟨c, true⟩
        | some .inProgress => fail .S019 p s!"the constant `{x}` depends on itself"
        | _ => nested p do
          setConst i .inProgress
          let c ← inFrame none do
            let t ← typeExpr n ty
            let o ← need v (← eval n v)
            copy cp o
            conform cp t o.value
          setConst i (.done c)
          return ⟨c, true⟩
      | _ => fail .S010 p s!"`{x}` is a function; slice 1 has no function values"
  termination_by (n + 1, 0)

  /-- A call of a function item, a prelude function, or a type. -/
  def call (n : Nat) (p : Pos) (f : Resolve.Expr) (xs : List Resolve.Expr) : M (Option Out) := do
    let args (xs : List Resolve.Expr) : M (List Value) :=
      xs.mapM fun x => do return (← need x (← eval n x)).value
    match f with
    | .name fp g (.item i) =>
      charge fp 1
      let some (.fn ip _ fname ps ret body) := (← read).items[i]?
        | fail .S010 fp s!"`{g}` is not a function"
      let vs ← args xs
      if ps.length != vs.length then
        fail .S007 p s!"`{g}` takes {ps.length} argument(s), but it has {vs.length}"
      nested p <| inFrame none do
        for (q, v) in ps.zip vs do
          let t ← typeExpr n q.ty
          charge p v.size
          bindLocal q.name.id ⟨some t, false, ← conform p t v⟩
        let rt ← typeExpr n ret
        match ← withReader (fun c => { c with ret := some rt }) (block n ip body) with
        | some v => return some ⟨v, false⟩
        | none => fail .S010 p s!"`{fname.name}` ends without `return`"
    | .name fp g (.fn h) =>
      charge fp 1
      match h, ← args xs with
      | .resize, [.type t, v] => return some ⟨← apply p (resize t v), false⟩
      | .reinterpret, [.type t, v] => return some ⟨← apply p (reinterpret t v), false⟩
      | .staticAssert, [.bool c, .str m] =>
        if c then return none else fail .S014 p s!"static assertion failed: {strText m}"
      | .error, [.str m] => fail .S014 p s!"error: {strText m}"
      | _, vs => fail .S010 p s!"`{g}` does not accept {vs.map Value.text}"
    | _ =>
      let t ← need f (← eval n f)
      match t.value, xs with
      | .type t, [x] =>
        let a ← need x (← eval n x)
        return some ⟨← conform p t a.value, false⟩
      | .type _, _ => fail .S007 p "a constructor takes 1 argument"
      | v, _ => fail .S010 p s!"{v.text} is not a function"
  termination_by (n + 1, 0)

  /-- A statement. The result is the value of a `return`. -/
  def stmt (b : Nat) (s : Resolve.Stmt) : M (Option Value) :=
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
          | some t => conform p t o.value
          | none => pure o.value
        bindLocal b.id ⟨t <|> x.ty?, m, x⟩
        return none
      | .assign p target v => do
        let some (id, slot) := ← place target
          | fail .S010 p "an assignment target is a `let mut` local"
        let o ← need v (← eval n v)
        copy p o
        let x ← match slot.ty with
          | some t => conform p t o.value
          | none =>
            if sameForm slot.value o.value then pure o.value
            else fail .S010 p s!"expected {slot.value.text}, but the value is {o.value.text}"
        bindLocal id { slot with value := x }
        return none
      | .ret p v => do
        let some rt := (← read).ret | fail .S006 p "only a function has `return`"
        let some v := v | fail .S010 p s!"`return` needs a value of {rt.text}"
        let o ← need v (← eval n v)
        charge p o.value.size
        return some (← conform p rt o.value)
      | .ctIf p c yes no => do
        if ← test p (← need c (← eval n c)) then block n p yes
        else match no with
          | some ss => block n p ss
          | none => return none
      | .ctFor p i lo hi body => do
        let a ← int p (← need lo (← eval n lo))
        let z ← int p (← need hi (← eval n hi))
        charge p ((Value.int a).size + (Value.int z).size)
        -- The charge of the loop value `v` also pays the work of the next value `v + 1`.
        let mut v := a
        for _ in [0:(z - a).toNat] do
          charge p (Value.int v).size
          bindLocal i.id ⟨some .int, false, .int v⟩
          if let some r ← block n p body then return some r
          v := v + 1
        return none
      | .block p ss => block n p ss
      | .expr _ v => do let _ ← eval n v; return none
      | .connect p .. | .reg p .. | .wire p .. | .input p .. | .output p .. | .inst p .. =>
        fail .S011 p "a static evaluation makes no hardware"
  termination_by (b, 1)

  /-- A block at `pos`. It charges as a statement. -/
  def block (b : Nat) (pos : Pos) (ss : List Resolve.Stmt) : M (Option Value) :=
    match b with
    | 0 => exhausted pos
    | n + 1 => do
      charge pos 1
      for s in ss do
        if let some r ← stmt n s then return some r
      return none
  termination_by (b, 1)
end

/-! Runs `act` with the budget. The result has the used fuel. -/
def run (budget : Budget) (items : Array Resolve.Item) (act : Nat → M α) :
    Except Error (α × Nat) := do
  let ctx : Ctx := ⟨items, budget.depth, 0, none⟩
  let st : St := ⟨budget.fuel, Array.replicate items.size .notStarted, {}⟩
  let (a, s) ← ((act budget.fuel).run ctx).run st
  return (a, budget.fuel - s.fuel)

/-! The value of a static expression in the file scope, and the used fuel. -/
def evalExpr (budget : Budget) (items : Array Resolve.Item) (e : Resolve.Expr) :
    Except Error (Value × Nat) :=
  run budget items fun n => do return (← need e (← eval n e)).value

/-!
The static part of the top selection at `pos`: the module parameters `ps` with the literals
`xs`. It charges the size of the arguments as an `instance` statement. Then it binds each
parameter in the top instantiation. The result is the used fuel.
-/
def top (budget : Budget) (items : Array Resolve.Item) (pos : Pos) (ps : List Resolve.Param)
    (xs : List Resolve.Expr) : Except Error Nat := do
  let ((), used) ← run budget items fun n => do
    let vs ← xs.mapM fun x => do return (← need x (← eval n x)).value
    charge pos (vs.map Value.size).sum
    nested pos <| inFrame none do
      for (q, v) in ps.zip vs do
        let t ← typeExpr n q.ty
        bindLocal q.name.id ⟨some t, false, ← conform pos t v⟩
  return used

end Silicon.Source.Eval
