-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Check
import Silicon.Source.Eval.Container

/-!
The evaluator of slice 1 with the budgets and the cost model of section 5.4 of the front-end
spec. It reads the resolved AST after the pre-check. It evaluates expressions, the bodies of
`comptime fn` and `fn` items, and top-level constants. A value is static, hardware, or a handle
(section 5.1). `Source.Elab` runs the module statements and the instantiations.
`Source.Eval.Container` gives the rules of the static containers of slice 2, and
`Source.Eval.Types` the rules of the types as values.

The operators follow v0.1 section 3. These rules settle the open points of slice 1:

- A static `Int` or `Nat` value takes a finite type at a typed use, if it fits (`S012`). The
  typed uses are an annotation, an assignment, an argument, a return, a constant, `T(n)`, and
  an operand of `+%`, `-%`, `*%`, `&`, `|`, `^`, or a comparison with a finite operand.
- A `Nat` is an `int` value. Only an annotation checks that it is not negative. A `let`
  without an annotation gets the type `Int` for an integer.
- A string is a static sequence of Unicode scalars. `+` joins two strings and charges the sum
  of their sizes. `==` and `!=` compare two strings, and no ordering takes them. Types compare
  the same way.
- `s[i]` and `len(s)` scan the string, so they charge its size (section 5.4). `str(n)` charges
  the copy of `n`, the square of the size of `n`, and then the size of its result.
- `List[T]` charges its size after its depth check. `list(T)` charges the copy of `T`, checks
  the depth of the empty list, and charges 1 for it.
- `push(xs, x)` and `pop(xs)` change the place `xs` directly, with no copy of the list. The
  place resolves first, by the steps of an assignment target, and then `x` evaluates. The place
  must hold a list (`S010`). `pop` of an empty list is `S013`. Then each checks the mutation
  rule (`S016`). `push` then makes the typed use of `x` at the element type, and a hardware
  element is `S011`. It checks the new depth of the root from the element and the number of
  steps of the place (`S015`). Each charges the
  size of the element before the change. `push` gives `()`, and `pop` gives the element.
- The result of an operand waits while the later operands of its node evaluate. The left
  operand of a binary operator other than `&&` and `||` waits, and so does the first arm of a
  hardware `if`. Each argument of a call, of an instance, of a type family, and of a struct use
  waits. Each element of a literal, the base of an index, and the lower bound of a `comptime
  for` wait too. A waiting result that refers to a static value in a local holds the local
  (`hold`). A mutation of a held local charges the size of the local before the change
  (`held`). The charge is the last step before the change, and it comes once for each mutation.
  The mutations are an assignment, `push`, `pop`, and a write-back.
- A hardware arm starts at the current nesting depth. A `push` or a `pop` on a binding of that
  depth changes a binding from before the arm: `S016`. A call nests deeper with a new frame,
  so a function that the arm calls can change its own bindings.
- An element of a list, also through an assignment to `xs[i]`, is never hardware (`S011`).
- A receiver call `x.m(a)` is the call of `m` with `x` at the first parameter without a written
  `comptime` mark (section 5.6). Its name `m` charges 1, as the callee name of a call does. `x`
  evaluates first, then the arguments. The copies then charge in the order of the parameters.
- A `mut` actual resolves its place by the steps of an assignment target, in the evaluation
  order of the arguments. Its copy charges with the other copies, in the order of the
  parameters. The place has exactly the type of the formal, else `S010` at the call. In a
  `comptime fn`, its value is static (`S011`). The formal is a mutable local of the callee.
- The write-backs of a call run after its result, in the order of the parameters. Each checks
  the mutation rule (`S016`). A static value then checks the new depth of the root from the
  value and the number of steps of the place (`S015`). Each then charges the size of the final
  value of the formal. Then it writes the value into the live root, by the steps that the place
  got before the call. A hardware value thus gives the caller root its next version.
- A function name that is not a callee gives a function value (section 5.1). A generic
  function or a builtin is `S010` at the name, after the charge of its node. The signature then
  evaluates in the scope of the function, and the function type checks its depth and charges its
  size at the name (`fnTy`).
- `==` and `!=` with an operand whose type holds a function type are `S010` at the operator.
  The check reads the function flag of the type after both operands, before each join and each
  charge.
- A constructor call of a function type is `S010` at the call, before its arguments, because
  a constructor needs a hardware data type.
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
- `Source.Resolve` gives each call node its call site `k`: its number in the pre-order of the
  body of the enclosing item. The call frame is `<fn>$<k>c`. A call outside a body has only
  static values, so it never names hardware.

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
5. `UInt[w]` and `SInt[w]` charge the size of the type that they make. The other type
   constructors, the joins, and the struct specializations charge by `Source.Eval.Types`.
   `data_bits(T)` charges its node and the size of the width that it copies. The metadata of
   `T` holds the width, so the size of `T` does not count.
6. A copy charges the size of the copied value: each argument, each return, and a binding of a
   reference. The arguments of a function, a prelude function other than `len`, and a
   constructor `T(x)` are copies. `len` only refers to its argument, so it copies nothing.
   Each copy charges after all arguments of the call run. A binding is a `let`, an
   assignment, or a constant. A reference is a name, or a conditional that selects a
   reference. The copy comes before the typed use.
7. The target of an assignment is a place, not an expression, so its root name charges
   nothing. Each step of the place, an index or a selector `.N`, charges 1 before it applies,
   so the charge pays for the walk over the path. The index expressions evaluate and charge.
8. A `comptime for` charges the sum of the sizes of its two bounds for the range. Each
   iteration charges the size of its loop value before it binds it.
9. A hardware operation makes one node and charges 1 plus the number of its operands. Its
   operand trees are shared, not copied. A hardware `&&`, `||`, and `if` are hardware
   operations. A read of a handle and a lift of a static operand only refer, so they charge
   nothing.

The nesting depth counts the active calls, the constants in progress, the struct uses, and the
top selection. A struct use counts while it binds its parameters and while its specialization
is in progress. A call and a struct use check it after their arguments, and a constant before
it starts. Above the limit, the result is `S015` at the call or at the use of the constant or
the struct.

`Eval` is total by the fuel alone. Each recursive function takes a bound, and the first call
gets the fuel as the bound. Each entry function charges one unit before it calls deeper with a
lower bound. Thus the fuel is never above the bound. At the bound 0 the fuel is 0, and the
charge of the entry fails as it does with more bound.
-/
namespace Silicon.Source.Eval

open Resolve Names

/-! A binary operator other than `&&` and `||`, after its operands and the typed uses. -/
def binary (op : BinOp) (a b : Value) : Except Fault Step :=
  let sum := a.size + b.size
  let product := a.size * b.size
  match op with
  | .add | .sub | .mul | .div | .rem =>
    match a, b with
    | .int x, .int y =>
      .ok ⟨if op == .add || op == .sub then sum else product, fun _ => intArith op x y⟩
    | .str x, .str y =>
      if op == .add then .ok ⟨sum, fun _ => .ok (.str (x ++ y))⟩
      else typeError s!"`{op.text}` does not accept strings; `+` joins them"
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

/-!
`==` and `!=` at `pos` take no operand whose type holds a function type (section 5.1), else
`S010`. The check reads the function flag of the type, before each join and each charge.
-/
def comparable (pos : Pos) (op : BinOp) (a b : Val) : M Unit := do
  let funcs (v : Val) : Bool := (v.ty?.map (·.info.funcs)).getD false
  if (op == .eq || op == .ne) && (funcs a || funcs b) then
    fail .S010 pos s!"`{op.text}` takes no function, here {a.text} and {b.text}"

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

/-!
`UInt[w]`, `SInt[w]`, or `List[T]`. The width is 1 to 65536. The charge is the size of the type.
-/
def family (t : PrimType) (args : List Value) : Except Fault Ty := do
  match t, args with
  | .list, [.type e] => .ok (.list e)
  | .list, [v] => typeError s!"the element of a list is a type, not {v.text}"
  | .uint, [.int w] | .sint, [.int w] =>
    unless 1 ≤ w && w ≤ 65536 do .error (.S012, s!"the width {intText w} is not 1 to 65536")
    .ok (if t == .uint then .uint w.toNat else .sint w.toNat)
  | .uint, [v] | .sint, [v] => typeError s!"a width is a static Int, not {v.text}"
  | _, _ => .error (.S007, "a type family takes one index argument")

def prim (pos : Pos) (x : String) : PrimType → M Ty
  | .bool => pure .bool
  | .nat => pure .nat
  | .int => pure .int
  | .uint | .sint | .list => fail .S007 pos s!"`{x}` takes 1 argument(s), but it has 0"
  | .unit => pure .unit
  | .type => pure .type
  | .string => pure .string

/-! A string and a handle have no `Ty`, so an assignment keeps their form. -/
def sameForm : Val → Val → Bool
  | .static (.str _), .static (.str _) => true
  | .handle (.res k _ t _), .handle (.res k' _ t' _) => k == k' && t == t'
  | _, _ => false

/-!
The result of an expression, and whether it is a reference to an existing value. `root` is the
local that the result refers to, if any. The result is then a name of the local, or a part of
the local that a step selects.
-/
structure Out where
  value : Val
  ref : Bool
  root : Option Nat

/-! The value of `e`. Only `static_assert` and `error` give no value. -/
def need (e : Resolve.Expr) : Option Out → M Out
  | some o => pure o
  | none => fail .S010 e.pos "`static_assert` gives no value"

/-! A binding copies a reference. -/
def copy (pos : Pos) (o : Out) : M Unit := if o.ref then charge pos o.value.size else pure ()

/-!
The result `o` of an operand waits while a later operand of its node evaluates (section 5.4).
A static value in a local holds the local: `hold` counts the wait, and `release` ends it.
-/
def waits (o : Out) (f : Nat → Nat) : M Unit :=
  match o.root, o.value with
  | some id, .static _ =>
    modify fun s => { s with holds := s.holds.insert id (f (s.holds.getD id 0)) }
  | _, _ => pure ()

def hold (o : Out) : M Unit := waits o (· + 1)

def release (o : Out) : M Unit := waits o (· - 1)

/-!
A mutation at `p` of the local `id` that a waiting result holds charges the size of the local
before the change (section 5.4). Thus a later copy of the waiting results is paid.
-/
def held (p : Pos) (id : Nat) : M Unit := do
  let s ← get
  if s.holds.getD id 0 != 0 then
    if let some sl := s.frame[id]? then charge p sl.value.size

/-! The value of a static position at the node `pos`. Another value there is `S011`. -/
def static (pos : Pos) : Val → M Value
  | .static v => pure v
  | .pending q _ => fail .S010 q "`[]` needs the type [T; 0] from its context"
  | v => fail .S011 pos s!"a static position needs a static value, not {v.text}"

/-! A static condition. -/
def test (pos : Pos) : Val → M Bool
  | .static (.bool b) => pure b
  | .static v => fail .S010 pos s!"a condition is a Bool, not {v.text}"
  | .pending q _ => fail .S010 q "`[]` needs the type [T; 0] from its context"
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
  | .pending q _ => fail .S010 q "`[]` needs the type [T; 0] from its context"
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

/-!
Makes a hardware node. It charges 1 plus the number of its operands. The operand trees are
shared, so the work is constant per node.
-/
def node (pos : Pos) (ty : Ty) (op : Op) (args : List Hw) : M Val := do
  charge pos (1 + args.length)
  return .hw (Hw.mk pos ty op args)

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
have one type. Two function arms are a static pair: they charge as a static equality, and one
function item gives the static value. Two different functions are `S011` at `pos`.
-/
def mux (pos : Pos) (c : Hw) (a b : Val) : M Val := do
  if let (.static v@(.function i ..), .static w@(.function j ..)) := (a, b) then
    charge pos (v.size + w.size)
    if i == j then return .static v
    else fail .S011 pos "the arms of a hardware `if` are two different functions"
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

/-! `[]` outside a typed use has no type: `S010` at the `[]`. -/
def known : Val → M Unit
  | .pending q _ => fail .S010 q "`[]` needs the type [T; 0] from its context"
  | _ => pure ()

/-! A typed use of `v` at the type `t`. It reads a handle. A hardware value needs the type `t`. -/
def conformVal (pos : Pos) (t : Ty) (v : Val) : M Val := do
  match ← data pos (← settle pos t v) with
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
A place after its steps (section 5.2). It holds the local number, the slot, and the source name
of its root. It also holds the selected part with its type, and the number of each step.
`inList` tells if the last step selects an element of a list.
-/
structure Place where
  id : Nat
  slot : Slot
  name : String
  ty : Option Ty
  part : Val
  keys : List Nat
  inList : Bool

/-!
Applies `f` at `p` to the selected part of the place `pl` in the live value of its root. The
indices of the place and the other operands ran after the root was read, so the change reads the
live slot. A held root first charges its size.
-/
def changeAt (p : Pos) (pl : Place) (f : Value → Value) : M Unit := do
  held p pl.id
  if let some s@{ value := .static r, .. } := (← get).frame[pl.id]? then
    bindLocal pl.id { s with value := .static (update f r pl.keys) }

/-!
Writes `y` into the place `pl` (section 5.2). A place without a step binds its root again, so a
hardware value gets the next version of the root. A place with a step checks the new depth of
the root: the number of steps plus the depth of the value (`S015` at `p`). Then it writes into
the live value of the root.
A container holds no hardware value: `S011` at `q` in a list, else `S010`. `q` is the node of
the value.
-/
def store (p q : Pos) (pl : Place) (y : Val) : M Unit := do
  if pl.keys.isEmpty then
    let v ← named p pl.id pl.name y
    held p pl.id
    bindLocal pl.id { pl.slot with value := v }
  else
    if pl.inList && y matches .hw _ then fail .S011 q "a list holds no hardware value"
    let w ← item q y
    -- The root is within the nesting depth, so only the value on the path can raise it.
    bounded p (pl.keys.length + w.depth)
    changeAt p pl fun _ => w

/-!
The callee of a call after its one evaluation. The name of a function item or of a prelude
function selects it without a value. Each other callee evaluates to a value.
-/
inductive Callee where
  | item (name : String) (i : Nat) (pos : Pos) (comptime : Bool) (u : Ident)
      (params : List Resolve.Param) (ret : Resolve.TypeExpr) (body : List Resolve.Stmt)
  | prim (name : String) (h : PrimFn)
  | value (o : Out)

/-! An actual of a function item: a value, or the place of a `mut` actual. -/
inductive Actual where
  | value (v : Val)
  | place (pl : Place)

/-!
The arguments `xs` in the order of the parameters. A receiver call evaluates its receiver first
and binds it at the parameter `b`. A plain call has `b = 0`, so it keeps its order.
-/
def bound (b : Nat) : List α → List α
  | x :: xs => xs.take b ++ x :: xs.drop b
  | [] => []

/-! The parameters `ps` in the evaluation order of their arguments: the inverse of `bound b`. -/
def unbound (b : Nat) (ps : List α) : List α :=
  match ps.drop b with
  | q :: rest => q :: (ps.take b ++ rest)
  | [] => ps

/-!
The final value of each `mut` formal with the place of its actual, in the order of the
parameters. It reads the frame of the callee before the call ends.
-/
def finals (ps : List Resolve.Param) (acts : List Actual) : M (List (Place × Val)) := do
  let s ← get
  return (ps.zip acts).filterMap fun
    | (q, .place pl) => (s.frame[q.name.id]?).map fun (sl : Slot) => (pl, sl.value)
    | (_, .value _) => none

/-!
The write-backs of the call at `p` in the order of the parameters (section 9.1). Each checks the
mutation rule (`S016`), then the depth of the root, then charges the copy of the value, then
writes into the live root.
-/
def writeBack (p : Pos) (outs : List (Place × Val)) : M Unit := do
  for (pl, v) in outs do
    mutation p
    -- Another value has the type of the place, so it keeps the depth of the root.
    if let .static w := v then bounded p (pl.keys.length + w.depth)
    charge p v.size
    store p p pl v

/-!
Binds the actual `a` to the formal `q` of the type `t` in the frame of the callee (section 9.1).
A value charges its copy, then its typed use. It is static in a `comptime fn` and at a `comptime`
parameter. A place charges the copy of its part, and its type is exactly `t`, else `S010` at the
call `p`. It is static in a `comptime fn`. Its formal is a mutable local.
-/
def copyIn (p : Pos) (c : Bool) (q : Resolve.Param) (t : Ty) : Actual → M Unit
  | .value v => do
    charge p v.size
    let x ← if c || q.mode == .comptime then do
        pure (.static (← conform p t (← static p (← settle p t v))))
      else conformVal p t v
    bindLocal q.name.id ⟨some t, false, ← named p q.name.id q.name.name.name x⟩
  | .place pl => do
    charge p pl.part.size
    let pt := pl.ty <|> pl.part.ty?
    unless pt == some t do
      let u := match pt with | some u => u.text | none => pl.part.text
      fail .S010 p s!"a `mut` actual has the type {u}, but its formal has {t.text}"
    let x ← if c then pure (Val.static (← static p pl.part)) else pure pl.part
    bindLocal q.name.id ⟨some t, true, ← named p q.name.id q.name.name.name x⟩

/-!
The result of the body of the function `u` in the call frame `path`. A hardware result gets the
role `0ret` there. A body without `return` at its end is `S010` at the call `p`.
-/
def result (p : Pos) (path : Path) (u : String) : Option Val → M Val
  | some (.hw h) => do bindHw p (← version .ret (path.push (.role .ret))) h
  | some v => pure v
  | none => fail .S010 p s!"`{u}` ends without `return`"

/-!
`push` at `p` of the value `v` at the node `x` onto the list at the place `pl`. `g` is the name
of the callee. The module doc gives the steps. It checks the list and the mutation rule. Then it
makes the typed use of the element, checks the depth, and charges the size of the element.
-/
def pushOnto (p x : Pos) (g : String) (pl : Place) (v : Val) : M (Option Out) := do
  let .static (.list e _) := pl.part | fail .S010 p s!"`{g}` needs a list, not {pl.part.text}"
  mutation p
  let w ← match ← data x (← settle p e v) with
    | .static w => conform p e w
    | .hw _ => fail .S011 x "a list holds no hardware value"
    | v => fail .S010 x s!"{v.text} is not an element of a list"
  -- The root is within the nesting depth, so only the element on the path can raise it.
  bounded p (pl.keys.length + 1 + w.depth)
  charge p w.size
  changeAt p pl (fun | .list t ys => .list t (ys.push w) | v => v)
  return some ⟨.static .unit, false, none⟩

/-!
`pop` at `p` of the list at the place `pl`. `g` is the name of the callee. An empty list is
`S013`. Then it checks the mutation rule and charges the size of the element.
-/
def popFrom (p : Pos) (g : String) (pl : Place) : M (Option Out) := do
  let .static (.list _ ys) := pl.part | fail .S010 p s!"`{g}` needs a list, not {pl.part.text}"
  let some w := ys.back? | fail .S013 p "`pop` of an empty list"
  mutation p
  charge p w.size
  changeAt p pl (fun | .list t ys => .list t ys.pop | v => v)
  return some ⟨.static w, false, none⟩

/-!
`data_bits` at `p` with the arguments `vs`. It charges the size of the width that it copies from
the metadata of the type. `g` is the name of the callee.
-/
def dataBitsOf (p : Pos) (g : String) : List Val → M (Option Out)
  | [.static (.type t)] => do
    if t.info.data then
      charge p (intSize t.info.width)
      return some ⟨.static (.int t.info.width), false, none⟩
    else fail .S010 p s!"`{g}` needs a hardware data type, not {t.text}"
  | [v] => fail .S010 p s!"`{g}` needs a type, not {v.text}"
  | vs => fail .S007 p s!"`{g}` takes 1 argument(s), but it has {vs.length}"

/-!
A call at `p` of the prelude function `h` other than `push` and `pop`, with the values `vs` of
its arguments in the order of the parameters. `g` is the name of the callee. `len` only refers
to its argument, and `data_bits` reads the metadata of its type. The others copy each argument.
-/
def primCall (p : Pos) (g : String) (h : PrimFn) (vs : List Val) : M (Option Out) := do
  match h with
  | .len => return some ⟨.static (← lenOf p vs), false, none⟩
  | .dataBits => dataBitsOf p g vs
  | h =>
    charge p (vs.map Val.size).sum
    match h, vs with
    | .resize, [t, v] | .reinterpret, [t, v] =>
      let t ← match ← static p t with
        | .type t => pure t
        | t => fail .S010 p s!"`{g}` needs a type, not {t.text}"
      match ← data p v with
      | .static v =>
        let s := if h == .resize then resize t v else reinterpret t v
        return some ⟨.static (← apply p s), false, none⟩
      | .hw x => return some ⟨← hwConvert p h t x, false, none⟩
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
    | .list, [t] =>
      match ← static p t with
      | .type t =>
        let v := Value.list t #[]
        bounded p v.depth
        charge p 1
        return some ⟨.static v, false, none⟩
      | t => fail .S010 p s!"`{g}` needs a type, not {t.text}"
    | .str, [v] =>
      match ← data p v with
      | .static n@(.int k) =>
        charge p (n.size * n.size)
        let s := Value.str (toString k)
        charge p s.size
        return some ⟨.static s, false, none⟩
      | v => fail .S010 p s!"`{g}` needs an Int, not {v.text}"
    | _, vs => fail .S010 p s!"`{g}` does not accept {vs.map Val.text}"

/-!
The evaluator. `eval`, `typeExpr`, `stmt`, and `block` are the entry functions. Each charges
one unit, then calls deeper with the bound `n`. The helpers `name`, `spec`, `index`, `params`,
`placeAt`, `args`, `ctor`, `invoke`, and `call` get the bound `n` of their caller after its
charge. They call entry functions, `spec`, which a name of a struct item uses, and the helpers
that `call` uses.
-/
mutual
  def eval (b : Nat) (e : Resolve.Expr) : M (Option Out) :=
    match b with
    | 0 => exhausted e.pos
    | n + 1 => do
      charge e.pos 1
      match e with
      | .num p v => let x : Value := .int v; charge p x.size; return some ⟨.static x, false, none⟩
      | .bool p v => let x : Value := .bool v; charge p x.size; return some ⟨.static x, false, none⟩
      | .str p v => let x : Value := .str v; charge p x.size; return some ⟨.static x, false, none⟩
      | .name p x r => return some (← name n p x r)
      | .unary p op a => do
        match ← data p (← need a (← eval n a)).value with
        | .static a => return some ⟨.static (← apply p (unary op a)), false, none⟩
        | .hw a => return some ⟨← hwUnary p op a, false, none⟩
        | v => fail .S010 p s!"`{op.text}` does not accept {v.text}"
      | .binary p .land l r | .binary p .lor l r => do
        let op : BinOp := if e matches .binary _ .lor .. then .lor else .land
        match ← data p (← need l (← eval n l)).value with
        | .static a => do
          let a ← test p (.static a)
          if a == (op == .lor) then return some ⟨.static (.bool a), false, none⟩
          match ← data p (← need r (← eval n r)).value with
          | .hw h =>
            if h.ty == .bool then return some ⟨.hw h, false, none⟩
            else fail .S010 p s!"a condition is a Bool, not {h.ty.text}"
          | v => return some ⟨.static (.bool (← test p v)), false, none⟩
        | a => do
          let b ← data p (← need r (← eval n r)).value
          return some ⟨← hwBinary p op a b, false, none⟩
      | .binary p op l r => do
        let o ← need l (← eval n l)
        let a ← data p o.value
        hold o
        let b ← data p (← need r (← eval n r)).value
        release o
        comparable p op a b
        match a, b with
        | .static a, .static b =>
          if composite a || composite b then
            return some ⟨.static (← containerOp p op a b), false, none⟩
          let (a, b) ← unify p op a b
          return some ⟨.static (← apply p (binary op a b)), false, none⟩
        | a, b => return some ⟨← hwBinary p op a b, false, none⟩
      | .cond p c y no => do
        match ← data p (← need c (← eval n c)).value with
        | .hw h =>
          unless h.ty == .bool do fail .S010 p s!"a condition is a Bool, not {h.ty.text}"
          let (a, b) ← withReader (fun c => { c with arm := some c.depth }) do
            let o ← need y (← eval n y)
            let a ← data p o.value
            hold o
            let b ← data p (← need no (← eval n no)).value
            release o
            return (a, b)
          return some ⟨← mux p h a b, false, none⟩
        | v => if ← test p v then eval n y else eval n no
      | .call p f xs k => call n p f xs 0 k
      | .method p r m f b xs k => do
        let some b := b
          | fail .S007 p s!"`{m.name}` has no parameter without `comptime` for the receiver"
        call n p (.name m.pos m.name f) (r :: xs) b k
      | .index p b xs => do
        if let .name bp _ (.type k) := b then
          charge bp 1
          return some ⟨.static (.type (← index n p k xs)), false, none⟩
        if let .name bp _ (.item i) := b then
          if let some (.struct ..) := (← read).items[i]? then
            charge bp 1
            return some ⟨.static (.type (← spec n p i xs)), false, none⟩
        let [x] := xs | fail .S010 p "an index of a value has one argument"
        let o ← need b (← eval n b)
        let v ← data p o.value
        if v matches .static (.type _) then fail .S007 p "a complete type takes no index"
        hold o
        let i ← static x.pos (← need x (← eval n x)).value
        release o
        if let .static (.str s) := v then
          return some ⟨.static (← strAt p x.pos s i), false, none⟩
        return some ⟨← pick p x.pos v i, true, o.root⟩
      | .field p b f => do
        let o ← need b (← eval n b)
        match o.value with
        | .handle (.inst id path iface) =>
          match (← read).field f.pos >>= (iface.ports[·]?) with
          | some q =>
            if q.input then return some ⟨.handle (.input id path q), true, none⟩
            else return some ⟨.hw (.mk p q.ty (.out path q.name) []), true, none⟩
          | none => fail .S010 p s!"the instance has no port `{f.name}`"
        | v => return some ⟨.static (← fieldAt p f v).2.1, true, o.root⟩
      | .unit p => do charge p Value.unit.size; return some ⟨.static .unit, false, none⟩
      | .tuple p xs => do
        let es ← operands n xs fun x o => element x.pos o.value
        match waiting es with
        | some q => return some ⟨.pending q (.tuple p (es.map (·.1))), false, none⟩
        | none => return some ⟨.static (← tupleOf p (values es)), false, none⟩
      | .array p [] => do charge p 1; return some ⟨.pending p (.empty p), false, none⟩
      | .array p xs => do
        let es ← operands n xs fun x o => element x.pos o.value
        match waiting es with
        | some q => return some ⟨.pending q (.array p (es.map (·.1))), false, none⟩
        | none => return some ⟨.static (← arrayOf p (values es)), false, none⟩
      | .select p b q i => do
        let o ← need b (← eval n b)
        return some ⟨← select p q i (← data p o.value), true, o.root⟩
      | .arrayType p t k => do
        let e ← typeExpr n t
        let t ← arrayTy p k.pos e (← static k.pos (← need k (← eval n k)).value)
        return some ⟨.static (.type t), false, none⟩
      | .fnType p ps r => do
        let qs ← params n ps
        return some ⟨.static (.type (← fnTy p qs (← typeExpr n r))), false, none⟩
  termination_by (b, 3)

  def typeExpr (b : Nat) (t : Resolve.TypeExpr) : M Ty :=
    match b with
    | 0 => exhausted t.pos
    | n + 1 => do
      charge t.pos 1
      match t with
      | .name p x r => do typeOf p x (← name n p x r).value
      | .index p (.name bp _ (.type k)) xs => do
        charge bp 1
        index n p k xs
      | .index p (.name bp _ (.item i)) xs => do
        charge bp 1
        spec n p i xs
      | .index p .. => fail .S007 p "a complete type takes no more index"
      | .unit p => do charge p Ty.unit.size; return .unit
      | .tuple p ts => do tupleTy p (← ts.mapM (typeExpr n))
      | .array p t k => do
        let e ← typeExpr n t
        arrayTy p k.pos e (← static k.pos (← need k (← eval n k)).value)
      | .fn p ps r => do
        let qs ← params n ps
        fnTy p qs (← typeExpr n r)
  termination_by (b, 3)

  /-- The parameter types of a function type in their order, each with its `mut` mark. -/
  def params (n : Nat) (ps : List Resolve.FnParam) : M (List TyParam) :=
    ps.mapM fun | .mk m q => do return TyParam.mk m (← typeExpr n q)
  termination_by (n + 1, 0)

  /-- `UInt[e]` or `SInt[e]` in a type or an expression. The base charged its node. -/
  def index (n : Nat) (p : Pos) (k : PrimType) (xs : List Resolve.Expr) : M Ty := do
    let args ← operands n xs fun _ o => static p o.value
    let t ← lift p (family k args)
    if t matches .list _ then bounded p t.depth
    charge p (Value.type t).size
    return t
  termination_by (n + 1, 0)

  /--
  A use of the struct item `i` at `p` with the arguments `xs`, in the table of specializations.
  Each argument is static. Each use binds the parameters in the scope of the struct, one level
  deeper. A literal with `[]` takes the type of its parameter there, as a module argument does.
  The typed uses give the key of the table. The first use evaluates the field types there. The
  key exists only after the parameter types, so a use of the struct while its parameter types
  evaluate is a cycle (`S019`).
  -/
  def spec (n : Nat) (p : Pos) (i : Nat) (xs : List Resolve.Expr) : M Ty := do
    let some (.struct _ x ps fs) := (← read).items[i]?
      | fail .S007 p "a complete type takes no index"
    let args ← operands n xs fun _ o => do
      match o.value with
      | v@(.pending ..) => pure v
      | v => return .static (← static p v)
    if ps.length != args.length then
      fail .S007 p s!"`{x.name}` takes {ps.length} argument(s), but it has {args.length}"
    if (← read).binding.contains i then
      fail .S019 p s!"the parameter types of `{x.name}` depend on `{x.name}`"
    nested p <| inFrame none <| withReader (fun c => { c with item := i, frame := ⟨none, 0⟩ }) do
      let keys ← withReader (fun c => { c with binding := i :: c.binding }) <|
        (ps.zip args).mapM fun (q, v) => do
          let t ← typeExpr n q.ty
          let w ← conform p t (← static p (← settle p t v))
          bindLocal q.name.id ⟨some t, false, .static w⟩
          return w
      specialize p x.name i keys (fs.mapM fun f => typeExpr n f.ty)
  termination_by (n + 1, 0)

  /--
  A name. A constant and a `type` item evaluate at their first use, in the table of constants.
  A struct item is a use of its specialization without arguments. A function item gives a
  function value. Its signature evaluates in the scope of the function, with no locals. It adds
  no nesting level and no call frame. The name makes the value, so a binding of it is no copy.
  -/
  def name (n : Nat) (p : Pos) (x : String) : Ref → M Out
    | .local id => do
      match (← get).frame[id]? with
      | some s => return ⟨s.value, true, some id⟩
      | _ => fail .S011 p s!"`{x}` is not a static value"
    | .type k => do return ⟨.static (.type (← prim p x k)), true, none⟩
    | .fn _ => fail .S010 p s!"`{x}` is a builtin; a builtin is not a value"
    | .item i => do
      match (← read).items[i]? with
      | some (.const cp _ ty v) => do
        let c ← constant p x i do
          let t ← typeExpr n ty
          let o ← need v (← eval n v)
          copy cp o
          conform cp t (← static cp (← settle cp t o.value))
        return ⟨.static c, true, none⟩
      | some (.alias _ _ ty) => do
        return ⟨.static (← constant p x i do return .type (← typeExpr n ty)), true, none⟩
      | some (.struct ..) => do return ⟨.static (.type (← spec n p i [])), true, none⟩
      | some (.fn _ _ u ps ret _) => do
        if generic ps ret then fail .S010 p s!"`{x}` is generic; a generic function is not a value"
        let (qs, r) ← inFrame none <|
            withReader (fun c => { c with item := i, frame := ⟨none, 0⟩ }) do
          let qs ← params n (ps.map fun q => .mk (q.mode == .mut) q.ty)
          return (qs, ← typeExpr n ret)
        let _ ← fnTy p qs r
        return ⟨.static (.function u.name qs.toArray r), false, none⟩
      | _ => fail .S010 p s!"`{x}` is not a value"
  termination_by (n + 1, 1)

  /--
  The place `target` at `p` (section 5.2). Its root is a `let mut` local, else it is `code` at
  `p`. Each step charges 1 before it applies. Then the index of an index step evaluates and
  checks against the live value of the root.
  -/
  def placeAt (n : Nat) (p : Pos) (code : ErrorCode) (target : Resolve.Expr) : M Place := do
    let some (root, sels) := chain target
      | fail code p "the root of a place is a `let mut` local"
    let some (id, slot, x) := ← place root
      | fail code p "the root of a place is a `let mut` local"
    let mut cur := slot.value
    let mut ty := slot.ty
    let mut keys : Array Nat := #[]
    let mut inList := false
    for sel in sels do
      charge sel.pos 1
      let (k, w, ft) ← match sel with
        | .index q [i] => do
          let (k, w) ← pickAt q i.pos cur (← static i.pos (← need i (← eval n i)).value)
          pure (k, w, none)
        | .index q _ => fail .S010 q "an index of a value has one argument"
        | .select q r i => do
          let (k, w) ← selectAt q r i cur
          pure (k, w, none)
        | .field q f => do
          let (k, w, ft) ← fieldAt q f cur
          pure (k, w, some ft)
      ty := match ft, ty with
        | some t, _ => some t
        | none, some t => partTy t k
        | none, none => w.ty?
      inList := cur matches .static (.list ..)
      cur := .static w
      keys := keys.push k
    return ⟨id, slot, x, ty, cur, keys.toList, inList⟩
  termination_by (n + 1, 0)

  /-- The values of the arguments `xs` in the order of the parameters, by `bound b`. -/
  def args (n b : Nat) (xs : List Resolve.Expr) : M (List Val) := do
    return bound b (← operands n xs fun _ o => pure o.value)
  termination_by (n + 1, 0)

  /--
  The results of `xs` in their order, each after the check `f`. Each result waits while the
  later ones evaluate (`hold`).
  -/
  def operands (n : Nat) (xs : List Resolve.Expr) (f : Resolve.Expr → Out → M α) :
      M (List α) := do
    let os ← xs.mapM fun x => do
      let o ← need x (← eval n x)
      let a ← f x o
      hold o
      return (a, o)
    for (_, o) in os do release o
    return os.map (·.1)
  termination_by (n, 4)

  /-- A constructor call at `p`: the callee result `o` gives a type, and `xs` are its arguments. -/
  def ctor (n : Nat) (p : Pos) (o : Out) (b : Nat) (xs : List Resolve.Expr) :
      M (Option Out) := do
    let .static (.type t) := o.value | fail .S010 p s!"{o.value.text} is not a function"
    if t matches .fn .. then fail .S010 p s!"a constructor needs a hardware data type, not {t.text}"
    match t, xs with
    | t, [] => return some ⟨.static (← zero p t), false, none⟩
    | t@(.struct ..), xs =>
      let some (_, fs) := fieldsIn (← get).specs t
        | fail .S010 p s!"{t.text} has no specialization"
      if fs.length != xs.length then
        fail .S007 p
          s!"a struct constructor takes 0 or {fs.length} argument(s), but it has {xs.length}"
      let vs ← args n b xs
      charge p (vs.map Val.size).sum
      return some ⟨.static (← recordOf p t fs (xs.map (·.pos)) vs), false, none⟩
    | t, [x] =>
      let a ← need x (← eval n x)
      charge p a.value.size
      return some ⟨.static (← conform p t (← static p a.value)), false, none⟩
    | _, _ => fail .S007 p "a constructor takes 0 or 1 argument(s)"
  termination_by (n + 1, 1)

  /--
  The run at `p` of the function item `i` with the actuals `acts`, in the order of the
  parameters `ps`. It runs in the call frame `<fn>$<k>c` of the call site `k`: the copy-in of
  each actual, then the body `body` at `ip` with the return type `ret`. The write-backs of its
  `mut` actuals then run in the frame of the caller. `c` is true for a `comptime fn`.
  -/
  def invoke (n : Nat) (p : Pos) (i k : Nat) (c : Bool) (u : Ident) (ps : List Resolve.Param)
      (ret : Resolve.TypeExpr) (ip : Pos) (body : List Resolve.Stmt) (acts : List Actual) :
      M (Option Out) := do
    let ctx ← read
    let (r, outs) ← nested p <| inFrame none do
      let (path, fr) ← frameOf u.name (ctx.syms.items.getD i 0) (.call k)
      withReader (fun c => { c with item := i, frame := fr }) do
        for (q, a) in ps.zip acts do copyIn p c q (← typeExpr n q.ty) a
        let rt ← typeExpr n ret
        let o ← withReader (fun c => { c with ret := some rt }) (block n ip body)
        return (← result p path u.name o, ← finals ps acts)
    writeBack p outs
    return some ⟨r, false, none⟩
  termination_by (n + 1, 0)

  /--
  A call of a function item, a prelude function, or a type. The callee `f` evaluates once,
  before the arguments, and its result selects the call. The arguments `xs` are in their
  evaluation order, and the first binds at the parameter `b` (`bound`). A function item runs in
  the call frame of the call site `k` (`invoke`). A `mut` actual resolves its place in the
  evaluation order of the arguments.
  -/
  def call (n : Nat) (p : Pos) (f : Resolve.Expr) (xs : List Resolve.Expr) (b k : Nat) :
      M (Option Out) := do
    let callee ← match f with
      | .name fp g (.item i) => do
        match (← read).items[i]? with
        | some (.fn ip c u ps ret body) => do
          charge fp 1
          pure (Callee.item g i ip c u ps ret body)
        | _ => pure (Callee.value (← need f (← eval n f)))
      | .name fp g (.fn h) => do
        charge fp 1
        pure (Callee.prim g h)
      | _ => pure (Callee.value (← need f (← eval n f)))
    match callee with
    | .item g i ip c u ps ret body =>
      if ps.length != xs.length then
        let _ ← args n b xs
        fail .S007 p s!"`{g}` takes {ps.length} argument(s), but it has {xs.length}"
      let acts ← (xs.zip (unbound b ps)).mapM fun (x, q) => do
        if q.mode == .mut then return (Actual.place (← placeAt n x.pos .S008 x), none)
        else
          let o ← need x (← eval n x)
          hold o
          return (Actual.value o.value, some o)
      for (_, o) in acts do if let some o := o then release o
      invoke n p i k c u ps ret ip body (bound b (acts.map (·.1)))
    | .prim g .push =>
      let [l, x] := xs | fail .S007 p s!"`{g}` takes 2 argument(s), but it has {xs.length}"
      let pl ← placeAt n l.pos .S008 l
      let o ← need x (← eval n x)
      pushOnto p x.pos g pl o.value
    | .prim g .pop =>
      let [l] := xs | fail .S007 p s!"`{g}` takes 1 argument(s), but it has {xs.length}"
      popFrom p g (← placeAt n l.pos .S008 l)
    | .prim g h => primCall p g h (← args n b xs)
    | .value o => ctor n p o b xs
  termination_by (n + 1, 2)

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
          | none => do known o.value; pure o.value
        let x ← named p b.id b.name.name x
        bindLocal b.id ⟨t <|> x.ty?, m, x⟩
        return none
      | .assign p target v => do
        let pl ← placeAt n p .S010 target
        let o ← need v (← eval n v)
        copy p o
        let y ← match pl.ty with
          | some t => conformVal p t o.value
          | none =>
            if sameForm pl.part o.value then pure o.value
            else fail .S010 p s!"expected {pl.part.text}, but the value is {o.value.text}"
        store p v.pos pl y
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
        let o ← need lo (← eval n lo)
        let a ← int p o.value
        hold o
        let z ← int p (← need hi (← eval n hi)).value
        release o
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
      | .expr _ v => do
        if let some o ← eval n v then known o.value
        return none
      | .connect p .. | .reg p .. | .wire p .. | .input p .. | .output p .. | .inst p .. =>
        fail .S011 p "a static evaluation makes no hardware"
      | .alias _ x ty => do
        bindLocal x.id ⟨some .type, false, .static (.type (← typeExpr n ty))⟩
        return none
  termination_by (b, 3)

  /-- A block at `pos`. It charges as a statement. -/
  def block (b : Nat) (pos : Pos) (ss : List Resolve.Stmt) : M (Option Val) :=
    match b with
    | 0 => exhausted pos
    | n + 1 => do
      charge pos 1
      for s in ss do
        if let some r ← stmt n s then return some r
      return none
  termination_by (b, 3)
end

/-!
The scan of an item holds the names that elaboration looks up. These are the binders with their
local numbers, and the field names with their positions.
-/
structure Scan where
  binders : List (Nat × String) := []
  fields : List (Pos × String) := []

abbrev ScanM := StateM Scan

def scanBinder (b : Binder) : ScanM Unit :=
  modify fun s => { s with binders := (b.id, b.name.name) :: s.binders }

mutual
  def scanExpr : Resolve.Expr → ScanM Unit
    | .call _ f xs _ => do
      scanExpr f
      for x in xs do scanExpr x
    | .method _ r _ _ _ xs _ => do
      scanExpr r
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
    | .select _ a .. => scanExpr a
    | .tuple _ xs | .array _ xs => for x in xs do scanExpr x
    | .arrayType _ t n => do scanType t; scanExpr n
    | .fnType _ ps r => do
      for q in ps do scanParam q
      scanType r
    | .num .. | .bool .. | .str .. | .name .. | .unit _ => pure ()

  def scanType : Resolve.TypeExpr → ScanM Unit
    | .name .. | .unit _ => pure ()
    | .index _ b xs => do
      scanType b
      for x in xs do scanExpr x
    | .tuple _ ts => for t in ts do scanType t
    | .array _ t n => do scanType t; scanExpr n
    | .fn _ ps r => do
      for q in ps do scanParam q
      scanType r

  def scanParam : Resolve.FnParam → ScanM Unit
    | .mk _ t => scanType t
end

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
    | .alias _ b ty => do scanType ty; scanBinder b

  def scanStmts (ss : List Resolve.Stmt) : ScanM Unit := do
    for s in ss do scanStmt s
end

/-! The scan of an item. The parameters of a struct bind in its specializations. -/
def scanItem (it : Resolve.Item) : Scan :=
  let go : ScanM Unit := match it with
    | .fn _ _ _ ps _ b => do
      scanStmts b
      for q in ps do
        scanBinder q.name
        scanType q.ty
    | .module _ _ ps ds b => do
      scanStmts b
      for q in ps do
        scanBinder q.name
        scanType q.ty
      for d in ds do scanBinder d
    | .struct _ _ ps fs => do
      for q in ps do
        scanBinder q.name
        scanType q.ty
      for f in fs do scanType f.ty
    | .const .. | .alias .. => pure ()
  (go.run {}).2

def itemName : Resolve.Item → String
  | .const _ n .. | .fn _ _ n .. | .module _ n .. | .struct _ n .. | .alias _ n .. => n.name

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
  (⟨items, budget.depth, 0, none, 0, symbols items scans, ⟨none, 0⟩, [], none⟩,
   ⟨budget.fuel, Array.replicate items.size .notStarted, #[], {}, {}, {}⟩)

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
