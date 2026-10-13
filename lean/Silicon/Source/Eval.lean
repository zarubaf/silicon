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
- An element of a list, also through an assignment to `xs[i]` or to a part of it, holds no
  hardware leaf (`S011`). A module argument and the element of `push` hold none either.
- A literal, a record constructor, and an assignment to a part can make a hardware aggregate.
  An assignment that gives a static root a hardware leaf binds the root as a rebind does.
- A receiver call `x.m(a)` is the call of `m` with `x` at the first parameter without a written
  `comptime` mark (section 5.6). Its name `m` charges 1, as the callee name of a call does. `x`
  evaluates first, then the arguments. The copies then charge in the order of the parameters.
- A `mut` actual resolves its place by the steps of an assignment target, in the evaluation
  order of the arguments. Its copy charges with the other copies, in the order of the
  parameters. The place has exactly the type of the formal, else `S010` at the call. In a
  `comptime fn`, its value is static (`S011`). The formal is a mutable local of the callee.
- `S008` at run time (section 9.1). Each frame has a counter of the open windows of each root,
  with no charge. The place of an assignment, of a `mut` actual, of `push`, and of `pop` opens
  a window of its root after the root resolves, before its steps. A root that is pending
  already is `S008` at the `mut` actual or the assignment. The window of an assignment closes
  after its right side, and the window of a `mut` actual after the last argument of its call.
  Pass 4 rejects each conflict that the syntax shows, so only a call through a function value
  gives this error.
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
- Another callee than the name of a function item or of a prelude function evaluates once,
  before the arguments. Its result waits while they evaluate. A type gives a constructor
  call. A function value checks the number of its arguments first (`S007` at the call). Then
  the marks of its type select the `mut` actuals, and it runs as a call of its item, found by
  its index. Its callee charges as an expression, and no function name charges. A `comptime fn`
  thus runs in the static mode, and a hardware argument is `S011`. Another value is `S010`.
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
  Arms of a container type join with the join charge. Then the walk of section 7.4 makes one
  `mux` for each leaf pair. Two scalar arms such as `3` and `3` are a static pair too. Equal
  sides of a static pair give the value. The first difference is `S011` at the `if` (F19). A
  walk with two or more `mux` nodes marks the condition once with `Op.share`. A core name and a
  constant get no mark, and the mark has no charge (`mux`).
- A shift count is a hardware `UInt`, or a static count that becomes an `Int` constant node.
- A `let`, an assignment, and a hardware argument of a function bind a hardware value to a
  core name of section 7.3. The hardware result of a function gets the role `0ret` in the call
  frame, with no version. A static value and a handle alias get no core name.
- A binding of a hardware aggregate takes one version, and each hardware leaf gets one core
  `let` at the name with its leaf fields. A reference expands into its leaves there, after the
  copy paid for them. An argument, a result, and a `mut` write-back bind the same way.
- `==` and `!=` with a hardware aggregate operand check the function flag, then join the two
  types with the join charge (`S010` without a join). Then the walk of section 7.4 visits the
  pairs in packing order, and it charges 1 before each pair, the root pair included. A
  reference pairs part by part through its type, so it never expands. A static pair charges as a
  static equality. A leaf pair keeps the scalar rule of slice 1 with its conversion charge. After
  the walk, the chain of `and` nodes charges from `(const 1 s)` when static pairs exist, and `!=`
  adds an `xor` node last (`aggEq`).
- A place update whose new root has a hardware leaf binds each hardware leaf of the root again,
  at the next version of the root. It charges the size of the new root from the stored sizes,
  before the path copies and before a reference on the path expands. The held root then
  charges, and the change and the core `let` statements follow (section 5.4).
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
   reference. The copy comes before the typed use. The copy of a handle that reads an aggregate
   also charges the size of the read reference: the zero size of its type.
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
  | .handle (.res k _ t _), .handle (.res k' _ t' _) => k == k' && t.same t'
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

/-!
The result of the part `r` that a step selects from `o`. `v` is the data of `o`. The part
refers to `o`. A reference gives a part without a hardware leaf as a new static value
(section 5.4). Thus a binding of it is not a copy.
-/
def part (o : Out) (v r : Val) : Out :=
  if v matches .agg (.ref ..) && r matches .static _ then ⟨r, false, none⟩ else ⟨r, true, o.root⟩

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

/-!
Opens at `p` a window of the root `id` of the current frame (section 9.1). A root that is
pending already is `S008` at `p`. The counters have no charge. `shut` closes the window.
-/
def pend (p : Pos) (x : String) (id : Nat) : M Unit := do
  let k := (← get).pending.getD id 0
  if k > 0 then fail .S008 p s!"the root `{x}` is pending in a window"
  modify fun s => { s with pending := s.pending.insert id (k + 1) }

def shut (id : Nat) : M Unit :=
  modify fun s => { s with pending := s.pending.insert id (s.pending.getD id 0 - 1) }

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
def hwNode (pos : Pos) (ty : Ty) (op : Op) (args : List Hw) : M Hw := do
  charge pos (1 + args.length)
  return Hw.mk pos ty op args

def node (pos : Pos) (ty : Ty) (op : Op) (args : List Hw) : M Val := do
  return .hw (← hwNode pos ty op args)

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
    if !t.same y.ty then bad
    else match op with
      | .eq | .ne => node pos .bool (.bin op) [x, y]
      | .land | .lor => if t == .bool then node pos .bool (.bin op) [x, y] else bad
      | .lt | .le | .gt | .ge => if t.finite then node pos .bool (.bin op) [x, y] else bad
      | _ => if t.finite then node pos t (.bin op) [x, y] else bad

/-!
The pairs of a hardware equality (section 7.4). `statics` tells if a static pair exists, and
`equal` tells if all static pairs are equal. `nodes` holds the `icmp eq` node of each hardware
pair in walk order.
-/
structure Pairs where
  statics : Bool := false
  equal : Bool := true
  nodes : Array Hw := #[]

/-!
The part `k` of the part `a` of an equality walk. `f` is its leaf field and `t` its type. An
element of a node or of a static container keeps its form. A part of a reference is a reference
to the part, or a hardware leaf of a scalar type. Thus the walk never expands a reference.
-/
def Agg.child (pos : Pos) (k : Nat) (f : Field) (t : Ty) : Agg → Option Agg
  | .array _ xs | .tuple _ xs | .record _ xs => xs[k]?
  | .static (.array _ xs) | .static (.tuple xs) | .static (.record _ xs) => xs[k]?.map .static
  | .ref b _ =>
    if t matches .bool | .uint _ | .sint _ then some (.hw (.mk pos t (b.sub f).op []))
    else some (.ref (b.sub f) t)
  | _ => none

/-!
A static pair of a hardware equality at `pos`. It charges as a static equality, the sum of the
two sizes, and its result goes into `s` (section 7.4). The two types joined before the walk, so
the charge comes before the comparison reads the values.
-/
def staticPair (pos : Pos) (x y : Value) (acc : Pairs) : M Pairs := do
  charge pos (x.size + y.size)
  let r ← lift pos (Id.run ((same x y).run.run' 0))
  let e ← lift pos (r ())
  return { acc with statics := true, equal := acc.equal && e }

/-!
A leaf pair of a hardware equality at `pos`. Two static leaves are a static pair. Another pair
keeps the scalar rule of slice 1. A static leaf converts to the type of its pair with its
conversion charge. Then the `icmp eq` node charges.
-/
def leafPair (pos : Pos) (a b : Agg) (acc : Pairs) : M Pairs := do
  match a, b with
  | .static x, .static y => staticPair pos x y acc
  | a, b =>
    let (x, y) ← hwPair pos a.val b.val
    unless x.ty.same y.ty do
      fail .S010 pos s!"`==` does not accept {x.ty.text} and {y.ty.text}"
    return { acc with nodes := acc.nodes.push (← hwNode pos .bool (.bin .eq) [x, y]) }

/-!
The walk of a hardware equality at `pos` over the parts `a` and `b` of the joined type `t`, by
the rules of section 7.4 in order. It charges 1 before it visits each pair. A container descends
into its pairs in packing order, also a container that is not hardware data. `()` adds nothing.
A part that is not hardware data is a static pair, and a data scalar is a leaf pair. `fs` gives
the named fields of a struct type. The depth `d` of `t` bounds the walk.
-/
def eqWalk (fs : Ty → Option (Array (String × Ty))) (pos : Pos) :
    Nat → Ty → Agg → Agg → Pairs → M Pairs
  | 0, t, _, _, _ => fail .S010 pos s!"{t.text} is deeper than its depth"
  | d + 1, t, a, b, acc => do
    charge pos 1
    let pair (k : Nat) (f : Field) (u : Ty) (acc : Pairs) : M Pairs :=
      match a.child pos k f u, b.child pos k f u with
      | some x, some y => eqWalk fs pos d u x y acc
      | _, _ => fail .S010 pos s!"`==` needs a common type, not {a.val.text} and {b.val.text}"
    match t with
    | .array e n => do
      let mut acc := acc
      for k in [0:n] do acc ← pair k (.elem k) e acc
      return acc
    | .tuple ts => do
      let mut acc := acc
      for (u, k) in ts.toList.zipIdx do acc ← pair k (.elem k) u acc
      return acc
    | .struct .. => do
      let some nfs := fs t | fail .S010 pos s!"{t.text} has no specialization"
      let mut acc := acc
      for ((x, u), k) in nfs.toList.zipIdx do acc ← pair k (.user x) u acc
      return acc
    | .unit => return acc
    | .bool | .uint _ | .sint _ => leafPair pos a b acc
    | _ =>
      match a, b with
      | .static x, .static y => staticPair pos x y acc
      | _, _ => fail .S010 pos s!"`==` needs a common type, not {a.val.text} and {b.val.text}"

/-!
`==` or `!=` at `pos` with a hardware aggregate operand (section 5.4). The function flag checked
before. The two types join with the join charge (`S010` without a join). Then the walk visits
the pairs. After the walk, the chain of `and` nodes charges in chain order from `E_0`, which is
`(const 1 s)` when static pairs exist. `!=` adds an `xor` node last. A walk without a hardware
pair gives a static `Bool`.
-/
def aggEq (pos : Pos) (op : BinOp) (a b : Val) : M Val := do
  let bad : M Val := fail .S010 pos s!"`{op.text}` needs a common type, not {a.text} and {b.text}"
  let (some s, some t, some x, some y) := (a.ty?, b.ty?, a.agg?, b.agg?) | bad
  let some j ← walked pos (joinTy s t : Walk (Option Ty)) | bad
  let r ← eqWalk (fieldsNamed (← read).items (← get).specs) pos j.depth j x y {}
  match r.nodes.toList with
  | [] => return .static (.bool (if op == .eq then r.equal else !r.equal))
  | n :: ns =>
    let (e₀, rest) ← if r.statics then do pure (← lit pos (.bool r.equal), n :: ns)
      else pure (n, ns)
    let mut e := e₀
    for z in rest do e ← hwNode pos .bool (.bin .and) [e, z]
    if op == .eq then return .hw e
    else node pos .bool (.bin .xor) [e, ← lit pos (.bool true)]

/-!
A static pair of a hardware `if` at `pos` (section 7.4) with the joined type `t`. It charges as a
static equality, the sum of the two sizes. Identical sides give the value, so a function compares
by its item. Other sides compare by the static equality of `==`, which converts a static integer
to the joined type. Equal sides give the side of the joined type. Different sides are `S011` at
the `if`, because a static part cannot depend on the hardware condition.
-/
def ifStatic (pos : Pos) (t : Ty) (x y : Value) : M Value := do
  charge pos (x.size + y.size)
  let differ : M Value :=
    fail .S011 pos s!"the arms of a hardware `if` differ in a static part: {x.text} and {y.text}"
  if x.cmp y == .eq then return x
  if x matches .function .. then return ← differ
  let r ← lift pos (Id.run ((same x y).run.run' 0))
  if ← lift pos (r ()) then return if x.ty?.any (·.same t) then x else y
  differ

/-!
A leaf pair of a hardware `if` at `pos` with the condition `c` and the joined type `t`. A static
leaf converts to `t`, also when both leaves are static. Then the `mux` node charges 1 plus 3.
-/
def ifLeaf (pos : Pos) (c : Hw) (t : Ty) (a b : Agg) : M Hw := do
  let (x, y) ← match a, b with
    | .static v, .static w => do pure (← litAt pos t v, ← litAt pos t w)
    | a, b => hwPair pos a.val b.val
  if x.ty.same y.ty then hwNode pos x.ty .mux [c, x, y]
  else fail .S010 pos s!"the arms of an `if` have one type, not {x.ty.text} and {y.ty.text}"

/-!
A pair of the type `t` that is not an array, a tuple, or a record. The rules 2 to 4 of the walk
apply: `()` gives `()`, a data scalar is a leaf pair, and each other part is a static pair.
-/
def ifPart (pos : Pos) (c : Hw) (t : Ty) (a b : Agg) : M Agg :=
  match t with
  | .unit => return .static .unit
  | .bool | .uint _ | .sint _ => return .hw (← ifLeaf pos c t a b)
  | _ =>
    match a, b with
    | .static x, .static y => return .static (← ifStatic pos t x y)
    | _, _ =>
      fail .S010 pos s!"the arms of an `if` have one type, not {a.val.text} and {b.val.text}"

/-!
The walk of a hardware `if` at `pos` over the arms `a` and `b` of the joined type `t`, by the
rules of section 7.4 in order. It charges 1 before it visits each pair. A container descends
into its pairs in packing order, also a container that is not hardware data. Then it rebuilds
the node in its normal form. `fs` gives the named fields of a struct type. The depth `d` of `t`
bounds the walk.
-/
def ifWalk (fs : Ty → Option (Array (String × Ty))) (pos : Pos) (c : Hw) :
    Nat → Ty → Agg → Agg → M Agg
  | 0, t, _, _ => fail .S010 pos s!"{t.text} is deeper than its depth"
  | d + 1, t, a, b => do
    charge pos 1
    let pair (k : Nat) (f : Field) (u : Ty) : M Agg :=
      match a.child pos k f u, b.child pos k f u with
      | some x, some y => ifWalk fs pos c d u x y
      | _, _ =>
        fail .S010 pos s!"the arms of an `if` have one type, not {a.val.text} and {b.val.text}"
    match t with
    | .array e n => do
      let mut xs := #[]
      for k in [0:n] do xs := xs.push (← pair k (.elem k) e)
      return .mkArray e xs
    | .tuple ts => do
      let mut xs := #[]
      for (u, k) in ts.toList.zipIdx do xs := xs.push (← pair k (.elem k) u)
      return .mkTuple ts xs
    | .struct .. => do
      let some nfs := fs t | fail .S010 pos s!"{t.text} has no specialization"
      let mut xs := #[]
      for ((x, u), k) in nfs.toList.zipIdx do xs := xs.push (← pair k (.user x) u)
      return .mkRecord t xs
    | t => ifPart pos c t a b

/-!
The condition `c` of an `if` whose walk makes `n` `mux` nodes. With two or more nodes, the leaf
statements share `c`, so it gets one mark with the next number of the instantiation. A core
name, a child output, and a constant get no mark. The mark has no charge.
-/
def shared (c : Hw) (n : Nat) : M Hw := do
  let .node _ _ _ op _ := c
  if n < 2 || op matches .ref _ | .out .. | .lit _ then return c
  let k := (← get).naming.shares
  modify fun s => { s with naming := { s.naming with shares := k + 1 } }
  return Hw.mk c.pos c.ty (.share k) [c]

/-!
A hardware `if` at `pos` with the condition `c` (section 5.4). Arms of a scalar type keep the
rule of slice 1. They need a common type (`S010`), with no join charge and no walk unit. Then
the rules 2 to 4 of the walk apply to the one pair (F19). Arms of a container type join
with the join charge (`S010` without a join). An array, a tuple, or a record root then walks.
The type metadata gives the number of `mux` nodes of the walk, its leaf count, so the mark of
`c` comes before the walk.
-/
def mux (pos : Pos) (c : Hw) (a b : Val) : M Val := do
  let bad : M Val := fail .S010 pos s!"the arms of an `if` have one type, not {a.text} and {b.text}"
  let (some s, some t, some x, some y) := (a.ty?, b.ty?, a.agg?, b.agg?) | bad
  let some j ← if containerTy s || containerTy t then walked pos (joinTy s t : Walk (Option Ty))
    else pure (scalarJoin s t) | bad
  match j with
  | .array .. | .tuple _ | .struct .. =>
    let c ← shared c j.info.leaves
    let fs := fieldsNamed (← read).items (← get).specs
    return (← ifWalk fs pos c j.depth j x y).val
  | j => return (← ifPart pos c j x y).val

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

/-!
A typed use of `v` at the type `t`. It reads a handle. A hardware value needs the type `t`, and
a hardware aggregate converts part by part (`typedAgg`).
-/
def conformVal (pos : Pos) (t : Ty) (v : Val) : M Val := do
  match ← data pos (← settle pos t v) with
  | .static x => return .static (← conform pos t x)
  | .hw h =>
    if h.ty.same t then return .hw h
    else fail .S010 pos s!"expected {t.text}, but the value is {h.ty.text}"
  | .agg a => return .agg (← typedAgg pos t a)
  | v => fail .S010 pos s!"{v.text} is not data"

/-!
The copy of `v` when `copies`, then its typed use at `t` at `pos`. The copy charges the size of
`v`, and a handle has the size 1 as in slice 1. A typed use then reads a handle. A read of an
aggregate gives a reference, and its binding expands the reference into its leaves. Thus the
copy also charges the size of the reference, the zero size of its type, before the typed use.
-/
def copyUse (pos : Pos) (t : Ty) (copies : Bool) (v : Val) : M Val := do
  if copies then charge pos v.size
  let d ← data pos (← settle pos t v)
  if copies && v matches .handle _ && d matches .agg _ then charge pos d.size
  conformVal pos t d

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

/-!
Binds the hardware aggregate `a` to the core name `path` (section 7.3). Each hardware leaf gets
one core `let`, and a reference expands into its leaves. The copy of the value paid for each
leaf before. The result refers to the names.
-/
def bindAgg (pos : Pos) (path : Path) (a : Agg) : M Agg := do
  let fs := fieldsNamed (← read).items (← get).specs
  let (r, lets) ← lift pos ((Agg.bindAt fs pos path a).run #[])
  modify fun s => { s with naming.lets := s.naming.lets ++ lets }
  return r

/-!
A binding of the local `id` with the source name `u`. Only a value with a hardware leaf gets a
core name. An aggregate takes one version, and each of its hardware leaves gets a core `let`.
-/
def named (pos : Pos) (id : Nat) (u : String) : Val → M Val
  | .hw h => do bindHw pos (← fresh id u) h
  | .agg a => do return .agg (← bindAgg pos (← fresh id u) a)
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
`inList` tells if a step selects an element of a list.
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
The aggregate `a` with the part at the numbers `ks` replaced by `y` (`Agg.set`). A reference on
the path expands one level. The caller paid for the expansion.
-/
def setAt (pos : Pos) (a y : Agg) (ks : List Nat) : M Agg := do
  let specs := (← get).specs
  match Agg.set (Agg.expand (fieldsNamed (← read).items specs) specs pos) y a ks with
  | some r => return r
  | none => fail .S010 pos "the place has no part for its value"

/-!
Applies `f` at `p` to the selected static part of the place `pl` in the live value of its root.
The indices of the place and the other operands ran after the root was read, so the change reads
the live slot. In an aggregate root, the change refreshes each container node on the path, so it
first charges the part count of each one (`Agg.pathWidth`). Then a held root charges its size.
The hardware leaves of an aggregate root keep their names, so the root takes no new version.
-/
def changeAt (p : Pos) (pl : Place) (f : Value → Value) : M Unit := do
  match (← get).frame[pl.id]?, pl.part with
  | some s@{ value := .static r, .. }, _ =>
    held p pl.id
    bindLocal pl.id { s with value := .static (update f r pl.keys) }
  | some s@{ value := .agg a, .. }, .static v =>
    charge p (a.pathWidth pl.keys)
    held p pl.id
    bindLocal pl.id { s with value := (← setAt p a (.static (f v)) pl.keys).val }
  | _, _ => fail .S010 p "the place has no static part to change"

/-!
The place update at `p` of the aggregate root `a` of the slot `sl` (section 5.4). The part `x`
at the place replaces the old part `o`. The new root has a hardware leaf unless the update
replaces each one. Then the rebind charges the size of the new root from the stored sizes: the
old size, minus the size of `o`, plus the size of `x`. This charge comes before the copy of the
path and before a reference on the path expands. Then the held root charges, the path copies,
and each hardware leaf of the new root binds at the next version of the root. A new root without
a hardware leaf is a static value. It has no rebind charge. Instead, at the same point, it charges
the zero size of each empty part that a reference on the path makes when it expands
(`Agg.emptySize`). The type metadata gives these sizes, as in `normalize`.
-/
def rebind (p : Pos) (pl : Place) (sl : Slot) (a o x : Agg) : M Unit := do
  let hw := a.leaves - o.leaves + x.leaves != 0
  if hw then charge p (a.size - o.size + x.size)
  else charge p (Agg.emptySize (← get).specs a pl.keys)
  held p pl.id
  let r ← setAt p a x pl.keys
  let v ← if hw then do pure (Val.agg (← bindAgg p (← fresh pl.id pl.name) r)) else pure r.val
  bindLocal pl.id { sl with value := v }

/-!
Writes `y` into the place `pl` (section 5.2). A place without a step binds its root again, so a
value with a hardware leaf gets the next version of the root. A place with a step checks the new
depth of the root: the number of steps plus the depth of the value (`S015` at `p`). Then it
writes into the live value of the root, and an aggregate root binds again (`rebind`).
A list holds no value with a hardware leaf: `S011` at `q`, the node of the value. A static root
that takes a value with a hardware leaf becomes a hardware aggregate, so it binds as `rebind`
gives.
-/
def store (p q : Pos) (pl : Place) (y : Val) : M Unit := do
  if pl.keys.isEmpty then
    held p pl.id
    bindLocal pl.id { pl.slot with value := ← named p pl.id pl.name y }
  else
    if pl.inList && (y matches .hw _ | .agg _) then
      fail .S011 q "a list holds no value with a hardware leaf"
    let x ← item q y
    -- The root is within the nesting depth, so only the value on the path can raise it.
    match (← get).frame[pl.id]?, pl.part.agg?, x with
    | some { value := .static _, .. }, _, .static w => do
      bounded p (pl.keys.length + w.depth)
      changeAt p pl fun _ => w
    | some sl@{ value := .static r, .. }, some o, x => do
      bounded p (pl.keys.length + x.depth)
      rebind p pl sl (.static r) o x
    | some sl@{ value := .agg a, .. }, some o, x => do
      bounded p (pl.keys.length + x.depth)
      rebind p pl sl a o x
    | _, _, _ => fail .S010 p "the place has no part for its value"

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
    let x ← if c || q.mode == .comptime then do
        charge p v.size
        pure (.static (← conform p t (← static p (← settle p t v))))
      else copyUse p t true v
    bindLocal q.name.id ⟨some t, false, ← named p q.name.id q.name.name.name x⟩
  | .place pl => do
    charge p pl.part.size
    let pt := pl.ty <|> pl.part.ty?
    unless pt.any (·.same t) do
      let u := match pt with | some u => u.text | none => pl.part.text
      fail .S010 p s!"a `mut` actual has the type {u}, but its formal has {t.text}"
    let x ← if c then pure (Val.static (← static p pl.part)) else pure pl.part
    bindLocal q.name.id ⟨some t, true, ← named p q.name.id q.name.name.name x⟩

/-!
The result of the body of the function `u` in the call frame `path`. A result with a hardware
leaf gets the role `0ret` there, in the place of a name, and each hardware leaf follows it. A
result never takes a version (section 7.3). A body without `return` at its end is `S010` at the
call `p`.
-/
def result (p : Pos) (path : Path) (u : String) : Option Val → M Val
  | some (.hw h) => bindHw p (path.push (.role .ret)) h
  | some (.agg a) => do return .agg (← bindAgg p (path.push (.role .ret)) a)
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
    | .hw _ | .agg _ => fail .S011 x "a list holds no hardware value"
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
`placeAt`, `args`, `ctor`, `actuals`, `invoke`, and `call` get the bound `n` of their caller
after its charge. They call entry functions, `spec`, which a name of a struct item uses, and
the helpers that `call` uses.
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
        | a, b =>
          if (op == .eq || op == .ne) && (a matches .agg _ || b matches .agg _) then
            return some ⟨← aggEq p op a b, false, none⟩
          return some ⟨← hwBinary p op a b, false, none⟩
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
        return some (part o v (← pick p x.pos v i))
      | .field p b f => do
        let o ← need b (← eval n b)
        match o.value with
        | .handle (.inst id path iface) =>
          match (← read).field f.pos >>= (iface.ports[·]?) with
          | some q =>
            if q.input then return some ⟨.handle (.input id path q), true, none⟩
            else
              -- A child output refers, unless it has no hardware leaf and is a new static value.
              let r ← normalize p (.ref (.out path (portName q.name)) q.ty)
              return some ⟨r, !(r matches .static _), none⟩
          | none => fail .S010 p s!"the instance has no port `{f.name}`"
        | v => do
          let w ← if v matches .handle (.res ..) then data p v else pure v
          return some (part o w (← field p f w))
      | .unit p => do charge p Value.unit.size; return some ⟨.static .unit, false, none⟩
      | .tuple p xs => do
        let es ← operands n xs fun x o => element x.pos o.value
        match waiting es with
        | some q => return some ⟨.pending q (.tuple p (es.map (·.1))), false, none⟩
        | none => return some ⟨(← tupleOf p (values es)).val, false, none⟩
      | .array p [] => do charge p 1; return some ⟨.pending p (.empty p), false, none⟩
      | .array p xs => do
        let es ← operands n xs fun x o => element x.pos o.value
        match waiting es with
        | some q => return some ⟨.pending q (.array p (es.map (·.1))), false, none⟩
        | none => return some ⟨(← arrayOf p (values es)).val, false, none⟩
      | .select p b q i => do
        let o ← need b (← eval n b)
        let v ← data p o.value
        return some (part o v (← select p q i v))
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
  no call frame, but it takes a nesting level. A signature can name its own function in a call,
  and the nesting depth ends that cycle. Each depth check of the signature reports `S015` at the
  name. The name makes the value, so a binding of it is no copy.
  -/
  def name (n : Nat) (p : Pos) (x : String) : Ref → M Out
    | .local id => do
      match (← get).frame[id]? with
      | some ⟨_, _, .agg (.ref b t)⟩ =>
        -- An empty input port refers to its name. The read pays its zero, a new static value.
        if t.info.leaves = 0 then return ⟨← normalize p (.ref b t), false, none⟩
        else return ⟨.agg (.ref b t), true, some id⟩
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
        let (qs, r) ← nested p <| inFrame none <|
            withReader (fun c => { c with item := i, frame := ⟨none, 0⟩, site := some p }) do
          let qs ← params n (ps.map fun q => .mk (q.mode == .mut) q.ty)
          return (qs, ← typeExpr n ret)
        let _ ← fnTy p qs r
        return ⟨.static (.function i u.name qs.toArray r), false, none⟩
      | _ => fail .S010 p s!"`{x}` is not a value"
  termination_by (n + 1, 1)

  /--
  The place `target` at `p` (section 5.2). Its root is a `let mut` local, else it is `code` at
  `p`. The place then opens a window of its root (`pend`), and the caller closes it (`shut`).
  Each step charges 1 before it applies. Then the index of an index step evaluates and checks
  against the live value of the root.
  -/
  def placeAt (n : Nat) (p : Pos) (code : ErrorCode) (target : Resolve.Expr) : M Place := do
    let some (root, sels) := chain target
      | fail code p "the root of a place is a `let mut` local"
    let some (id, slot, x) := ← place root
      | fail code p "the root of a place is a `let mut` local"
    pend p x id
    let mut cur := slot.value
    let mut ty := slot.ty
    let mut keys : Array Nat := #[]
    let mut inList := false
    for sel in sels do
      charge sel.pos 1
      let (k, w, ft) ← match sel with
        | .index q [i] => do
          let (k, w) ← pickKey q i.pos cur (← static i.pos (← need i (← eval n i)).value)
          pure (k, w, none)
        | .index q _ => fail .S010 q "an index of a value has one argument"
        | .select q r i => do
          let (k, w) ← selectKey q r i cur
          pure (k, w, none)
        | .field q f => do
          let (k, w, ft) ← fieldKey q f cur
          pure (k, w, some ft)
      ty := match ft, ty with
        | some t, _ => some t
        | none, some t => partTy t k
        | none, none => w.ty?
      inList := inList || cur matches .static (.list ..)
      cur := w
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

  /--
  A constructor call at `p`: the callee result `o` gives a type, and `xs` are its arguments. The
  callee waits while the arguments evaluate.
  -/
  def ctor (n : Nat) (p : Pos) (o : Out) (b : Nat) (xs : List Resolve.Expr) :
      M (Option Out) := do
    let .static (.type t) := o.value | fail .S010 p s!"{o.value.text} is not a function"
    if t matches .fn .. then fail .S010 p s!"a constructor needs a hardware data type, not {t.text}"
    match t, xs with
    | t, [] => return some ⟨.static (← zero p t), false, none⟩
    | t@(.struct ..), xs =>
      let some (_, fs) := fieldsIn (← get).specs t
        | fail .S010 p s!"{t.text} has no specialization"
      if fs.size != xs.length then
        fail .S007 p
          s!"a struct constructor takes 0 or {fs.size} argument(s), but it has {xs.length}"
      hold o
      let vs ← args n b xs
      release o
      charge p (vs.map Val.size).sum
      return some ⟨(← recordOf p t fs.toList (xs.map (·.pos)) vs).val, false, none⟩
    | t, [x] =>
      hold o
      let a ← need x (← eval n x)
      release o
      charge p a.value.size
      return some ⟨.static (← conform p t (← static p a.value)), false, none⟩
    | _, _ => fail .S007 p "a constructor takes 0 or 1 argument(s)"
  termination_by (n + 1, 1)

  /--
  The actuals of the arguments `xs` of a function item, in their evaluation order. The mark of
  an argument in `muts` makes it a `mut` actual, which resolves its place by the steps of an
  assignment target. Its window stays open until the last argument evaluates. Each other
  argument evaluates, and its result waits while the later arguments evaluate.
  -/
  def actuals (n : Nat) (xs : List Resolve.Expr) (muts : List Bool) : M (List Actual) := do
    let acts ← (xs.zip muts).mapM fun (x, m) => do
      if m then return (Actual.place (← placeAt n x.pos .S008 x), none)
      else
        let o ← need x (← eval n x)
        hold o
        return (Actual.value o.value, some o)
    for (a, o) in acts do
      if let some o := o then release o
      if let .place pl := a then shut pl.id
    return acts.map (·.1)
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
  A call of a function item, a prelude function, a function value, or a type. The callee `f`
  evaluates once, before the arguments, and its result selects the call. The arguments `xs` are
  in their evaluation order, and the first binds at the parameter `b` (`bound`). A function item
  runs in the call frame of the call site `k` (`invoke`). A `mut` actual resolves its place in
  the evaluation order of the arguments. A function value checks the number of arguments before
  they evaluate (`S007`), and its callee waits while they evaluate. The `mut` marks of its type
  select the `mut` actuals. It then runs as a call of its function item. Another value that is
  not a type is `S010` at the call (`ctor`).
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
      let acts ← actuals n xs ((unbound b ps).map (·.mode == .mut))
      invoke n p i k c u ps ret ip body (bound b acts)
    | .prim g .push =>
      let [l, x] := xs | fail .S007 p s!"`{g}` takes 2 argument(s), but it has {xs.length}"
      let pl ← placeAt n l.pos .S008 l
      let o ← need x (← eval n x)
      shut pl.id
      pushOnto p x.pos g pl o.value
    | .prim g .pop =>
      let [l] := xs | fail .S007 p s!"`{g}` takes 1 argument(s), but it has {xs.length}"
      let pl ← placeAt n l.pos .S008 l
      shut pl.id
      popFrom p g pl
    | .prim g h => primCall p g h (← args n b xs)
    | .value o =>
      let .static (.function i g qs _) := o.value | ctor n p o b xs
      if qs.size != xs.length then
        fail .S007 p s!"`{g}` takes {qs.size} argument(s), but it has {xs.length}"
      let some (.fn ip c u ps ret body) := (← read).items[i]?
        | fail .S010 p s!"`{g}` is not a function"
      hold o
      let acts ← actuals n xs (qs.toList.map fun (.mk m _) => m)
      release o
      invoke n p i k c u ps ret ip body (bound b acts)
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
        let x ← match t with
          | some t => copyUse p t o.ref o.value
          | none => do
            copy p o
            known o.value
            pure o.value
        let x ← named p b.id b.name.name x
        bindLocal b.id ⟨t <|> x.ty?, m, x⟩
        return none
      | .assign p target v => do
        let pl ← placeAt n p .S010 target
        let o ← need v (← eval n v)
        shut pl.id
        let y ← match pl.ty with
          | some t => copyUse p t o.ref o.value
          | none =>
            copy p o
            if sameForm pl.part o.value then pure o.value
            else fail .S010 p s!"expected {pl.part.text}, but the value is {o.value.text}"
        store p v.pos pl y
        return none
      | .ret p v => do
        let some rt := (← read).ret | fail .S006 p "only a function has `return`"
        let some v := v | fail .S010 p s!"`return` needs a value of {rt.text}"
        let o ← need v (← eval n v)
        return some (← copyUse p rt true o.value)
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

/-!
The rest of the scan of an item. It scans the type and the value of a constant, the type of
an alias, and the result type of a function. Their names take symbols after those of
`scanItem`. Thus the symbols of `scanItem` keep their order.
-/
def scanRest (it : Resolve.Item) : Scan :=
  let go : ScanM Unit := match it with
    | .const _ _ ty v => do scanType ty; scanExpr v
    | .alias _ _ ty => scanType ty
    | .fn _ _ _ _ r _ => scanType r
    | .module .. | .struct .. => pure ()
  (go.run {}).2

/-! The scan of a top expression. -/
def scanTop (e : Resolve.Expr) : Scan := ((scanExpr e).run {}).2

def itemName : Resolve.Item → String
  | .const _ n .. | .fn _ _ n .. | .module _ n .. | .struct _ n .. | .alias _ n .. => n.name

/-!
The symbols of the items. `scans` holds the scan of each item and then that of the top
expression, and `rests` the rest of the scan of each item. The text table runs once for each
elaboration, in time linear in the source up to a logarithmic factor, before the fuel counts.
-/
def symbols (items : Array Resolve.Item) (scans rests : Array Scan) : Syms := Id.run do
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
  for (sc, i) in rests.zipIdx do
    for (p, x) in sc.fields do
      let (t, k) := intern table x
      table := t
      fields := fields.modify i (·.insert p k)
  let mut members := #[]
  for it in items do
    let mut ms : Std.TreeMap Nat Nat compare := {}
    if let .struct _ _ _ fs := it then
      for (f, j) in fs.zipIdx do
        let (t, k) := intern table f.name.name
        table := t
        unless ms.contains k do ms := ms.insert k j
    members := members.push ms
  return ⟨binders, fields, names, members⟩

/-!
The context and the state of an elaboration with the budget `budget`, and with the scan `top`
of its top expression.
-/
def start (budget : Budget) (items : Array Resolve.Item) (top : Scan) : Ctx × St :=
  let syms := symbols items ((items.map scanItem).push top) (items.map scanRest)
  (⟨items, budget.depth, 0, none, 0, syms, ⟨none, 0⟩, [], none, none⟩,
   ⟨budget.fuel, Array.replicate items.size .notStarted, {}, {}, {}, {}, {}⟩)

/-! Runs `act` with the budget. The result has the used fuel. -/
def run (budget : Budget) (items : Array Resolve.Item) (act : Nat → M α) (top : Scan := {}) :
    Except Error (α × Nat) := do
  let (ctx, st) := start budget items top
  let (a, s) ← ((act budget.fuel).run ctx).run st
  return (a, budget.fuel - s.fuel)

/-!
The value of a static expression in the file scope, and the used fuel. The expression has the
symbols of the entry after the items.
-/
def evalExpr (budget : Budget) (items : Array Resolve.Item) (e : Resolve.Expr) :
    Except Error (Value × Nat) :=
  run budget items (top := scanTop e) fun n =>
    withReader (fun c => { c with item := items.size }) do
      static e.pos (← need e (← eval n e)).value

end Silicon.Source.Eval
