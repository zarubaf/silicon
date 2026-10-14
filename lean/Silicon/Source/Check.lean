-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Resolve

/-!
The generic pre-check of slice 1 and of the containers and the types of slice 2: pass 4 of the
front end. It reads the resolved AST of `Source.Resolve`. It gives the same AST, or the first
error of `S005` to `S008` by position.

These checks need no static values. Widths, types, and the dynamic stage rule are for `Elab`.
The check runs on each item, also on an item that no instantiation uses. It checks both
branches of each `comptime if`.

`S005`: a static position does not name a port, a register, a wire, a memory, or an instance. The
rule is syntactic. It looks only at names that resolve to the declaration of such a resource. A
`let` alias of a resource and a domain name are for the stage rule `S011` of `Elab`. The error is
at the name. These are the static positions:

1. Each argument of an index: `T[e]` in a type and `b[e]` in an expression. Thus each argument
   of a struct specialization `P[e]`. Also the length `N` of an array type `[T; N]`, in a type
   and in an expression.
2. The value of a `const` item.
3. The condition of a `comptime if`, and both bounds of a `comptime for`.
4. Each argument of an `instance`.
5. The reset value of a `reg`, and the depth `N` of a `mem m: [T; N]`.
6. The callee of each call.
7. Each argument of a call to a `comptime fn` item, and each argument at a `comptime` parameter
   of a call to a `fn` item. A receiver call binds its receiver and its arguments to the
   parameters first, so this also holds for the receiver and for each explicit argument.
8. The first argument of `resize`, `reinterpret`, and `list`, and each argument of
   `static_assert` and `error`. These are the `comptime` parameters of the prelude, and the
   arguments of the prelude functions that take a message. The argument of `data_bits(T)` is
   not a static position (section 5.6).
9. The argument of a constructor `T(n)`: a call whose callee is a prelude type, an index of
   one, or an array type `[T; N]`. The arguments of a struct constructor are not static
   positions.
10. Each part of an expression in a static position. A static expression is thus built only of
   static parts, also in a branch that a static condition does not select.

`S006` is at the statement:

- A module body has no `return`, also in a nested block.
- A `comptime fn` has no `input`, `output`, `reg`, `wire`, `mem`, `instance`, or `:=` statement.
- A `comptime fn` has no call of the prelude functions `read_port` and `write_port`, also in the
  receiver form. The rule reads the resolved callee, so a user function with such a name has no
  rule. The error is at the call. It comes before an `S007` of the call at that position.

`S007` is at the call, the index, the type name, or the `instance` statement:

- A call to a `fn` item has one argument for each parameter.
- `resize`, `reinterpret`, `static_assert`, and `push` have two arguments. `error`, `len`,
  `data_bits`, `list`, `pop`, and `str` have one. `read_port` has three, and `write_port` four.
- A receiver call `x.m(args)` binds its receiver to the first parameter of `m` without a written
  `comptime` mark, also in a `comptime fn`. A function without such a parameter is `S007` at the
  call. Then the receiver and the arguments together have one argument for each parameter. The
  modes of the prelude are those of section 5.6: `T` of `resize`, `reinterpret`, and `list` is
  `comptime`, and the list of `push` and `pop` is `mut`. Thus `T.data_bits()` binds `T`.
- A constructor `T(n)` of a prelude type or an array type has one argument. `T()` has none: it
  is the zero of `T`.
- A struct constructor has one argument for each field. `P()` has none: it is the zero of `P`
  (section 5.6).
- An `instance` has one argument for each parameter of its module.
- `UInt`, `SInt`, and `List` have one index argument. `Bool`, `Nat`, `Int`, `Unit`, `Type`, and
  `String` have none.
  A struct has one index argument for each parameter. The prelude struct `ReadResponse` thus
  has one, and its constructor two arguments. Thus each use of a struct with parameters
  has its arguments, also the callee of a constructor. This also holds for a type name in an
  expression. A complete type such as `UInt[8]`, `P[8]`, a `type` item, `()`, a tuple type, or
  an array type takes no index.
- A function type takes no index, in a type and in an expression: `(fn () -> UInt)[8]` is
  `S007` at the index.

A call through a function value, a local, or a `const` has no known arity. `Elab` checks it in
pass 5: `S007` for a function value, else `S010`. The type of a `type` item and of a local is
known only in `Elab`, so `Elab` checks its constructor. A constructor of a function type has no
rule of this check either, and its arguments are not static positions. A function name as a value
is a name like another. `Elab` checks that it is not generic and not a builtin (`S010`).

`S008` follows section 9.1. A mutable root is a `let mut` local or a `mut` parameter. A place is
a name, or an index, a selector `.N`, or a field of a place. Its root is that name. An index of a
place is a static position, so `Elab` checks that it is static (`S011`). A `mut` actual is an
argument at a `mut` parameter of a `fn` item, of `push`, or of `pop`, also the receiver of a
receiver call:

- A `mut` actual that is not a place, or whose root is not a mutable root, is `S008` at the start
  of the actual.
- A `mut` actual makes its root pending before its indices. The root stays pending until the
  call ends, so the window holds the indices of the actual and each later argument of the call.
  The receiver of a receiver call comes first, then the arguments from left to right: the
  evaluation order, not the binding order.
- An assignment `place = e` makes the root of its place pending for the indices of the place and
  for `e`.
- A `mut` actual whose root is pending is `S008` at the start of the actual. An assignment is a
  statement, so no window holds one.

Each local has a counter of the windows that hold its root as pending. A `mut` actual reads and
changes only the counter of its root, so each step takes constant amortized time. A call through
a local or a `const` has no known parameter modes. `Eval` checks its `S008` in pass 5.

The other rules of the containers need static values, so they are for `Elab` (`S010`, `S011`,
and `S013`). Among them are an index with two or more arguments, `<` on containers, and `==` on
containers without a common type.

Errors compete by position. At one position, the first error of the walk wins. Before slice 2,
only two `S007` errors could share a position. A receiver call starts at its receiver, so its
`S007` can share the position of an `S005` or an `S008` at the receiver. The walk checks the
binding and the arity of the call first, because the receiver has no parameter before the
binding. Then it checks the receiver as a `mut` actual (`S008`), then its parts (`S005`).

The prelude struct `ReadResponse` is an item of the resolved file, but it has no source position.
The walk skips it, so its errors never compete by position (section 5.6).

The walk is a single pass in source order. Its recursion follows the blocks and the expressions.
The syntax depth thus bounds it at about 2N. A loop handles each list. The resources, the mutable
roots, and the pending counters of an item are arrays by local number, so each step takes
constant amortized time.
-/
namespace Silicon.Source.Check

open Resolve

/-! A resource that a static position cannot name. -/
inductive Resource where
  | port | reg | wire | mem | inst
  deriving Repr, DecidableEq, BEq, Inhabited

def Resource.text : Resource → String
  | .port => "a port" | .reg => "a register" | .wire => "a wire" | .mem => "a memory"
  | .inst => "an instance"

/-! A local: a resource, a mutable root, or another local. -/
inductive Local where
  | plain
  | resource (r : Resource)
  | mutable
  deriving Inhabited

/-!
The signature of an item. A function has its `comptime` mark and the mode of each parameter.
Each parameter of a `comptime fn` is static. A module has its number of parameters. A struct has
its number of parameters and its number of fields.
-/
inductive Sig where
  | const
  | fn (comptime : Bool) (modes : Array ParamMode)
  | module (arity : Nat)
  | struct (params fields : Nat)
  | alias

def sig : Resolve.Item → Sig
  | .const .. => .const
  | .fn _ c _ ps _ _ => .fn c (ps.map (·.mode)).toArray
  | .module _ _ ps _ _ => .module ps.length
  | .struct _ _ ps fs _ => .struct ps.length fs.length
  | .alias .. => .alias

/-! The item of a statement, for `S006`. -/
inductive Owner where
  | module | fn | comptimeFn
  deriving DecidableEq, BEq

/-!
The state of the walk. `locals` maps the local number of each resource and each mutable root of
the current item to its kind. `pending` maps a local number to the number of windows that hold
it as a pending root. `err` holds the first error by position. `comptime` is true in the body
of a `comptime fn`.
-/
structure St where
  locals : Array Local
  pending : Array Nat
  err : Option Error
  comptime : Bool

/-! The context of the walk is the signature of each item. -/
abbrev M := ReaderT (Array Sig) (StateM St)

def report (code : ErrorCode) (pos : Pos) (msg : String) : M Unit :=
  modify fun s => { s with err := earlier s.err ⟨code, pos, msg⟩ }

/-! `a` with the entry `i` set to `x`. Local numbers are dense, so the array stays small. -/
def setAt [Inhabited α] (a : Array α) (i : Nat) (x : α) : Array α :=
  let a := if a.size ≤ i then a ++ Array.replicate (i + 1 - a.size) default else a
  a.set! i x

/-! Records the kind of the local `b`. -/
def declare (b : Binder) (l : Local) : M Unit :=
  modify fun s => { s with locals := setAt s.locals b.id l }

/-! `S007` at `pos` if `what` has `got` arguments, not `want`. -/
def arity (pos : Pos) (what : String) (want got : Nat) : M Unit :=
  if want == got then pure ()
  else report .S007 pos s!"{what} takes {want} argument(s), but it has {got}"

def typeArity : PrimType → Nat
  | .uint | .sint | .list => 1
  | .bool | .nat | .int | .unit | .type | .string => 0

/-!
True for each static argument of a prelude function, by its index. A `comptime` parameter is
static. Each argument of a function that takes a message is static too (section 5.6).
-/
def fnStatic (f : PrimFn) (k : Nat) : Bool :=
  f == .staticAssert || f == .error || (fnModes f)[k]? == some .comptime

/-! `S006` at the call `pos` of a memory port function `f` in a `comptime fn`. -/
def portCall (pos : Pos) : Ref → M Unit
  | .fn f => do
    if f.port && (← get).comptime then
      report .S006 pos "a `comptime fn` has no memory port call"
  | _ => pure ()

/-! A function that a call names: its parameter modes and its static parameters, by index. -/
structure Callee where
  modes : Array ParamMode
  static : Nat → Bool

/-! The callee of a `fn` item or a prelude function. Another name has no known parameters. -/
def callee : Ref → M (Option Callee)
  | .item i => do
    match (← read)[i]? with
    | some (.fn c ms) => return some ⟨ms, fun k => c || ms[k]? == some .comptime⟩
    | _ => return none
  | .fn f => return some ⟨fnModes f, fnStatic f⟩
  | _ => return none

/-! The mode of the parameter `k` of the callee `c`. -/
def modeAt (c : Option Callee) (k : Nat) : ParamMode :=
  (c.bind (·.modes[k]?)).getD .none

/-!
The rule of a constructor call `T(...)`. A `convert` type takes no argument or one static
argument. A `record` type takes no argument or one argument for each field. Only `Elab` knows the
type of a `type` item, so its rule is `unknown`.
-/
inductive Ctor where
  | convert
  | record (fields : Nat)
  | unknown

/-! A type head: its text, its number of missing index arguments, and its constructor rule. -/
structure Head where
  text : String
  missing : Nat
  ctor : Ctor

/-!
The type head of the type name `n`. A struct item misses its parameters. A `type` item is a
complete type. A local has no known head.
-/
def head (n : String) : Ref → M (Option Head)
  | .type t => return some ⟨s!"`{n}`", typeArity t, .convert⟩
  | .item i => do
    match (← read)[i]? with
    | some (.struct k f) => return some ⟨s!"`{n}`", k, .record f⟩
    | some .alias => return some ⟨s!"`{n}`", 0, .unknown⟩
    | _ => return none
  | _ => return none

/-! The head of a type that a type node makes: a complete type. -/
def complete (h : Head) : Head := { h with text := "a complete type", missing := 0 }

/-! A name that is not a type. A resource in a static position is `S005`. -/
def name (static : Bool) (pos : Pos) (n : String) : Ref → M Unit
  | .local id => do
    if static then
      if let some (.resource r) := (← get).locals[id]? then
        report .S005 pos s!"`{n}` is {r.text}; a static position needs a static value"
  | _ => pure ()

/-!
The arity of a call at `pos` with the callee `f` and `got` arguments. `h` is the type head of a
type callee. The result is the callee: the modes of the parameters and the static positions.
A constructor `T(n)` has no modes, and its argument is static.
-/
def call (pos : Pos) (f : Resolve.Expr) (h : Option Head) (got : Nat) : M (Option Callee) := do
  match h, f with
  | some h, _ =>
    match h.ctor with
    | .convert =>
      if got > 1 then
        report .S007 pos s!"a constructor takes 0 or 1 argument(s), but it has {got}"
      return some ⟨#[], fun _ => true⟩
    | .record k =>
      unless got == 0 || got == k do
        report .S007 pos s!"a struct constructor takes 0 or {k} argument(s), but it has {got}"
      return none
    | .unknown => return none
  | none, .name _ g r =>
    let c ← callee r
    if let some c := c then arity pos s!"`{g}`" c.modes.size got
    return c
  | none, _ => return none

/-!
The binding of the receiver call at `pos` to the function `m` with the reference `r` and `got`
explicit arguments. The receiver binds to the parameter `b` of `Resolve`. The result is the
callee and `b`, or `none` after an `S007`.
-/
def receiver (pos : Pos) (m : Ident) (r : Ref) (b : Option Nat) (got : Nat) :
    M (Option (Callee × Nat)) := do
  let some c ← callee r | return none
  match b with
  | none =>
    report .S007 pos s!"`{m.name}` has no parameter without `comptime` for the receiver"
    return none
  | some b =>
    arity pos s!"`{m.name}`" c.modes.size (got + 1)
    return some (c, b)

/-! The local of the root of a place, if the expression is a place with a local root. -/
def root : Resolve.Expr → Option Nat
  | .name _ _ (.local id) => some id
  | .index _ b _ | .select _ b .. | .field _ b _ => root b
  | _ => none

/-! Makes the local `id` pending for one more window. `release` ends the windows. -/
def hold (id : Nat) : M Unit :=
  modify fun s => { s with pending := setAt s.pending id (s.pending.getD id 0 + 1) }

def release (ids : List Nat) : M Unit :=
  for id in ids do
    modify fun s => { s with pending := s.pending.modify id (· - 1) }

/-!
The `mut` actual `x`, before its parts. It is `S008` if it is not a place with a mutable root, or
if its root is pending. Then its root is pending. The result is the root, for `release`.
-/
def mutActual (x : Resolve.Expr) : M (Option Nat) := do
  let s ← get
  match root x with
  | some id =>
    unless s.locals[id]? matches some .mutable do
      report .S008 x.pos "a `mut` actual has a `let mut` local or a `mut` formal as its root"
      return none
    if s.pending.getD id 0 > 0 then
      report .S008 x.pos "the root of this `mut` actual is pending in its window"
    hold id
    return some id
  | none =>
    report .S008 x.pos "a `mut` actual is a place"
    return none

/-!
The check of the actual `x` at the parameter `k` of the callee `c`, before its parts. The result
is the root that it makes pending, for `release`.
-/
def pre (c : Option Callee) (k : Nat) (x : Resolve.Expr) : M (List Nat) :=
  if modeAt c k == .mut then return (← mutActual x).toList else return []

/-! True if the parameter `k` of the callee `c` is a static position in the context `static`. -/
def staticAt (static : Bool) (c : Option Callee) (k : Nat) : Bool :=
  static || (c.map (·.static k)).getD false

/-!
An expression and a type expression. `static` is true in a static position. `base` is true for
the base of an index, whose index holds the arguments of a type name. The result of an
expression is the type head of a type in an expression: a type name, an index of one, or
`[T; N]`. Another expression gives `none`. Thus the walk visits each node once.
-/
mutual
  def visit (static base : Bool) : Resolve.Expr → M (Option Head)
    | .num .. | .bool .. | .str .. => return none
    | .name p n r => do
      match ← head n r with
      | some h =>
        unless base do arity p h.text h.missing 0
        return some h
      | none => name static p n r; return none
    | .unary _ _ a => do let _ ← visit static false a; return none
    | .binary _ _ l r => do
      let _ ← visit static false l
      let _ ← visit static false r
      return none
    | .cond _ c y n => do
      let _ ← visit static false c
      let _ ← visit static false y
      let _ ← visit static false n
      return none
    | .call p f xs _ => do
      if let .name _ _ r := f then portCall p r
      let h ← visit true false f
      let c ← call p f h xs.length
      let mut held := []
      let mut k := 0
      for x in xs do
        held := (← pre c k x) ++ held
        let _ ← visit (staticAt static c k) false x
        k := k + 1
      release held
      return none
    | .method p r m f b xs _ => do
      -- The receiver evaluates first. It binds to the parameter `b`, so the argument `k` binds
      -- to the parameter `k` before `b` and to `k + 1` from `b` on.
      portCall p f
      let cb ← receiver p m f b xs.length
      let c := cb.map (·.1)
      let b := (cb.map (·.2)).getD 0
      let mut held ← pre c b r
      let _ ← visit (staticAt static c b) false r
      let mut k := 0
      for x in xs do
        let j := if k < b then k else k + 1
        held := (← pre c j x) ++ held
        let _ ← visit (staticAt static c j) false x
        k := k + 1
      release held
      return none
    | .index p b xs => do
      let h ← visit static true b
      if let some h := h then arity p h.text h.missing xs.length
      for x in xs do let _ ← visit true false x
      return h.map complete
    | .field _ b _ | .select _ b .. => do let _ ← visit static false b; return none
    | .unit _ => return none
    | .tuple _ xs | .array _ xs => do
      for x in xs do let _ ← visit static false x
      return none
    | .arrayType _ t n => do
      typeExpr t
      let _ ← visit true false n
      return some ⟨"a complete type", 0, .convert⟩
    | .fnType _ ps r => do
      for q in ps do fnParam q
      typeExpr r
      return some ⟨"a function type", 0, .unknown⟩

  def typeExpr : Resolve.TypeExpr → M Unit
    | .name p n r => do
      if let some h ← head n r then arity p h.text h.missing 0
    | .index p (.name _ n r) xs => do
      if let some h ← head n r then arity p h.text h.missing xs.length
      for x in xs do let _ ← visit true false x
    | .index p b xs => do
      arity p (if b matches .fn .. then "a function type" else "a complete type") 0 xs.length
      typeExpr b
      for x in xs do let _ ← visit true false x
    | .unit _ => pure ()
    | .tuple _ ts => for t in ts do typeExpr t
    | .array _ t n => do typeExpr t; let _ ← visit true false n
    | .fn _ ps r => do
      for q in ps do fnParam q
      typeExpr r

  /-- A parameter type of a function type. -/
  def fnParam : Resolve.FnParam → M Unit
    | .mk _ t => typeExpr t
end

def expr (static : Bool) (e : Resolve.Expr) : M Unit := do let _ ← visit static false e

/-! `S006` at `pos` if a `comptime fn` has the statement `what`. -/
def placement (o : Owner) (pos : Pos) (what : String) : M Unit :=
  if o == .comptimeFn then report .S006 pos s!"a `comptime fn` has no {what}" else pure ()

mutual
  def stmt (o : Owner) : Resolve.Stmt → M Unit
    | .local _ m b ty v => do
      if let some ty := ty then typeExpr ty
      expr false v
      if m then declare b .mutable
    | .assign _ t v => do
      let id := root t
      if let some id := id then hold id
      expr false t
      expr false v
      release id.toList
    | .connect p t v => do
      placement o p "`:=`"
      expr false t
      expr false v
    | .reg p b ty i => do
      placement o p "register"
      typeExpr ty
      expr true i
      declare b (.resource .reg)
    | .wire p b ty => do placement o p "wire"; typeExpr ty; declare b (.resource .wire)
    | .mem p b w d => do
      placement o p "memory"
      typeExpr w
      expr true d
      declare b (.resource .mem)
    | .input p b ty => do placement o p "port"; typeExpr ty; declare b (.resource .port)
    | .output p b ty => do placement o p "port"; typeExpr ty; declare b (.resource .port)
    | .inst p b m i xs => do
      placement o p "instance"
      if let some (.module k) := (← read)[i]? then arity p s!"`{m.name}`" k xs.length
      for x in xs do expr true x
      declare b (.resource .inst)
    | .ret p v => do
      if o == .module then report .S006 p "a module body has no `return`"
      if let some v := v then expr false v
    | .ctIf _ c y n => do
      expr true c
      stmts o y
      if let some n := n then stmts o n
    | .ctFor _ _ lo hi b => do expr true lo; expr true hi; stmts o b
    | .block _ b => stmts o b
    | .expr _ v => expr false v
    | .alias _ _ ty => typeExpr ty

  /-- The statements of one block, in a loop. -/
  def stmts (o : Owner) (ss : List Resolve.Stmt) : M Unit := do
    for s in ss do stmt o s
end

def item : Resolve.Item → M Unit
  | .const _ _ ty v => do typeExpr ty; expr true v
  | .fn _ c _ ps r b => do
    for p in ps do
      typeExpr p.ty
      if p.mode == .mut then declare p.name .mutable
    typeExpr r
    modify fun s => { s with comptime := c }
    stmts (if c then .comptimeFn else .fn) b
    modify fun s => { s with comptime := false }
  | .module _ _ ps _ b => do
    for p in ps do typeExpr p.ty
    stmts .module b
  | .struct _ _ _ _ true => pure ()
  | .struct _ _ ps fs false => do
    for p in ps do typeExpr p.ty
    for f in fs do typeExpr f.ty
  | .alias _ _ ty => typeExpr ty

/-! The resolved items, or the first error of pass 4 by position. It runs after `resolve`. -/
def check (items : Array Resolve.Item) : Except Error (Array Resolve.Item) :=
  let walk : M Unit := items.forM fun it => do
    modify fun s => { s with locals := #[], pending := #[] }
    item it
  let ((), s) := (walk.run (items.map sig)).run ⟨#[], #[], none, false⟩
  match s.err with
  | some e => .error e
  | none => .ok items

/-! A static expression in the file scope, such as the `EXPR` of `eval`, or its first error. -/
def checkExpr (items : Array Resolve.Item) (e : Resolve.Expr) : Except Error Unit :=
  let ((), s) := ((expr true e).run (items.map sig)).run ⟨#[], #[], none, false⟩
  match s.err with
  | some e => .error e
  | none => .ok ()

end Silicon.Source.Check
