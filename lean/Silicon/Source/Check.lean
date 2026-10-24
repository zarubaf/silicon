-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Resolve

/-!
The generic pre-check: pass 4 of the front end. It covers slice 1, the containers and the types
of slice 2, and the enums of slice 3. It reads the resolved AST of `Source.Resolve`. It gives the
same AST, or the first error of `S005` to `S008` by position.

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
2. The value of a `const` item, and the tag value of each variant of an `enum` item.
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
   one, or an array type `[T; N]`. The arguments of a struct constructor and of a variant
   constructor are not static positions.
10. Each part of an expression in a static position. A static expression is thus built only of
   static parts, also in a branch that a static condition does not select.
11. From slice 4 on, the key of an indexed `input` or `output` (section 5.6). The key of a family
   selection `req[k]` is an index argument, so rule 1 holds for it.

A port family names ports, so its name in a static position is `S005`, also before its first
declaration. A family is no mutable root, so a `mut` actual with a family root is `S008`.

`S006` is at the statement:

- A module body has no `return`, also in a nested block.
- A `comptime fn` has no `input`, `output`, `reg`, `wire`, `mem`, `instance`, or `:=` statement.
- A `comptime fn` has no call of the prelude functions `read_port` and `write_port`, also in the
  receiver form. The rule reads the resolved callee, so a user function with such a name has no
  rule. The error is at the call. It comes before an `S007` of the call at that position.

`S007` is at the call, the index, the type name, or the `instance` statement:

- A call to a `fn` item has one argument for each parameter.
- `resize`, `reinterpret`, `static_assert`, and `push` have two arguments. `error`, `len`,
  `data_bits`, `list`, `pop`, `str`, and `read` have one. `read_port` has three, and `write_port`
  four.
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
- `UInt`, `SInt`, `List`, `Reg`, `Wire`, and `Input` have one index argument, and `Mem` has two.
  `Instance` has its module and one argument for each parameter of the module, so a bare
  `Instance` misses one. The text of these families ends with their signature (section 6.2).
  `Bool`, `Nat`, `Int`, `Unit`, `Type`, and `String` have none.
  A struct has one index argument for each parameter. The prelude struct `ReadResponse` thus
  has one, and its constructor two arguments. The prelude structs of slice 4 have none. Thus
  each use of a struct with parameters has its arguments, also the callee of a constructor.
  This also holds for a type name in an expression. A complete type such as `UInt[8]`, `P[8]`,
  a `type` item, `()`, a tuple type, or an array type takes no index.
- A function type takes no index, in a type and in an expression: `(fn () -> UInt)[8]` is
  `S007` at the index.
- A variant constructor `E::V(args)` has one argument for each payload type of `V`. A path
  `E::V` without a call has none. The error is at the start of the path (section 5.6). An enum
  has no parameters, so its name takes no index. Only `Elab` checks a call `E(args)` of the
  enum type (`S010`).
- A variant pattern `E::V(b, _)` has one binder or `_` for each payload type of `V`. The error
  is at the start of the path. A binder is a plain local: a static position can name it, and it
  is no mutable root.

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

The prelude structs are items of the resolved file, but they have no source position. The walk
skips them by their `prelude` flag, so their errors never compete by position (section 5.6).

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
its number of parameters and its number of fields. An enum has the number of payload types of
each variant.
-/
inductive Sig where
  | const
  | fn (comptime : Bool) (modes : Array ParamMode)
  | module (arity : Nat)
  | struct (params fields : Nat)
  | alias
  | enum (payloads : Array Nat)

def sig : Resolve.Item → Sig
  | .const .. => .const
  | .fn _ c _ ps _ _ => .fn c (ps.map (·.mode)).toArray
  | .module _ _ ps _ _ => .module ps.length
  | .struct _ _ ps fs _ => .struct ps.length fs.length
  | .alias .. => .alias
  | .enum _ _ _ vs => .enum (vs.map (·.payload.length)).toArray

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

/-! `S007` at `pos` if `what` has `got` arguments, not `want`. `fix` ends the text. -/
def arity (pos : Pos) (what : String) (want got : Nat) (fix := "") : M Unit :=
  if want == got then pure ()
  else report .S007 pos s!"{what} takes {want} argument(s), but it has {got}{fix}"

/-! The number of index arguments of a prelude type. `Instance` adds the module parameters. -/
def typeArity : PrimType → Nat
  | .uint | .sint | .list | .reg | .wire | .input | .instance => 1
  | .mem => 2
  | .bool | .nat | .int | .unit | .type | .string => 0

/-! The signature of a prelude type family, for the fix of its `S007` (section 6.2). -/
def signature : PrimType → Option String
  | .uint => some "UInt[W]" | .sint => some "SInt[W]" | .list => some "List[T]"
  | .reg => some "Reg[T]" | .wire => some "Wire[T]" | .input => some "Input[T]"
  | .mem => some "Mem[T, N]" | .instance => some "Instance[M, args]"
  | .bool | .nat | .int | .unit | .type | .string => none

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

/-!
A type head: its text, its number of missing index arguments, and its constructor rule. `fix`
ends the text of its `S007`. `inst` is true for `Instance`, which also misses one argument for
each parameter of its module.
-/
structure Head where
  text : String
  missing : Nat
  ctor : Ctor
  fix : String := ""
  inst : Bool := false

/-!
The `S007` text of the struct type `x` with `n` parameters and `m` index arguments (section 6.2).
Pass 4 builds it from `structFix`, and pass 5 gives it whole.
-/
def structTypeArity (x : String) (n m : Nat) : String :=
  s!"`{x}` takes {n} argument(s), but it has {m}; pass one argument for each `comptime` " ++
    s!"parameter of `{x}`"

/-! The fix of `structTypeArity` for the struct `x`. -/
def structFix (x : String) : String :=
  s!"; pass one argument for each `comptime` parameter of `{x}`"

/-!
The type head of the type name `n`. A struct item misses its parameters. A `type` item and an
`enum` item are complete types. A local has no known head.
-/
def head (n : String) : Ref → M (Option Head)
  | .type t =>
    let fix := ((signature t).map (s!"; write `{·}`")).getD ""
    return some { text := s!"`{n}`", missing := typeArity t, ctor := .convert, fix,
                  inst := t == .instance }
  | .item i => do
    match (← read)[i]? with
    | some (.struct k f) =>
      return some { text := s!"`{n}`", missing := k, ctor := .record f, fix := structFix n }
    | some .alias | some (.enum _) =>
      return some { text := s!"`{n}`", missing := 0, ctor := .unknown }
    | _ => return none
  | _ => return none

/-! The head of a type that a type node makes: a complete type. -/
def complete (h : Head) : Head :=
  { h with text := "a complete type", missing := 0, fix := "", inst := false }

/-!
`S007` at `pos` if the head `h` with the index arguments `xs` misses arguments. The module of
`Instance` is its first argument, a module item after `Resolve`.
-/
def indexArity (pos : Pos) (h : Head) (xs : List Resolve.Expr) : M Unit := do
  let mut want := h.missing
  if h.inst then
    if let .name _ _ (.item i) :: _ := xs then
      if let some (.module k) := (← read)[i]? then want := want + k
  arity pos h.text want xs.length h.fix

/-! `S007` at `pos` if the variant `x::y` with `want` payload types has `got` payload values. -/
def payloads (pos : Pos) (x y : Ident) (want got : Nat) : M Unit :=
  if want == got then pure ()
  else report .S007 pos (s!"the variant `{x.name}::{y.name}` has {want} payload value(s), but " ++
    s!"the constructor has {got}; pass one value for each payload type")

/-!
`S007` at the start of a variant pattern whose binders and `_` do not match the payload values
of its variant.
-/
def pattern : Resolve.Pattern → M Unit
  | .variant p _ y i j bs => do
    let some (.enum ns) := (← read)[i]? | pure ()
    let n := ns.getD j 0
    unless n == bs.length do
      report .S007 p (s!"the variant `{y.name}` has {n} payload value(s), but the pattern has " ++
        s!"{bs.length}; write one binder or `_` for each payload value")
  | _ => pure ()

/-! `S005` at `pos` for the name `n` of the resource `r` in a static position. -/
def staticResource (pos : Pos) (n : String) (r : Resource) : M Unit :=
  report .S005 pos s!"`{n}` is {r.text}; a static position needs a static value"

/-! A name that is not a type. A resource or a port family in a static position is `S005`. -/
def name (static : Bool) (pos : Pos) (n : String) : Ref → M Unit
  | .local id => do
    if static then
      if let some (.resource r) := (← get).locals[id]? then staticResource pos n r
  | .family .. => if static then staticResource pos n .port else pure ()
  | _ => pure ()

/-! The fix of the `S007` text of the prelude `read` (section 6.2). Another callee has none. -/
def readFix : Ref → String
  | .fn .read => "; write `read(h)` with one register or wire"
  | _ => ""

/-!
The `S007` text of a struct constructor with `n` fields and `m` arguments (section 6.2). Pass 4
and pass 5 both give it.
-/
def structArity (n m : Nat) : String :=
  s!"a struct constructor takes 0 or {n} argument(s), but it has {m}; pass one value for " ++
    "each field, or none for the zero"

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
        report .S007 pos (structArity k got)
      return none
    | .unknown => return none
  | none, .name _ g r =>
    let c ← callee r
    if let some c := c then arity pos s!"`{g}`" c.modes.size got (readFix r)
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
    arity pos s!"`{m.name}`" c.modes.size (got + 1) (readFix r)
    return some (c, b)

/-! The local of the root of a place, if the expression is a place with a local root. -/
def root : Resolve.Expr → Option Nat
  | .name _ _ (.local id) | .name _ _ (.family id _) => some id
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
        unless base do arity p h.text h.missing 0 h.fix
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
      if let some h := h then indexArity p h xs
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
      return some { text := "a complete type", missing := 0, ctor := .convert }
    | .fnType _ ps r => do
      for q in ps do fnParam q
      typeExpr r
      return some { text := "a function type", missing := 0, ctor := .unknown }
    | .variant p x y i j xs _ => do
      if let some (.enum ns) := (← read)[i]? then payloads p x y (ns.getD j 0) xs.length
      for a in xs do let _ ← visit static false a
      return none
    | .«match» _ x as => do
      let _ ← visit static false x
      for a in as do arm static a
      return none

  /-- An arm: the arity of its pattern, then its value. A binder is a plain local. -/
  def arm (static : Bool) : Resolve.Arm → M Unit
    | .mk q v => do pattern q; let _ ← visit static false v

  def typeExpr : Resolve.TypeExpr → M Unit
    | .name p n r => do
      if let some h ← head n r then arity p h.text h.missing 0 h.fix
    | .index p (.name _ n r) xs => do
      if let some h ← head n r then indexArity p h xs
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
    | .input p b k ty | .output p b k ty => do
      placement o p "port"
      if let some k := k then expr true k
      typeExpr ty
      declare b (.resource .port)
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
  | .enum _ _ t vs => do
    typeExpr t
    for v in vs do
      for q in v.payload do typeExpr q
      expr true v.tag

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
