-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Resolve

/-!
The generic pre-check of slice 1 and of the containers and the types of slice 2: pass 4 of the
front end. It reads the resolved AST of `Source.Resolve`. It gives the same AST, or the first
error of `S005` to `S007` by position.

These checks need no static values. Widths, types, and the dynamic stage rule are for `Elab`.
The check runs on each item, also on an item that no instantiation uses. It checks both
branches of each `comptime if`.

`S005`: a static position does not name a port, a register, a wire, or an instance. Slice 1 has
no memory. The rule is syntactic. It looks only at names that resolve to the declaration of such
a resource. A `let` alias of a resource and a domain name are for the stage rule `S011` of
`Elab`. The error is at the name. These are the static positions:

1. Each argument of an index: `T[e]` in a type and `b[e]` in an expression. Thus each argument
   of a struct specialization `P[e]`. Also the length `N` of an array type `[T; N]`, in a type
   and in an expression.
2. The value of a `const` item.
3. The condition of a `comptime if`, and both bounds of a `comptime for`.
4. Each argument of an `instance`.
5. The reset value of a `reg`.
6. The callee of each call.
7. Each argument of a call to a `comptime fn` item, and each argument at a `comptime` parameter
   of a call to a `fn` item.
8. The first argument of `resize` and `reinterpret`, and each argument of `static_assert` and
   `error`.
9. The argument of a constructor `T(n)`: a call whose callee is a prelude type, an index of
   one, or an array type `[T; N]`. The arguments of a struct constructor are not static
   positions.
10. Each part of an expression in a static position. A static expression is thus built only of
   static parts, also in a branch that a static condition does not select.

`S006` is at the statement:

- A module body has no `return`, also in a nested block.
- A `comptime fn` has no `input`, `output`, `reg`, `wire`, `instance`, or `:=` statement.

`S007` is at the call, the index, the type name, or the `instance` statement:

- A call to a `fn` item has one argument for each parameter.
- `resize`, `reinterpret`, and `static_assert` have two arguments. `error`, `len`, and
  `data_bits` have one.
- A constructor `T(n)` of a prelude type or an array type has one argument. `T()` has none: it
  is the zero of `T`.
- A struct constructor has one argument for each field. `P()` has none: it is the zero of `P`
  (section 5.6).
- An `instance` has one argument for each parameter of its module.
- `UInt` and `SInt` have one index argument. `Bool`, `Nat`, `Int`, `Unit`, and `Type` have none.
  A struct has one index argument for each parameter. Thus each use of a struct with parameters
  has its arguments, also the callee of a constructor. This also holds for a type name in an
  expression. A complete type such as `UInt[8]`, `P[8]`, a `type` item, `()`, a tuple type, or
  an array type takes no index.

A call through a local or a `const` has no known arity. `Elab` checks it with `S010`. The type of
a `type` item and of a local is known only in `Elab`, so `Elab` checks its constructor.

`S008` cannot occur in slice 1, so this check has no code for it. The parser rejects a `mut`
formal with `S004`, so no `mut` actual exists. No expression mutates a root. An assignment is a
statement, also with an index or a selector `.N` in its place. The containers have no `push`,
no `pop`, and no receiver call. Thus no window of section 9.1 holds a mutation.

The other rules of the containers need static values, so they are for `Elab` (`S010`, `S011`,
and `S013`). Among them are an index with two or more arguments, `<` on containers, and `==` on
containers without a common type.

Errors compete by position. At one position, the first error of the walk wins. Only two `S007`
errors can share a position, so the code and the line do not depend on this order.

The walk is a single pass in source order. Its recursion follows the blocks and the expressions.
The syntax depth thus bounds it at about 2N. A loop handles each list. The resources of an item
are an array by local number, so each step takes constant amortized time.
-/
namespace Silicon.Source.Check

open Resolve

/-! A resource that a static position cannot name. -/
inductive Resource where
  | port | reg | wire | inst
  deriving Repr, DecidableEq, BEq, Inhabited

def Resource.text : Resource → String
  | .port => "a port" | .reg => "a register" | .wire => "a wire" | .inst => "an instance"

/-!
The signature of an item. A function has a flag for each parameter: true for a static
parameter. Each parameter of a `comptime fn` is static. A module has its number of parameters.
A struct has its number of parameters and its number of fields.
-/
inductive Sig where
  | const
  | fn (static : Array Bool)
  | module (arity : Nat)
  | struct (params fields : Nat)
  | alias

def sig : Resolve.Item → Sig
  | .const .. => .const
  | .fn _ c _ ps _ _ => .fn (ps.map (c || ·.comptime)).toArray
  | .module _ _ ps _ _ => .module ps.length
  | .struct _ _ ps fs => .struct ps.length fs.length
  | .alias .. => .alias

/-! The item of a statement, for `S006`. -/
inductive Owner where
  | module | fn | comptimeFn
  deriving DecidableEq, BEq

/-!
The state of the walk. `resources` maps the local number of each resource of the current item to
its kind. `err` holds the first error by position.
-/
structure St where
  resources : Array (Option Resource)
  err : Option Error

/-! The context of the walk is the signature of each item. -/
abbrev M := ReaderT (Array Sig) (StateM St)

def report (code : ErrorCode) (pos : Pos) (msg : String) : M Unit :=
  modify fun s => { s with err := earlier s.err ⟨code, pos, msg⟩ }

/-! Records the kind of the resource `b`. Local numbers are dense, so the array stays small. -/
def declare (b : Binder) (r : Resource) : M Unit :=
  modify fun s =>
    let a := s.resources
    let a := if a.size ≤ b.id then a ++ Array.replicate (b.id + 1 - a.size) none else a
    { s with resources := a.set! b.id (some r) }

/-! `S007` at `pos` if `what` has `got` arguments, not `want`. -/
def arity (pos : Pos) (what : String) (want got : Nat) : M Unit :=
  if want == got then pure ()
  else report .S007 pos s!"{what} takes {want} argument(s), but it has {got}"

def typeArity : PrimType → Nat
  | .uint | .sint => 1
  | .bool | .nat | .int | .unit | .type => 0

def fnArity : PrimFn → Nat
  | .resize | .reinterpret | .staticAssert => 2
  | .error | .len | .dataBits => 1

/-! True for each static argument of a prelude function, by its index. -/
def fnStatic : PrimFn → Nat → Bool
  | .resize, k | .reinterpret, k => k == 0
  | .staticAssert, _ | .error, _ => true
  | .len, _ | .dataBits, _ => false

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
      if let some (some r) := (← get).resources[id]? then
        report .S005 pos s!"`{n}` is {r.text}; a static position needs a static value"
  | _ => pure ()

/-!
The arity of a call at `pos` with the callee `f` and `got` arguments. `h` is the type head of a
type callee. The result tells which arguments are static positions, by index.
-/
def call (pos : Pos) (f : Resolve.Expr) (h : Option Head) (got : Nat) : M (Nat → Bool) := do
  match h, f with
  | some h, _ =>
    match h.ctor with
    | .convert =>
      if got > 1 then
        report .S007 pos s!"a constructor takes 0 or 1 argument(s), but it has {got}"
      return fun _ => true
    | .record k =>
      unless got == 0 || got == k do
        report .S007 pos s!"a struct constructor takes 0 or {k} argument(s), but it has {got}"
      return fun _ => false
    | .unknown => return fun _ => false
  | none, .name _ g (.item i) =>
    match (← read)[i]? with
    | some (.fn ps) =>
      arity pos s!"`{g}`" ps.size got
      return fun k => ps.getD k false
    | _ => return fun _ => false
  | none, .name _ g (.fn h) =>
    arity pos s!"`{g}`" (fnArity h) got
    return fnStatic h
  | none, _ => return fun _ => false

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
    | .call p f xs => do
      let h ← visit true false f
      let st ← call p f h xs.length
      let mut k := 0
      for x in xs do
        let _ ← visit (static || st k) false x
        k := k + 1
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

  def typeExpr : Resolve.TypeExpr → M Unit
    | .name p n r => do
      if let some h ← head n r then arity p h.text h.missing 0
    | .index p (.name _ n r) xs => do
      if let some h ← head n r then arity p h.text h.missing xs.length
      for x in xs do let _ ← visit true false x
    | .index p b xs => do
      arity p "a complete type" 0 xs.length
      typeExpr b
      for x in xs do let _ ← visit true false x
    | .unit _ => pure ()
    | .tuple _ ts => for t in ts do typeExpr t
    | .array _ t n => do typeExpr t; let _ ← visit true false n
end

def expr (static : Bool) (e : Resolve.Expr) : M Unit := do let _ ← visit static false e

/-! `S006` at `pos` if a `comptime fn` has the statement `what`. -/
def placement (o : Owner) (pos : Pos) (what : String) : M Unit :=
  if o == .comptimeFn then report .S006 pos s!"a `comptime fn` has no {what}" else pure ()

mutual
  def stmt (o : Owner) : Resolve.Stmt → M Unit
    | .local _ _ _ ty v => do
      if let some ty := ty then typeExpr ty
      expr false v
    | .assign _ t v => do expr false t; expr false v
    | .connect p t v => do
      placement o p "`:=`"
      expr false t
      expr false v
    | .reg p b ty i => do
      placement o p "register"
      typeExpr ty
      expr true i
      declare b .reg
    | .wire p b ty => do placement o p "wire"; typeExpr ty; declare b .wire
    | .input p b ty => do placement o p "port"; typeExpr ty; declare b .port
    | .output p b ty => do placement o p "port"; typeExpr ty; declare b .port
    | .inst p b m i xs => do
      placement o p "instance"
      if let some (.module k) := (← read)[i]? then arity p s!"`{m.name}`" k xs.length
      for x in xs do expr true x
      declare b .inst
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
    for p in ps do typeExpr p.ty
    typeExpr r
    stmts (if c then .comptimeFn else .fn) b
  | .module _ _ ps _ b => do
    for p in ps do typeExpr p.ty
    stmts .module b
  | .struct _ _ ps fs => do
    for p in ps do typeExpr p.ty
    for f in fs do typeExpr f.ty
  | .alias _ _ ty => typeExpr ty

/-! The resolved items, or the first error of pass 4 by position. It runs after `resolve`. -/
def check (items : Array Resolve.Item) : Except Error (Array Resolve.Item) :=
  let walk : M Unit := items.forM fun it => do
    modify fun s => { s with resources := #[] }
    item it
  let ((), s) := (walk.run (items.map sig)).run ⟨#[], none⟩
  match s.err with
  | some e => .error e
  | none => .ok items

/-! A static expression in the file scope, such as the `EXPR` of `eval`, or its first error. -/
def checkExpr (items : Array Resolve.Item) (e : Resolve.Expr) : Except Error Unit :=
  let ((), s) := ((expr true e).run (items.map sig)).run ⟨#[], none⟩
  match s.err with
  | some e => .error e
  | none => .ok ()

end Silicon.Source.Check
