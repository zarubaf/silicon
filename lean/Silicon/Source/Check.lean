import Silicon.Source.Resolve

/-!
The generic pre-check of slice 1: pass 4 of the front end. It reads the resolved AST of
`Source.Resolve`. It gives the same AST, or the first error of `S005` to `S007` by position.

These checks need no static values. Widths, types, and the dynamic stage rule are for `Elab`.
The check runs on each item, also on an item that no instantiation uses. It checks both
branches of each `comptime if`.

`S005`: a static position does not name a port, a register, a wire, or an instance. Slice 1 has
no memory. The rule is syntactic. It looks only at names that resolve to the declaration of such
a resource. A `let` alias of a resource and a domain name are for the stage rule `S011` of
`Elab`. The error is at the name. These are the static positions of slice 1:

1. Each argument of an index: `T[e]` in a type and `b[e]` in an expression.
2. The value of a `const` item.
3. The condition of a `comptime if`, and both bounds of a `comptime for`.
4. Each argument of an `instance`.
5. The reset value of a `reg`.
6. The callee of each call.
7. Each argument of a call to a `comptime fn` item, and each argument at a `comptime` parameter
   of a call to a `fn` item.
8. The first argument of `resize` and `reinterpret`, and each argument of `static_assert` and
   `error`.
9. The argument of a constructor `T(n)`: a call whose callee is a prelude type, or an index of
   one.
10. Each part of an expression in a static position. A static expression is thus built only of
   static parts, also in a branch that a static condition does not select.

`S006` is at the statement:

- A module body has no `return`, also in a nested block.
- A `comptime fn` has no `input`, `output`, `reg`, `wire`, `instance`, or `:=` statement.

`S007` is at the call, the index, the type name, or the `instance` statement:

- A call to a `fn` item has one argument for each parameter.
- `resize`, `reinterpret`, and `static_assert` have two arguments, and `error` has one.
- A constructor `T(n)` has one argument. Slice 1 has no `T()`.
- An `instance` has one argument for each parameter of its module.
- `UInt` and `SInt` have one index argument. `Bool`, `Nat`, and `Int` have none. This also holds
  for a type name in an expression. A complete type such as `UInt[8]` takes no more index.

A call through a local or a `const` has no known arity. `Elab` checks it with `S010`.

`S008` cannot occur in slice 1, so this check has no code for it. The parser rejects a `mut`
formal with `S004`, so no `mut` actual exists. A place is `x` or `x.f`, so it has no index
expression. No expression mutates a root: an assignment is a statement, and slice 1 has no
`push`, no `pop`, and no receiver call. Thus no window of section 9.1 holds a mutation.

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
-/
inductive Sig where
  | const
  | fn (static : Array Bool)
  | module (arity : Nat)

def sig : Resolve.Item → Sig
  | .const .. => .const
  | .fn _ c _ ps _ _ => .fn (ps.map (c || ·.comptime)).toArray
  | .module _ _ ps _ _ => .module ps.length

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
  | .bool | .nat | .int => 0

def fnArity : PrimFn → Nat
  | .resize | .reinterpret | .staticAssert => 2
  | .error => 1

/-! True for each static argument of a prelude function, by its index. -/
def fnStatic : PrimFn → Nat → Bool
  | .resize, k | .reinterpret, k => k == 0
  | .staticAssert, _ | .error, _ => true

/-!
The name and the number of missing index arguments of a type in an expression: `T` or an index
of it. A complete type misses none. Another expression is not a type.
-/
def typeHead : Resolve.Expr → Option (String × Nat)
  | .name _ n (.type t) => some (s!"`{n}`", typeArity t)
  | .index _ b _ => (typeHead b).map fun _ => ("a complete type", 0)
  | _ => none

/-! The same for a type expression. -/
def typeHeadOf : Resolve.TypeExpr → String × Nat
  | .name _ n t => (s!"`{n}`", typeArity t)
  | .index .. => ("a complete type", 0)

/-! A name. A type name has no index here. A resource in a static position is `S005`. -/
def name (static : Bool) (pos : Pos) (n : String) : Ref → M Unit
  | .type t => arity pos s!"`{n}`" (typeArity t) 0
  | .local id => do
    if static then
      if let some (some r) := (← get).resources[id]? then
        report .S005 pos s!"`{n}` is {r.text}; a static position needs a static value"
  | _ => pure ()

/-!
The arity of a call at `pos` with the callee `f` and `got` arguments. The result tells which
arguments are static positions, by index.
-/
def call (pos : Pos) (f : Resolve.Expr) (got : Nat) : M (Nat → Bool) := do
  match f with
  | .name _ g (.item i) =>
    match (← read)[i]? with
    | some (.fn ps) =>
      arity pos s!"`{g}`" ps.size got
      return fun k => ps.getD k false
    | _ => return fun _ => false
  | .name _ g (.fn h) =>
    arity pos s!"`{g}`" (fnArity h) got
    return fnStatic h
  | _ =>
    if (typeHead f).isSome then
      arity pos "a constructor" 1 got
      return fun _ => true
    return fun _ => false

/-! An expression. `static` is true in a static position. -/
def expr (static : Bool) : Resolve.Expr → M Unit
  | .num .. | .bool .. | .str .. => pure ()
  | .name p n r => name static p n r
  | .unary _ _ a => expr static a
  | .binary _ _ l r => do expr static l; expr static r
  | .cond _ c y n => do expr static c; expr static y; expr static n
  | .call p f xs => do
    expr true f
    let st ← call p f xs.length
    let mut k := 0
    for x in xs do
      expr (static || st k) x
      k := k + 1
  | .index p b xs => do
    if let some (n, k) := typeHead b then arity p n k xs.length
    -- The base type name of an index has its arguments, so it skips the check of a bare name.
    unless b matches .name _ _ (.type _) do expr static b
    for x in xs do expr true x
  | .field _ b _ => expr static b

def typeExpr : Resolve.TypeExpr → M Unit
  | .name p n t => arity p s!"`{n}`" (typeArity t) 0
  | .index p b xs => do
    let (n, k) := typeHeadOf b
    arity p n k xs.length
    if b matches .index .. then typeExpr b
    for x in xs do expr true x

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

/-! The resolved items, or the first error of pass 4 by position. It runs after `resolve`. -/
def check (items : Array Resolve.Item) : Except Error (Array Resolve.Item) :=
  let walk : M Unit := items.forM fun it => do
    modify fun s => { s with resources := #[] }
    item it
  let ((), s) := (walk.run (items.map sig)).run ⟨#[], none⟩
  match s.err with
  | some e => .error e
  | none => .ok items

end Silicon.Source.Check
