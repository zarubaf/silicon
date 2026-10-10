import Std.Data.TreeMap
import Silicon.Source.Syntax

/-!
The resolver of slice 1. It reads the AST of `Source.Parse`. It gives the resolved AST, in which
each name points to its declaration. Else it gives the first `S002` or the first `S003`.

The scopes follow v0.1 section 2, with the change of the front-end spec: the language reserves
no name. These rules settle the open points:

- The prelude is the outermost scope. The item scope is inside it. A local scope is inside the
  item scope. Thus a declaration can shadow a prelude name, and a local can shadow an item.
- The item scope holds each `const`, `fn`, and `module`. An item is visible in the full file,
  also before its declaration.
- The parameters of a function or a module are in its outer local scope. The domain names of a
  module and the top-level statements of its body are in the same scope. Thus a `let` with the
  name of a parameter is `S002`.
- A parameter is visible in the types of the later parameters, in the return type, and in the
  body. It is not visible in its own type.
- A block, each branch of a `comptime if`, and a `comptime for` make a new local scope. The loop
  variable and the top-level statements of the loop body are in the same scope.
- A local is visible after its full declaration statement. Its type and its value see only the
  earlier declarations. Thus `let x = x;` reads an outer `x`.
- A name in a nested scope can shadow a name of an outer scope. Two declarations of one name in
  one scope are `S002`.
- A module without a `domains` clause has the default domain `clock` (section 7.5). The resolver
  declares it before the parameters, because it has no token. Its position is the start of the
  module. Thus a parameter `clock` is `S002` at the parameter. `domains()` declares no domain.

The resolver does not look up the name after a `.`. The selection of a field or a port is a
later check.

A position that needs a fixed kind gets a name of that kind, else `S003`:

- A type name is a prelude type. Slice 1 has no type item.
- The module of an `instance` is a `module` item.
- A name in an expression is not a module. A module is used only in an `instance`.

`S002` is at the name of the second declaration. `S003` is at the name. The resolver reports the
first `S002` by position. Without an `S002`, it reports the first `S003` by position.

The walk is a single pass in source order. It continues after an error, so it finds the first
error of each code. Its recursion follows the blocks and the expressions. The syntax depth thus
bounds it at about 2N. A loop handles each list. A scope is a persistent tree map from a name to
its declaration, so each lookup takes logarithmic time.
-/
namespace Silicon.Source.Resolve

/-! The prelude types of slice 1. -/
inductive PrimType where
  | bool | uint | sint | nat | int
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The prelude functions of slice 1. -/
inductive PrimFn where
  | resize | reinterpret | staticAssert | error
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The declaration of a name. An `item` holds the index of the item in the file. A `local` holds
the number of the local declaration in its item. The numbers start at 0 in each item, in source
order: the implicit `clock`, the parameters, the domain names, and then the statements.
-/
inductive Ref where
  | type (t : PrimType)
  | fn (f : PrimFn)
  | item (index : Nat)
  | local (id : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The prelude of slice 1. It holds only the names of slice 1: the scalar types of section 12.1 and
the functions `resize`, `reinterpret`, `static_assert`, and `error`. `true` and `false` are
keywords, and `T(n)` is syntax, so they need no name.
-/
def prelude : List (String × Ref) :=
  [("Bool", .type .bool), ("UInt", .type .uint), ("SInt", .type .sint), ("Nat", .type .nat),
   ("Int", .type .int), ("resize", .fn .resize), ("reinterpret", .fn .reinterpret),
   ("static_assert", .fn .staticAssert), ("error", .fn .error)]

/-!
The prelude names of later slices, with their slice. A use of one is `S003`, and the message
names the slice.
-/
def laterPrelude : List (String × Nat) :=
  [("String", 2), ("Type", 2), ("Unit", 2), ("List", 2), ("list", 2), ("push", 2), ("pop", 2),
   ("len", 2), ("str", 2), ("data_bits", 2), ("diagnostic", 2),
   ("Reg", 3), ("Wire", 3), ("Mem", 3), ("Input", 3), ("Instance", 3), ("Domain", 3),
   ("read", 3), ("FieldInfo", 4), ("TypeInfo", 4), ("PortKey", 4), ("PortInfo", 4)]

/-! A declared name and its local number. -/
structure Binder where
  name : Ident
  id : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The resolved expression. It is the expression of `Source.Syntax` with a `Ref` at each name. -/
inductive Expr where
  | num (pos : Pos) (value : Nat)
  | bool (pos : Pos) (value : Bool)
  | str (pos : Pos) (value : String)
  | name (pos : Pos) (name : String) (ref : Ref)
  | unary (pos : Pos) (op : UnOp) (arg : Expr)
  | binary (pos : Pos) (op : BinOp) (lhs rhs : Expr)
  | cond (pos : Pos) (cond yes no : Expr)
  | call (pos : Pos) (callee : Expr) (args : List Expr)
  | index (pos : Pos) (base : Expr) (args : List Expr)
  | field (pos : Pos) (base : Expr) (field : Ident)
  deriving Repr, BEq, Inhabited

/-! The resolved type expression. A type name is a prelude type. -/
inductive TypeExpr where
  | name (pos : Pos) (name : String) (type : PrimType)
  | index (pos : Pos) (base : TypeExpr) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-! The resolved statement. Each declaration has a `Binder`. An `inst` has its module item. -/
inductive Stmt where
  | local (pos : Pos) (mutable : Bool) (name : Binder) (ty : Option TypeExpr) (value : Expr)
  | assign (pos : Pos) (target value : Expr)
  | connect (pos : Pos) (target value : Expr)
  | reg (pos : Pos) (name : Binder) (ty : TypeExpr) (init : Expr)
  | wire (pos : Pos) (name : Binder) (ty : TypeExpr)
  | input (pos : Pos) (name : Binder) (ty : TypeExpr)
  | output (pos : Pos) (name : Binder) (ty : TypeExpr)
  | inst (pos : Pos) (name : Binder) (module : Ident) (item : Nat) (args : List Expr)
  | ret (pos : Pos) (value : Option Expr)
  | ctIf (pos : Pos) (cond : Expr) (yes : List Stmt) (no : Option (List Stmt))
  | ctFor (pos : Pos) (var : Binder) (lo hi : Expr) (body : List Stmt)
  | block (pos : Pos) (body : List Stmt)
  | expr (pos : Pos) (value : Expr)
  deriving Repr, BEq, Inhabited

structure Param where
  pos : Pos
  comptime : Bool
  name : Binder
  ty : TypeExpr
  deriving Repr, BEq, Inhabited

/-!
The resolved item. A `Ref.item` holds the index of an item in the resolved file. The `domains`
of a module without a clause hold the one default domain `clock`.
-/
inductive Item where
  | const (pos : Pos) (name : Ident) (ty : TypeExpr) (value : Expr)
  | fn (pos : Pos) (comptime : Bool) (name : Ident) (params : List Param) (ret : TypeExpr)
      (body : List Stmt)
  | module (pos : Pos) (name : Ident) (params : List Param) (domains : List Binder)
      (body : List Stmt)
  deriving Repr, BEq, Inhabited

/-! Position order: the lower line, then the lower column. -/
def before (a b : Pos) : Bool := a.line < b.line || (a.line == b.line && a.col < b.col)

/-! The earlier of two errors by position. -/
def earlier (old : Option Error) (e : Error) : Option Error :=
  match old with
  | some o => if before e.pos o.pos then some e else some o
  | none => some e

/-! A visible declaration and the number of its scope. The item scope has the number 0. -/
structure Binding where
  ref : Ref
  scope : Nat

/-!
The state of the walk. `env` maps each visible name to its innermost declaration. `scope` is the
number of the current scope, and `scopes` the next free scope number. `locals` is the next local
number of the current item. `dup` and `unknown` hold the first `S002` and the first `S003`.
-/
structure St where
  env : Std.TreeMap String Binding compare
  scope : Nat
  scopes : Nat
  locals : Nat
  dup : Option Error
  unknown : Option Error

/-! The context of the walk is the parsed items, for the kind of an item. -/
abbrev M := ReaderT (Array Source.Item) (StateM St)

def recordDup (e : Error) : M Unit := modify fun s => { s with dup := earlier s.dup e }

def recordUnknown (e : Error) : M Unit :=
  modify fun s => { s with unknown := earlier s.unknown e }

/-! Adds `n` to the current scope with `ref`. A name of the same scope is `S002`. -/
def bind (n : Ident) (ref : Ref) : M Unit := do
  let s ← get
  if let some b := s.env.get? n.name then
    if b.scope == s.scope then
      recordDup ⟨.S002, n.pos, s!"`{n.name}` is already declared in this scope"⟩
  modify fun t => { t with env := t.env.insert n.name ⟨ref, t.scope⟩ }

/-! Declares the local `n` with the next local number. -/
def declare (n : Ident) : M Binder := do
  let id := (← get).locals
  modify fun s => { s with locals := id + 1 }
  bind n (.local id)
  return ⟨n, id⟩

/-! Runs `act` in a new scope. The declarations of `act` are not visible after it. -/
def inScope (act : M α) : M α := do
  let s ← get
  set { s with scope := s.scopes, scopes := s.scopes + 1 }
  let r ← act
  modify fun t => { t with env := s.env, scope := s.scope }
  return r

/-!
The declaration of the name `n` at `pos`, or `S003`. After an error, the walk continues with a
placeholder, and `resolve` discards its result.
-/
def lookup (pos : Pos) (n : String) : M (Option Ref) := do
  match (← get).env.get? n with
  | some b => return some b.ref
  | none =>
    match prelude.lookup n with
    | some r => return some r
    | none =>
      let msg := match laterPrelude.lookup n with
        | some k => s!"`{n}` is not in slice 1; it comes in slice {k}"
        | none => s!"`{n}` is not declared"
      recordUnknown ⟨.S003, pos, msg⟩
      return none

def isModule (i : Nat) : M Bool := return (← read)[i]? matches some (.module ..)

def wrongKind (pos : Pos) (n what : String) : M Unit :=
  recordUnknown ⟨.S003, pos, s!"`{n}` is not {what}"⟩

def expr : Source.Expr → M Expr
  | .num p v => return .num p v
  | .bool p v => return .bool p v
  | .str p v => return .str p v
  | .name p n => do
    let r ← lookup p n
    if let some (.item i) := r then
      if ← isModule i then wrongKind p n "a value; a module is used only in an `instance`"
    return .name p n (r.getD default)
  | .unary p op a => return .unary p op (← expr a)
  | .binary p op l r => return .binary p op (← expr l) (← expr r)
  | .cond p c y n => return .cond p (← expr c) (← expr y) (← expr n)
  | .call p f xs => return .call p (← expr f) (← xs.mapM expr)
  | .index p b xs => return .index p (← expr b) (← xs.mapM expr)
  | .field p b f => return .field p (← expr b) f

def typeExpr : Source.TypeExpr → M TypeExpr
  | .name p n => do
    match ← lookup p n with
    | some (.type t) => return .name p n t
    | some _ => wrongKind p n "a type"; return .name p n default
    | none => return .name p n default
  | .index p b xs => return .index p (← typeExpr b) (← xs.mapM expr)

/-! The module item of an `instance`. -/
def moduleRef (m : Ident) : M Nat := do
  match ← lookup m.pos m.name with
  | some (.item i) => if ← isModule i then return i
  | some _ => pure ()
  | none => return 0
  wrongKind m.pos m.name "a module"
  return 0

mutual
  def stmt : Source.Stmt → M Stmt
    | .local p m n ty v => do
      let ty ← ty.mapM typeExpr
      let v ← expr v
      return .local p m (← declare n) ty v
    | .assign p t v => return .assign p (← expr t) (← expr v)
    | .connect p t v => return .connect p (← expr t) (← expr v)
    | .reg p n ty i => do
      let ty ← typeExpr ty
      let i ← expr i
      return .reg p (← declare n) ty i
    | .wire p n ty => do let ty ← typeExpr ty; return .wire p (← declare n) ty
    | .input p n ty => do let ty ← typeExpr ty; return .input p (← declare n) ty
    | .output p n ty => do let ty ← typeExpr ty; return .output p (← declare n) ty
    | .inst p n m xs => do
      let i ← moduleRef m
      let xs ← xs.mapM expr
      return .inst p (← declare n) m i xs
    | .ret p v => return .ret p (← v.mapM expr)
    | .ctIf p c y n => do
      let c ← expr c
      let y ← inScope (stmts y)
      let n ← match n with
        | some n => some <$> inScope (stmts n)
        | none => pure none
      return .ctIf p c y n
    | .ctFor p i lo hi b => do
      let lo ← expr lo
      let hi ← expr hi
      inScope do
        let i ← declare i
        return .ctFor p i lo hi (← stmts b)
    | .block p b => return .block p (← inScope (stmts b))
    | .expr p v => return .expr p (← expr v)

  /-- The statements of one scope, in a loop. -/
  def stmts (ss : List Source.Stmt) : M (List Stmt) := ss.mapM stmt
end

def param (p : Source.Param) : M Param := do
  let ty ← typeExpr p.ty
  return ⟨p.pos, p.comptime, ← declare p.name, ty⟩

/-! The parameters, the domain names, and the body of an item share one new scope. -/
def body (act : M α) : M α := do
  modify fun s => { s with locals := 0 }
  inScope act

def item : Source.Item → M Item
  | .const p n ty v => return .const p n (← typeExpr ty) (← expr v)
  | .fn p c n ps r b => body do
    let ps ← ps.mapM param
    let r ← typeExpr r
    return .fn p c n ps r (← stmts b)
  | .module p n ps ds b => body do
    -- The implicit `clock` has no token, so it comes before the parameters.
    let clock ← if ds.isNone then some <$> declare ⟨p, "clock"⟩ else pure none
    let ps ← ps.mapM param
    let ds ← match clock with
      | some c => pure [c]
      | none => (ds.getD []).mapM declare
    return .module p n ps ds (← stmts b)

def itemName : Source.Item → Ident
  | .const _ n .. | .fn _ _ n .. | .module _ n .. => n

/-!
The resolved items of a file, or the first error. The index of an item in the result is its
index in `items`.
-/
def resolve (items : List Source.Item) : Except Error (Array Item) :=
  let walk : M (Array Item) := do
    for (it, i) in items.zipIdx do
      bind (itemName it) (.item i)
    modify fun s => { s with scopes := 1 }
    items.toArray.mapM item
  let (out, s) := (walk.run items.toArray).run ⟨{}, 0, 0, 0, none, none⟩
  match s.dup, s.unknown with
  | some e, _ => .error e
  | none, some e => .error e
  | none, none => .ok out

end Silicon.Source.Resolve
