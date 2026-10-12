-- SPDX-License-Identifier: Apache-2.0
import Std.Data.TreeMap
import Silicon.Source.Syntax

/-!
The resolver of slice 1 and of the containers and the types of slice 2. It reads the AST of
`Source.Parse`. It gives the resolved AST, in which each name points to its declaration. Else it
gives the first `S002` or the first `S003`.

The scopes follow v0.1 section 2, with the change of the front-end spec: the language reserves
no name. These rules settle the open points:

- The prelude is the outermost scope. The item scope is inside it. A local scope is inside the
  item scope. Thus a declaration can shadow a prelude name, and a local can shadow an item.
- The item scope holds each `const`, `fn`, `module`, `struct`, and `type` item. An item is
  visible in the full file, also before its declaration.
- The parameters of a function or a module are in its outer local scope. The domain names of a
  module and the top-level statements of its body are in the same scope. Thus a `let` with the
  name of a parameter is `S002`.
- The parameters of a struct are in a new scope. Its field types are in this scope too.
- A parameter is visible in the types of the later parameters, in the return type, in the body,
  and in the field types. It is not visible in its own type.
- A block, each branch of a `comptime if`, and a `comptime for` make a new local scope. The loop
  variable and the top-level statements of the loop body are in the same scope.
- A local is visible after its full declaration statement. Its type and its value see only the
  earlier declarations. Thus `let x = x;` reads an outer `x`. A `type` statement declares a
  local in the same way.
- A name in a nested scope can shadow a name of an outer scope. Two declarations of one name in
  one scope are `S002`.
- A module without a `domains` clause has the default domain `clock` (section 7.5). The resolver
  declares it before the parameters, because it has no token. Its position is the start of the
  module. Thus a parameter `clock` is `S002` at the parameter. `domains()` declares no domain.

The resolver does not look up the name after a `.`. The selection of a field or a port is a
later check. A selector `.N` holds a number, so it has no name. The container forms of slice 2,
`()`, tuples, arrays, and the selector, have no declaration. The walk resolves their parts.

The name `m` of a receiver call `x.m(args)` resolves in the item scope, then in the prelude.
It never resolves to a local (section 5.6 of the front-end spec). It names a function, else
`S003` at `m`. A parameter keeps its mode: none, `comptime`, or `mut`.

Each call node and each receiver-call node gets a call site `k`. The sites of an item body count
from 0 in pre-order (section 7.3). A call node comes before its callee, its receiver, and its
arguments. The walk visits the children in source order. A call outside a body also gets a
site, but it runs on static values only, so its site never names hardware.

A position that needs a fixed kind gets a name of that kind, else `S003`:

- A type name is a prelude type, a `struct` item, a `type` item, or a local. Only `Elab` knows
  whether a local holds a type.
- The module of an `instance` is a `module` item.
- A name in an expression is not a module. A module is used only in an `instance`.

The field names of a struct are not in a scope. Two fields with one name are `S002`.

`S002` is at the name of the second declaration or field. `S003` is at the name. The resolver
reports the first `S002` by position. Without an `S002`, it reports the first `S003` by position.

The walk is a single pass in source order. It continues after an error, so it finds the first
error of each code. Its recursion follows the blocks and the expressions. The syntax depth thus
bounds it at about 2N. A loop handles each list. A scope is a persistent tree map from a name to
its declaration, so each lookup takes logarithmic time.
-/
namespace Silicon.Source.Resolve

/-! The prelude types of slice 1, and `Unit`, `Type`, `String`, and `List` of slice 2. -/
inductive PrimType where
  | bool | uint | sint | nat | int | unit | type | string | list
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The prelude functions of slice 1, and `len`, `data_bits`, `list`, `push`, `pop`, and `str` of
slice 2.
-/
inductive PrimFn where
  | resize | reinterpret | staticAssert | error | len | dataBits | list | push | pop | str
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
The prelude. It holds the scalar types of section 12.1 and the functions `resize`,
`reinterpret`, `static_assert`, and `error` of slice 1. It also holds `Unit` and `len`, the
names of the containers of slice 2, and `Type` and `data_bits`, the names of the types as values.
The names of the strings and the lists are `String`, `List`, `list`, `push`, `pop`, and `str`.
`true` and `false` are keywords, and `T(n)` is syntax, so they need no name.
-/
def prelude : List (String × Ref) :=
  [("Bool", .type .bool), ("UInt", .type .uint), ("SInt", .type .sint), ("Nat", .type .nat),
   ("Int", .type .int), ("Unit", .type .unit), ("Type", .type .type), ("resize", .fn .resize),
   ("reinterpret", .fn .reinterpret), ("static_assert", .fn .staticAssert),
   ("error", .fn .error), ("len", .fn .len), ("data_bits", .fn .dataBits),
   ("String", .type .string), ("List", .type .list), ("list", .fn .list), ("push", .fn .push),
   ("pop", .fn .pop), ("str", .fn .str)]

/-!
The prelude names of later slices, with their slice. A use of one is `S003`, and the message
names the slice.
-/
def laterPrelude : List (String × Nat) :=
  [("diagnostic", 2),
   ("Reg", 3), ("Wire", 3), ("Mem", 3), ("Input", 3), ("Instance", 3), ("Domain", 3),
   ("read", 3), ("FieldInfo", 4), ("TypeInfo", 4), ("PortKey", 4), ("PortInfo", 4)]

/-! A declared name and its local number. -/
structure Binder where
  name : Ident
  id : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The resolved expression and type expression. They are those of `Source.Syntax` with a `Ref` at
each name, so they are mutually recursive too. The container forms keep the shape of the parsed
forms. A `call` and a `method` hold their call site. The `fn` of a `method` is a `fn` item or a
prelude function. A type name refers to a prelude type, a `struct` item, a `type` item, or a
local. A local holds a value of type `Type`, which `Elab` checks.
-/
mutual
  inductive Expr where
    | num (pos : Pos) (value : Nat)
    | bool (pos : Pos) (value : Bool)
    | str (pos : Pos) (value : String)
    | name (pos : Pos) (name : String) (ref : Ref)
    | unary (pos : Pos) (op : UnOp) (arg : Expr)
    | binary (pos : Pos) (op : BinOp) (lhs rhs : Expr)
    | cond (pos : Pos) (cond yes no : Expr)
    | call (pos : Pos) (callee : Expr) (args : List Expr) (site : Nat)
    | index (pos : Pos) (base : Expr) (args : List Expr)
    | field (pos : Pos) (base : Expr) (field : Ident)
    | unit (pos : Pos)
    | tuple (pos : Pos) (elems : List Expr)
    | array (pos : Pos) (elems : List Expr)
    | select (pos : Pos) (base : Expr) (litPos : Pos) (index : Nat)
    | arrayType (pos : Pos) (elem : TypeExpr) (len : Expr)
    | method (pos : Pos) (recv : Expr) (name : Ident) (fn : Ref) (args : List Expr) (site : Nat)

  inductive TypeExpr where
    | name (pos : Pos) (name : String) (ref : Ref)
    | index (pos : Pos) (base : TypeExpr) (args : List Expr)
    | unit (pos : Pos)
    | tuple (pos : Pos) (elems : List TypeExpr)
    | array (pos : Pos) (elem : TypeExpr) (len : Expr)
end

deriving instance Repr, BEq, Inhabited for Expr, TypeExpr

/-!
The resolved statement. Each declaration has a `Binder`. An `inst` has its module item. An
`alias` is a local of type `Type`.
-/
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
  | alias (pos : Pos) (name : Binder) (ty : TypeExpr)
  deriving Repr, BEq, Inhabited

structure Param where
  pos : Pos
  mode : ParamMode
  name : Binder
  ty : TypeExpr
  deriving Repr, BEq, Inhabited

structure StructField where
  name : Ident
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
  | struct (pos : Pos) (name : Ident) (params : List Param) (fields : List StructField)
  | alias (pos : Pos) (name : Ident) (ty : TypeExpr)
  deriving Repr, BEq, Inhabited

/-! The position of the first token of a form. -/
def Expr.pos : Expr → Pos
  | .num p _ | .bool p _ | .str p _ | .name p .. | .unary p .. | .binary p ..
  | .cond p .. | .call p .. | .index p .. | .field p .. | .unit p | .tuple p ..
  | .array p .. | .select p .. | .arrayType p .. | .method p .. => p

def TypeExpr.pos : TypeExpr → Pos
  | .name p .. | .index p .. | .unit p | .tuple p .. | .array p .. => p

def Stmt.pos : Stmt → Pos
  | .local p .. | .assign p .. | .connect p .. | .reg p .. | .wire p .. | .input p ..
  | .output p .. | .inst p .. | .ret p .. | .ctIf p .. | .ctFor p .. | .block p ..
  | .expr p .. | .alias p .. => p

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
number of the current item, and `sites` its next call site. `dup` holds the first `S002`, and
`unknown` the first `S003`.
-/
structure St where
  env : Std.TreeMap String Binding compare
  scope : Nat
  scopes : Nat
  locals : Nat
  sites : Nat
  dup : Option Error
  unknown : Option Error

/-!
The context of the walk holds the parsed items, for the kind of an item. It also holds the item
scope, which maps each item name to its index. A receiver call looks up its name there, past
each local.
-/
structure File where
  items : Array Source.Item
  names : Std.TreeMap String Nat compare

abbrev M := ReaderT File (StateM St)

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

/-! `S003` at `pos` for the name `n` that is neither declared nor in the prelude. -/
def missing (pos : Pos) (n : String) : M Unit :=
  let msg := match laterPrelude.lookup n with
    | some k => s!"`{n}` is not supported yet; it comes in slice {k}"
    | none => s!"`{n}` is not declared"
  recordUnknown ⟨.S003, pos, msg⟩

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
    | none => missing pos n; return none

def isModule (i : Nat) : M Bool := return (← read).items[i]? matches some (.module ..)

def wrongKind (pos : Pos) (n what : String) : M Unit :=
  recordUnknown ⟨.S003, pos, s!"`{n}` is not {what}"⟩

/-!
A name in a type position refers to a type: a prelude type, a `struct` item, a `type` item, or a
local. Only `Elab` knows whether a local holds a type.
-/
def isType : Ref → M Bool
  | .type _ | .local _ => return true
  | .item i => do
    match (← read).items[i]? with
    | some (.struct ..) | some (.alias ..) => return true
    | _ => return false
  | .fn _ => return false

/-! The next call site of the current item body. -/
def site : M Nat := modifyGet fun s => (s.sites, { s with sites := s.sites + 1 })

/-!
The function `m` of a receiver call: a `fn` item of the item scope, else a prelude function. A
local does not hide it. Another name is `S003` at `m`.
-/
def method (m : Ident) : M Ref := do
  let notFn : M Ref := do wrongKind m.pos m.name "a function"; return default
  match (← read).names.get? m.name with
  | some i => if (← read).items[i]? matches some (.fn ..) then return .item i else notFn
  | none =>
    match prelude.lookup m.name with
    | some (.fn f) => return .fn f
    | some _ => notFn
    | none => missing m.pos m.name; return default

mutual
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
    | .call p f xs => do
      let k ← site
      return .call p (← expr f) (← xs.mapM expr) k
    | .index p b xs => return .index p (← expr b) (← xs.mapM expr)
    | .field p b f => return .field p (← expr b) f
    | .unit p => return .unit p
    | .tuple p xs => return .tuple p (← xs.mapM expr)
    | .array p xs => return .array p (← xs.mapM expr)
    | .select p b l k => return .select p (← expr b) l k
    | .arrayType p t n => return .arrayType p (← typeExpr t) (← expr n)
    | .method p r m xs => do
      let k ← site
      let r ← expr r
      let f ← method m
      return .method p r m f (← xs.mapM expr) k

  def typeExpr : Source.TypeExpr → M TypeExpr
    | .name p n => do
      match ← lookup p n with
      | some r =>
        unless ← isType r do wrongKind p n "a type"
        return .name p n r
      | none => return .name p n default
    | .index p b xs => return .index p (← typeExpr b) (← xs.mapM expr)
    | .unit p => return .unit p
    | .tuple p ts => return .tuple p (← ts.mapM typeExpr)
    | .array p t n => return .array p (← typeExpr t) (← expr n)
end

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
    | .alias p n t => do let t ← typeExpr t; return .alias p (← declare n) t

  /-- The statements of one scope, in a loop. -/
  def stmts (ss : List Source.Stmt) : M (List Stmt) := ss.mapM stmt
end

def param (p : Source.Param) : M Param := do
  let ty ← typeExpr p.ty
  return ⟨p.pos, p.mode, ← declare p.name, ty⟩

/-!
The fields of a struct. A field name is not a local, so the fields have their own table of
names. A second field with one name is `S002` at its name.
-/
def fields (fs : List Source.StructField) : M (List StructField) := do
  let mut seen : Std.TreeMap String Unit compare := {}
  let mut out : Array StructField := #[]
  for f in fs do
    if seen.contains f.name.name then
      recordDup ⟨.S002, f.name.pos, s!"the field `{f.name.name}` is already declared"⟩
    seen := seen.insert f.name.name ()
    out := out.push ⟨f.name, ← typeExpr f.ty⟩
  return out.toList

/-! The parameters, the domain names, and the body of an item share one new scope. -/
def body (act : M α) : M α := do
  modify fun s => { s with locals := 0 }
  inScope act

/-! The statements of an item body. Their call sites count from 0. -/
def bodyStmts (ss : List Source.Stmt) : M (List Stmt) := do
  modify fun s => { s with sites := 0 }
  stmts ss

def item : Source.Item → M Item
  | .const p n ty v => return .const p n (← typeExpr ty) (← expr v)
  | .fn p c n ps r b => body do
    let ps ← ps.mapM param
    let r ← typeExpr r
    return .fn p c n ps r (← bodyStmts b)
  | .module p n ps ds b => body do
    -- The implicit `clock` has no token, so it comes before the parameters.
    let clock ← if ds.isNone then some <$> declare ⟨p, "clock"⟩ else pure none
    let ps ← ps.mapM param
    let ds ← match clock with
      | some c => pure [c]
      | none => (ds.getD []).mapM declare
    return .module p n ps ds (← bodyStmts b)
  | .struct p n ps fs => body do
    let ps ← ps.mapM param
    return .struct p n ps (← fields fs)
  | .alias p n t => return .alias p n (← typeExpr t)

def itemName : Source.Item → Ident
  | .const _ n .. | .fn _ _ n .. | .module _ n .. | .struct _ n .. | .alias _ n .. => n

/-! Runs `act` in the item scope of `items`. The result is the first error, if one occurs. -/
def inFile (items : List Source.Item) (act : M α) : Except Error α :=
  let walk : M α := do
    for (it, i) in items.zipIdx do
      bind (itemName it) (.item i)
    modify fun s => { s with scopes := 1 }
    act
  let names := items.zipIdx.foldl (fun m (it, i) => m.insert (itemName it).name i) {}
  let (out, s) := (walk.run ⟨items.toArray, names⟩).run ⟨{}, 0, 0, 0, 0, none, none⟩
  match s.dup, s.unknown with
  | some e, _ => .error e
  | none, some e => .error e
  | none, none => .ok out

/-!
The resolved items of a file, or the first error. The index of an item in the result is its
index in `items`.
-/
def resolve (items : List Source.Item) : Except Error (Array Item) :=
  inFile items (items.toArray.mapM item)

/-! An expression in the file scope, such as the `EXPR` of `eval`, or its first `S003`. -/
def resolveExpr (items : List Source.Item) (e : Source.Expr) : Except Error Expr :=
  inFile items (expr e)

end Silicon.Source.Resolve
