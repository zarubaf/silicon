-- SPDX-License-Identifier: Apache-2.0
import Std.Data.TreeMap
import Silicon.Source.Syntax

/-!
The resolver of slice 1, of the containers and the types of slice 2, and of the enums of slice 3.
It reads the AST of
`Source.Parse`. It gives the resolved AST, in which each name points to its declaration. Else it
gives the first `S002` or the first `S003`.

The scopes follow v0.1 section 2, with the change of the front-end spec: the language reserves
no name. These rules settle the open points:

- The prelude is the outermost scope. The item scope is inside it. A local scope is inside the
  item scope. Thus a declaration can shadow a prelude name, and a local can shadow an item.
- The prelude structs (section 5.6) are struct items after the user items, with the `prelude`
  flag, in the order `ReadResponse`, `FieldInfo`, `TypeInfo`, `VariantInfo`, `PortKey`, and
  `PortInfo` (`preludeStructs`). They are built already resolved, and no field type resolves in
  the item scope. Thus a user `struct Bool`, `type Type`, `struct String`, or `struct FieldInfo`
  does not change them, and the user items keep their indices. A prelude name of one refers to
  it. The walk never visits them, so they add no error.
- The item scope holds each `const`, `fn`, `module`, `struct`, `type`, and `enum` item. An item
  is visible in the full file, also before its declaration.
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

A port family has module scope (F35, section 5.6). Before the statements of a module body, one
pre-order walk (`famStmts`) visits each statement at each block depth. These are a block, both
arms of a `comptime if`, and the body of a `comptime for`. A statement holds no item, so the walk
enters no nested item. The first indexed declaration of a name gives it one family binder in the
scope of the body. This binder is a local number with the reference `Ref.family`. Each indexed
declaration of the name refers to it, and it also binds the name in its own block. Thus a `let`
with that name in that block is `S002`, in each order. These are the other collisions:

- A family and a scalar port of one name, at any depth, are `S002` "Family and scalar port" at
  the later name.
- One family with an input entry and an output entry is `S002` "Family with two directions". It
  is at the name of the first entry of the second direction.
- A family and another name of the body scope is the ordinary `S002`, at the later name.
- A port with an `as` key is no port name of the walk. Its binder is a name of the body only, so
  a family with the name of its binder is the ordinary `S002`.

The walk also runs on the body of each `fn` without `comptime`. Thus a family of a helper has the
scope of the helper body, and its entries are ports of the owner (section 5.6). The module body
cannot select a family that only a helper declares. There, the name has no declaration, so it is
`S003`. In a `comptime fn`, an indexed port declares a local at its statement, and `Check`
reports it (`S006`).

The resolver does not look up the name after a `.`. The selection of a field or a port is a
later check. A selector `.N` holds a number, so it has no name. The container forms of slice 2,
`()`, tuples, arrays, and the selector, have no declaration. The walk resolves their parts.

The name `m` of a receiver call `x.m(args)` resolves in the item scope, then in the prelude.
It never resolves to a local (section 5.6 of the front-end spec). It names a function, else
`S003` at `m`. A parameter keeps its mode: none, `comptime`, or `mut`. The receiver binds to the
first parameter of `m` without a written `comptime` mark. The node holds the index of that
parameter, or none, which `Check` reports as `S007`.

Each call node and each receiver-call node gets a call site `k`. The sites of an item body count
from 0 in pre-order (section 7.3). A call node comes before its callee, its receiver, and its
arguments. The walk visits the children in source order. A call outside a body also gets a
site, but it runs on static values only, so its site never names hardware.

A position that needs a fixed kind gets a name of that kind, else `S003`:

- A type name is a prelude type, a `struct` item, a `type` item, an `enum` item, or a local.
  Only `Elab` knows whether a local holds a type.
- The module of an `instance` is a `module` item.
- The first argument `M` of the prelude `Instance[M, args]` resolves by the ordinary scoping to a
  `module` item, as the first part of a variant path does. Another first argument is `S003` at
  its start, with the text of section 6.2.
- A name in an expression is not a module. Only an `instance` and `Instance` use a module.
- `Domain` is `S003` until more domains come (#11). A user item or a local can shadow each prelude
  name, also `read`.

A function item is a name in an expression too: a callee, or a function value in another
position. Whether it is a value of the right kind, not generic and not a builtin, is the type
rule `S010` of `Elab` (section 5.1). `generic` tells from the resolved signature whether a
function is generic, with no evaluation. The types of a function type resolve as type
expressions.

The field names of a struct are not in a scope. Two fields with one name are `S002`. The variant
names of an enum are not in a scope either. Two variants with one name are `S002`.

Section 5.6 gives the rules of a variant path `X::Y`:

- The first part `X` resolves by the ordinary scoping of a name. Thus a local or a parameter `X`
  shadows an enum item `X`.
- When `X` is an enum item, `Y` names one of its variants, else `S003` at `Y`.
- Else the path is `S003` at its start. This holds also for a `type` alias of an enum and for a
  name with no declaration.

A path and a call of a path are one `variant` node. It holds the enum item, the index of the
variant, the payload values, and whether a call holds it. A call of a path still takes a call
site, so each call node keeps its own site.

A `match` resolves its scrutinee, then each arm in source order. The path of a variant pattern
resolves as a variant path in an expression. The binders of a pattern are locals in a new scope,
which holds only the value of their arm. Thus a binder shadows an outer name, and two binders
with one name in one pattern are `S002` at the second binder. A binder `_` declares no name.

`S002` is at the name of the second declaration or field. `S003` is at the name. The resolver
reports the first `S002` by position. Without an `S002`, it reports the first `S003` by position.

The walk is a single pass in source order. It continues after an error, so it finds the first
error of each code. Its recursion follows the blocks and the expressions. The syntax depth thus
bounds it at about 2N. A loop handles each list. A scope is a persistent tree map from a name to
its declaration, so each lookup takes logarithmic time.
-/
namespace Silicon.Source.Resolve

/-!
The prelude types of slice 1, `Unit`, `Type`, `String`, and `List` of slice 2, and the handle
type families `Reg`, `Wire`, `Input`, `Mem`, and `Instance` of slice 3.
-/
inductive PrimType where
  | bool | uint | sint | nat | int | unit | type | string | list
  | reg | wire | input | mem | «instance»
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The prelude functions of slice 1, and `len`, `data_bits`, `list`, `push`, `pop`, `str`,
`read_port`, `write_port`, and `diagnostic` of slice 2, and `read` of slice 3.
-/
inductive PrimFn where
  | resize | reinterpret | staticAssert | error | len | dataBits | list | push | pop | str
  | readPort | writePort | diagnostic | read
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The declaration of a name. An `item` holds the index of the item in the file. A `local` holds
the number of the local declaration in its item. The numbers start at 0 in each item, in the
order of the declarations: the implicit `clock`, the parameters, the domain names, and then the
statements. A binder of a pattern takes its number when its arm starts. A `family` holds the
local number of its family binder, which the body takes before its statements, and whether its
first entry is an input.
-/
inductive Ref where
  | type (t : PrimType)
  | fn (f : PrimFn)
  | item (index : Nat)
  | local (id : Nat)
  | family (id : Nat) (input : Bool)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The parameter modes of a prelude function (section 5.6). -/
def fnModes : PrimFn → Array ParamMode
  | .resize | .reinterpret => #[.comptime, .none]
  | .list => #[.comptime]
  | .push => #[.mut, .none]
  | .pop => #[.mut]
  | .staticAssert | .diagnostic => #[.none, .none]
  | .error | .len | .dataBits | .str | .read => #[.none]
  | .readPort => #[.none, .none, .none]
  | .writePort => #[.none, .none, .none, .none]

/-! True for a memory port function: `read_port` or `write_port`. -/
def PrimFn.port : PrimFn → Bool
  | .readPort | .writePort => true
  | _ => false

/-!
The prelude. It holds the scalar types of section 12.1 and the functions `resize`,
`reinterpret`, `static_assert`, and `error` of slice 1. It also holds `Unit` and `len`, the
names of the containers of slice 2, and `Type` and `data_bits`, the names of the types as values.
The names of the strings and the lists are `String`, `List`, `list`, `push`, `pop`, and `str`.
The memory ports are `read_port` and `write_port`, and `diagnostic` makes a record. The handle
type families are `Reg`, `Wire`, `Input`, `Mem`, and `Instance`, and `read` reads a handle.
`true` and `false` are keywords, and `T(n)` is syntax, so they need no name. The prelude structs
are items (`preludeStructs`).
-/
def prelude : List (String × Ref) :=
  [("Bool", .type .bool), ("UInt", .type .uint), ("SInt", .type .sint), ("Nat", .type .nat),
   ("Int", .type .int), ("Unit", .type .unit), ("Type", .type .type), ("resize", .fn .resize),
   ("reinterpret", .fn .reinterpret), ("static_assert", .fn .staticAssert),
   ("error", .fn .error), ("len", .fn .len), ("data_bits", .fn .dataBits),
   ("String", .type .string), ("List", .type .list), ("list", .fn .list), ("push", .fn .push),
   ("pop", .fn .pop), ("str", .fn .str), ("read_port", .fn .readPort),
   ("write_port", .fn .writePort), ("diagnostic", .fn .diagnostic), ("Reg", .type .reg),
   ("Wire", .type .wire), ("Input", .type .input), ("Mem", .type .mem),
   ("Instance", .type .instance), ("read", .fn .read)]

/-! `Domain` waits for more domains (#11), so its `S003` has its own text. -/
def domainText : String :=
  "`Domain` is not supported yet; it comes with more domains (#11); a module has one domain " ++
    "or none, so it needs no `Domain` value"

/-! The `S003` text of a first argument of `Instance` that is not a module (section 6.2). -/
def instanceText : String :=
  "the first argument of `Instance` is not a module; write the module first, for example " ++
    "`Instance[Counter, 8]`"

/-! A declared name and its local number. -/
structure Binder where
  name : Ident
  id : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
A resolved pattern. A variant pattern holds the enum item, the index of the variant, and one
binder or `_` (`none`) for each written place.
-/
inductive Pattern where
  | wild (pos : Pos)
  | int (pos : Pos) (neg : Bool) (value : Nat)
  | bool (pos : Pos) (value : Bool)
  | variant (pos : Pos) (ty v : Ident) (item index : Nat) (binders : List (Option Binder))
  deriving Repr, BEq, Inhabited

/-!
The resolved expression and type expression. They are those of `Source.Syntax` with a `Ref` at
each name, so they are mutually recursive too. The container forms keep the shape of the parsed
forms. A `call` and a `method` hold their call site. The `fn` of a `method` is a `fn` item or
a prelude function, and its `param` is the parameter that the receiver binds to. A type name
refers to a prelude type, a `struct` item, a `type` item, or a local. A local holds a value of
type `Type`, which `Elab` checks. A function type keeps its form, with the `mut` mark of each
parameter type. A `match` holds its scrutinee and its arms. The parser checked the operands
of a builtin, so each builtin has its own form. `typeOf` holds the place of `@TypeOf`, and
`atField` holds the base and the key of `@field`.
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
    | method (pos : Pos) (recv : Expr) (name : Ident) (fn : Ref) (param : Option Nat)
        (args : List Expr) (site : Nat)
    | fnType (pos : Pos) (params : List FnParam) (ret : TypeExpr)
    | variant (pos : Pos) (ty variant : Ident) (item index : Nat) (args : List Expr)
        (called : Bool)
    | «match» (pos : Pos) (scrut : Expr) (arms : List Arm)
    | typeOf (pos : Pos) (place : Expr)
    | atField (pos : Pos) (base key : Expr)

  inductive TypeExpr where
    | name (pos : Pos) (name : String) (ref : Ref)
    | index (pos : Pos) (base : TypeExpr) (args : List Expr)
    | unit (pos : Pos)
    | tuple (pos : Pos) (elems : List TypeExpr)
    | array (pos : Pos) (elem : TypeExpr) (len : Expr)
    | fn (pos : Pos) (params : List FnParam) (ret : TypeExpr)

  inductive FnParam where
    | mk (mutable : Bool) (ty : TypeExpr)

  inductive Arm where
    | mk (pat : Pattern) (value : Expr)
end

deriving instance Repr, BEq, Inhabited for Expr, TypeExpr, FnParam, Arm

/-! The parsed form of a resolved pattern: its binders without their local numbers. -/
def Pattern.source : Pattern → Source.Pattern
  | .wild p => .wild p
  | .int p neg v => .int p neg v
  | .bool p v => .bool p v
  | .variant p t v _ _ bs => .variant p t v (bs.map (·.map (·.name)))

/-!
The parsed form of a resolved expression: each name without its reference, and each call without
its call site. A message prints it as the source writes it, in the form of the printer.
-/
mutual
  def Expr.source : Expr → Source.Expr
    | .num p v => .num p v
    | .bool p v => .bool p v
    | .str p v => .str p v
    | .name p x _ => .name p x
    | .unary p op a => .unary p op a.source
    | .binary p op l r => .binary p op l.source r.source
    | .cond p c y n => .cond p c.source y.source n.source
    | .call p f xs _ => .call p f.source (xs.map Expr.source)
    | .index p b xs => .index p b.source (xs.map Expr.source)
    | .field p b f => .field p b.source f
    | .unit p => .unit p
    | .tuple p xs => .tuple p (xs.map Expr.source)
    | .array p xs => .array p (xs.map Expr.source)
    | .select p b q i => .select p b.source q i
    | .arrayType p t n => .arrayType p t.source n.source
    | .method p r m _ _ xs _ => .method p r.source m (xs.map Expr.source)
    | .fnType p ps r => .fnType p (ps.map FnParam.source) r.source
    | .variant p t v _ _ xs called =>
      if called then .call p (.path p t v) (xs.map Expr.source) else .path p t v
    | .«match» p x as => .«match» p x.source (as.map Arm.source)
    | .typeOf p x => .builtin p .typeOf [x.source]
    | .atField p b k => .builtin p .field [b.source, k.source]

  def TypeExpr.source : TypeExpr → Source.TypeExpr
    | .name p x _ => .name p x
    | .index p b xs => .index p b.source (xs.map Expr.source)
    | .unit p => .unit p
    | .tuple p ts => .tuple p (ts.map TypeExpr.source)
    | .array p t n => .array p t.source n.source
    | .fn p ps r => .fn p (ps.map FnParam.source) r.source

  def FnParam.source : FnParam → Source.FnParam
    | .mk m t => .mk m t.source

  def Arm.source : Arm → Source.Arm
    | .mk q v => .mk q.source v.source
end

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
  | mem (pos : Pos) (name : Binder) (word : TypeExpr) (depth : Expr)
  | input (pos : Pos) (name : Binder) (form : PortForm Expr) (ty : TypeExpr)
  | output (pos : Pos) (name : Binder) (form : PortForm Expr) (ty : TypeExpr)
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

/-! A resolved variant of an enum: its name, its payload types, and its tag value. -/
structure Variant where
  name : Ident
  payload : List TypeExpr
  tag : Expr
  deriving Repr, BEq, Inhabited

/-!
The resolved item. A `Ref.item` holds the index of an item in the resolved file. The `domains`
of a module without a clause hold the one default domain `clock`. A struct has the `prelude`
flag when it is a prelude struct (`preludeStructs`). An enum has its tag type and its variants.
-/
inductive Item where
  | const (pos : Pos) (name : Ident) (ty : TypeExpr) (value : Expr)
  | fn (pos : Pos) (comptime : Bool) (name : Ident) (params : List Param) (ret : TypeExpr)
      (body : List Stmt)
  | module (pos : Pos) (name : Ident) (params : List Param) (domains : List Binder)
      (body : List Stmt)
  | struct (pos : Pos) (name : Ident) (params : List Param) (fields : List StructField)
      (prelude : Bool)
  | alias (pos : Pos) (name : Ident) (ty : TypeExpr)
  | enum (pos : Pos) (name : Ident) (tag : TypeExpr) (variants : List Variant)
  deriving Repr, BEq, Inhabited

/-! The position of the first token of a form. -/
def Expr.pos : Expr → Pos
  | .num p _ | .bool p _ | .str p _ | .name p .. | .unary p .. | .binary p ..
  | .cond p .. | .call p .. | .index p .. | .field p .. | .unit p | .tuple p ..
  | .array p .. | .select p .. | .arrayType p .. | .method p .. | .fnType p .. | .variant p ..
  | .«match» p .. | .typeOf p .. | .atField p .. => p

def TypeExpr.pos : TypeExpr → Pos
  | .name p .. | .index p .. | .unit p | .tuple p .. | .array p .. | .fn p .. => p

def Stmt.pos : Stmt → Pos
  | .local p .. | .assign p .. | .connect p .. | .reg p .. | .wire p .. | .mem p ..
  | .input p .. | .output p .. | .inst p .. | .ret p .. | .ctIf p .. | .ctFor p .. | .block p ..
  | .expr p .. | .alias p .. => p

/-!
Whether a form names one of the locals `ps`. In a signature, a binder of a pattern is a local
that is no parameter, so the check takes the parameters as a set.
-/
abbrev Ids := Std.TreeMap Nat Unit compare

mutual
  def Expr.namesLocal (ps : Ids) : Expr → Bool
    | .name _ _ r => match r with | .local id => ps.contains id | _ => false
    | .num .. | .bool .. | .str .. | .unit _ => false
    | .unary _ _ a => a.namesLocal ps
    | .field _ a _ => a.namesLocal ps
    | .select _ a .. => a.namesLocal ps
    | .binary _ _ l r => l.namesLocal ps || r.namesLocal ps
    | .cond _ c y n => c.namesLocal ps || y.namesLocal ps || n.namesLocal ps
    | .call _ f xs _ => f.namesLocal ps || Expr.anyLocal ps xs
    | .index _ f xs => f.namesLocal ps || Expr.anyLocal ps xs
    | .method _ r _ _ _ xs _ => r.namesLocal ps || Expr.anyLocal ps xs
    | .tuple _ xs => Expr.anyLocal ps xs
    | .array _ xs => Expr.anyLocal ps xs
    | .arrayType _ t n => t.namesLocal ps || n.namesLocal ps
    | .fnType _ qs r => FnParam.anyLocal ps qs || r.namesLocal ps
    | .variant _ _ _ _ _ xs _ => Expr.anyLocal ps xs
    | .«match» _ x as => x.namesLocal ps || Arm.anyLocal ps as
    | .typeOf _ x => x.namesLocal ps
    | .atField _ b k => b.namesLocal ps || k.namesLocal ps

  def Expr.anyLocal (ps : Ids) : List Expr → Bool
    | [] => false
    | x :: xs => x.namesLocal ps || Expr.anyLocal ps xs

  def Arm.anyLocal (ps : Ids) : List Arm → Bool
    | [] => false
    | .mk _ v :: as => v.namesLocal ps || Arm.anyLocal ps as

  def TypeExpr.namesLocal (ps : Ids) : TypeExpr → Bool
    | .name _ _ r => match r with | .local id => ps.contains id | _ => false
    | .unit _ => false
    | .index _ b xs => b.namesLocal ps || Expr.anyLocal ps xs
    | .tuple _ ts => TypeExpr.anyLocal ps ts
    | .array _ t n => t.namesLocal ps || n.namesLocal ps
    | .fn _ qs r => FnParam.anyLocal ps qs || r.namesLocal ps

  def TypeExpr.anyLocal (ps : Ids) : List TypeExpr → Bool
    | [] => false
    | t :: ts => t.namesLocal ps || TypeExpr.anyLocal ps ts

  def FnParam.anyLocal (ps : Ids) : List FnParam → Bool
    | [] => false
    | .mk _ t :: qs => t.namesLocal ps || FnParam.anyLocal ps qs
end

/-!
A function with the parameters `ps` and the result type `ret` is generic in two cases
(section 5.1). It has a `comptime` parameter, or a parameter type or its result type names one
of its parameters. The check reads only the resolved signature, so it needs no evaluation.
-/
def generic (ps : List Param) (ret : TypeExpr) : Bool :=
  let ids : Ids := ps.foldl (fun m q => m.insert q.name.id ()) {}
  ps.any (fun q => q.mode == .comptime || q.ty.namesLocal ids) || ret.namesLocal ids

/-! Position order: the lower line, then the lower column. -/
def before (a b : Pos) : Bool := a.line < b.line || (a.line == b.line && a.col < b.col)

/-! The earlier of two errors by position. -/
def earlier (old : Option Error) (e : Error) : Option Error :=
  match old with
  | some o => if before e.pos o.pos then some e else some o
  | none => some e

/-!
The prelude struct `ReadResponse`: the item
`struct ReadResponse(comptime T: Type) { data: T, valid: Bool }`, already resolved (section
5.6). `Type` and `Bool` are the prelude types, and `T` is the local 0 of the item. It has no
source position, so each of its forms has the position `0:0`. Its errors report at its use.
-/
def response : Item :=
  let p : Pos := ⟨0, 0⟩
  .struct p ⟨p, "ReadResponse"⟩ [⟨p, .comptime, ⟨⟨p, "T"⟩, 0⟩, .name p "Type" (.type .type)⟩]
    [⟨⟨p, "data"⟩, .name p "T" (.local 0)⟩, ⟨⟨p, "valid"⟩, .name p "Bool" (.type .bool)⟩] true

/-!
A prelude struct of slice 4 (section 5.6) with the name `x` and the resolved fields `fs`. It has
no parameters. Each form has the position `0:0`.
-/
def preludeStruct4 (x : String) (fs : List (String × TypeExpr)) : Item :=
  let p : Pos := ⟨0, 0⟩
  .struct p ⟨p, x⟩ [] (fs.map fun (f, t) => ⟨⟨p, f⟩, t⟩) true

/-!
The prelude struct items in the order of section 5.6. They follow the user items, so `base` is
the index of the first one. `ReadResponse` comes first. `String`, `Type`, `Nat`, `Bool`, and
`List` are the prelude types. A field type refers to a prelude struct by its index from `base`,
never by a lookup in the item scope.
-/
def preludeStructs (base : Nat) : List Item :=
  let p : Pos := ⟨0, 0⟩
  let prim (x : String) (t : PrimType) : TypeExpr := .name p x (.type t)
  let item (x : String) (k : Nat) : Expr := .name p x (.item (base + k))
  let list (x : Expr) : TypeExpr := .index p (prim "List" .list) [x]
  let str := prim "String" .string
  let ty := prim "Type" .type
  let nat := prim "Nat" .nat
  let bool := prim "Bool" .bool
  [response,
   preludeStruct4 "FieldInfo" [("name", str), ("ty", ty)],
   preludeStruct4 "TypeInfo"
     [("kind", str), ("fields", list (item "FieldInfo" 1)), ("element", ty), ("length", nat),
      ("width", nat), ("variants", list (item "VariantInfo" 3))],
   preludeStruct4 "VariantInfo"
     [("name", str), ("tag", nat), ("payload", list (.name p "Type" (.type .type)))],
   preludeStruct4 "PortKey" [("name", str), ("indexed", bool), ("index", nat)],
   preludeStruct4 "PortInfo"
     [("key", .name p "PortKey" (.item (base + 4))), ("ty", ty), ("is_input", bool),
      ("domain", str)]]

/-! The number of prelude struct items. -/
def preludeCount : Nat := (preludeStructs 0).length

/-! The name of an item. -/
def Item.name : Item → Ident
  | .const _ n .. | .fn _ _ n .. | .module _ n .. | .struct _ n .. | .alias _ n ..
  | .enum _ n .. => n

/-! The offset of the prelude struct `n` in `preludeStructs`, or none. -/
def preludeStruct (n : String) : Option Nat :=
  (preludeStructs 0).findIdx? (·.name.name == n)

/-!
The index of `ReadResponse` in a resolved file of `size` items. It is the first prelude struct,
so the read takes constant work.
-/
def responseIndex (size : Nat) : Nat := size - preludeCount

/-!
A visible declaration, the number of its scope, and the position of its name. The item scope has
the number 0.
-/
structure Binding where
  ref : Ref
  scope : Nat
  pos : Pos

/-!
What the family walk of a body knows of one port name. `family` holds its first indexed
declaration: the position of its name, the number of its family binder, and whether it is an
input. `scalar` holds the position of the name of its first scalar port.
-/
structure PortName where
  family : Option (Pos × Nat × Bool) := none
  scalar : Option Pos := none
  deriving Inhabited

/-!
The state of the walk. `env` maps each visible name to its innermost declaration. `scope` is the
number of the current scope, and `scopes` the next free scope number. `locals` is the next local
number of the current item, and `sites` its next call site. `ports` holds the port names of the
current body (`PortName`). `dup` holds the first `S002`, and `unknown` the first `S003`.
-/
structure St where
  env : Std.TreeMap String Binding compare
  scope : Nat
  scopes : Nat
  locals : Nat
  sites : Nat
  ports : Std.TreeMap String PortName compare
  dup : Option Error
  unknown : Option Error

/-!
The context of the walk holds the parsed items, for the kind of an item. It also holds the item
scope, which maps each item name to its index. A receiver call looks up its name there, past
each local. The prelude structs have the indices after the user items.
-/
structure File where
  items : Array Source.Item
  names : Std.TreeMap String Nat compare

abbrev M := ReaderT File (StateM St)

def recordDup (e : Error) : M Unit := modify fun s => { s with dup := earlier s.dup e }

def recordUnknown (e : Error) : M Unit :=
  modify fun s => { s with unknown := earlier s.unknown e }

/-!
Adds `n` to the current scope with `ref`. Another declaration of the same scope is `S002` at the
later of the two names. Only a family binder, which the body binds before its statements, can be
the later one. An indexed declaration binds its family again in its own block, so the same family
binder is no second declaration.
-/
def bind (n : Ident) (ref : Ref) : M Unit := do
  let s ← get
  if let some b := s.env.get? n.name then
    if b.scope == s.scope && !(ref matches .family .. && b.ref == ref) then
      let p := if before n.pos b.pos then b.pos else n.pos
      recordDup ⟨.S002, p, s!"`{n.name}` is already declared in this scope"⟩
  modify fun t => { t with env := t.env.insert n.name ⟨ref, t.scope, n.pos⟩ }

/-! The next local number. -/
def fresh : M Nat := modifyGet fun s => (s.locals, { s with locals := s.locals + 1 })

/-! Declares the local `n` with the next local number. -/
def declare (n : Ident) : M Binder := do
  let id ← fresh
  bind n (.local id)
  return ⟨n, id⟩

/-! The `S002` text of a family and a scalar port `x`, the earlier name at `b` (section 6.2). -/
def familyScalarText (x : String) (b : Pos) : String :=
  s!"`{x}` names a port family and a scalar port, here and at {b.line}:{b.col}; use one form " ++
    "for the name"

/-! The `S002` text of a family `x` with two directions, the earlier entry at `b` (section 6.2). -/
def familyDirectionsText (x : String) (b : Pos) : String :=
  s!"the port family `{x}` has an input entry and an output entry, here and at " ++
    s!"{b.line}:{b.col}; give the entries of one direction another name"

/-!
The family walk sees the port name `n`, with a key if `indexed`, as an input if `input`. The
walk runs in source order, so each `S002` is at the later name. The first indexed declaration of
`n` takes a local number and binds the family binder in the scope of the body.
-/
def seePort (n : Ident) (indexed input : Bool) : M Unit := do
  let fam (e : PortName) : M PortName := do
    let id ← fresh
    bind n (.family id input)
    return { e with family := some (n.pos, id, input) }
  let e := ((← get).ports.get? n.name).getD {}
  let e ← match indexed, e.family, e.scalar with
    | false, some (b, _), _ =>
      recordDup ⟨.S002, n.pos, familyScalarText n.name b⟩
      pure { e with scalar := e.scalar <|> some n.pos }
    | false, none, _ => pure { e with scalar := e.scalar <|> some n.pos }
    | true, _, some c =>
      recordDup ⟨.S002, n.pos, familyScalarText n.name c⟩
      if e.family.isSome then pure e else fam e
    | true, some (b, _, i), none =>
      if i != input then recordDup ⟨.S002, n.pos, familyDirectionsText n.name b⟩
      pure e
    | true, none, none => fam e
  modify fun s => { s with ports := s.ports.insert n.name e }

/-!
The family walk sees a port of the form `k`. A keyed port is no port name of the walk: its binder
is a name of the body only (section 5.6).
-/
def famPort (n : Ident) (k : PortForm α) (input : Bool) : M Unit :=
  match k with
  | .scalar => seePort n false input
  | .indexed _ => seePort n true input
  | .keyed _ => pure ()

/-!
The family walk of a body (section 5.6). It walks a module body and the body of a `fn` without
`comptime`. It visits each statement at each block depth in pre-order, before the statements
resolve.
-/
mutual
  def famStmt : Source.Stmt → M Unit
    | .input _ n k _ => famPort n k true
    | .output _ n k _ => famPort n k false
    | .ctIf _ _ y n => do
      famStmts y
      match n with
      | some n => famStmts n
      | none => pure ()
    | .ctFor _ _ _ _ b | .block _ b => famStmts b
    | _ => pure ()

  def famStmts : List Source.Stmt → M Unit
    | [] => pure ()
    | s :: ss => do famStmt s; famStmts ss
end

/-!
The binder of the port `n`. An indexed declaration of a walked body takes its family binder, and
it binds the name in its own block too (section 5.6). Another port declares a local.
-/
def port (n : Ident) (k : PortForm Expr) : M Binder := do
  if k matches .indexed _ then
    if let some ⟨some (_, id, input), _⟩ := (← get).ports.get? n.name then
      bind n (.family id input)
      return ⟨n, id⟩
  declare n

/-! Runs `act` in a new scope. The declarations of `act` are not visible after it. -/
def inScope (act : M α) : M α := do
  let s ← get
  set { s with scope := s.scopes, scopes := s.scopes + 1 }
  let r ← act
  modify fun t => { t with env := s.env, scope := s.scope }
  return r

/-! `S003` at `pos` for the name `n` that is neither declared nor in the prelude. -/
def missing (pos : Pos) (n : String) : M Unit :=
  let msg := if n == "Domain" then domainText else s!"`{n}` is not declared"
  recordUnknown ⟨.S003, pos, msg⟩

/-!
The prelude declaration of the name `n`. A prelude struct is an item after the user items
(`preludeStructs`).
-/
def inPrelude (n : String) : M (Option Ref) := do
  match prelude.lookup n with
  | some r => return some r
  | none => do
    let k := (← read).items.size
    return (preludeStruct n).map (.item <| k + ·)

/-!
The declaration of the name `n` at `pos`, or `S003`. After an error, the walk continues with a
placeholder, and `resolve` discards its result.
-/
def lookup (pos : Pos) (n : String) : M (Option Ref) := do
  match (← get).env.get? n with
  | some b => return some b.ref
  | none =>
    match ← inPrelude n with
    | some r => return some r
    | none => missing pos n; return none

def isModule (i : Nat) : M Bool := return (← read).items[i]? matches some (.module ..)

def wrongKind (pos : Pos) (n what : String) : M Unit :=
  recordUnknown ⟨.S003, pos, s!"`{n}` is not {what}"⟩

/-!
A name in a type position refers to a type: a prelude type, a `struct` item, a `type` item, an
`enum` item, or a local. Only `Elab` knows whether a local holds a type.
-/
def isType : Ref → M Bool
  | .type _ | .local _ => return true
  | .item i => do
    match (← read).items[i]? with
    | some (.struct ..) | some (.alias ..) | some (.enum ..) => return true
    | some _ => return false
    | none => return i - (← read).items.size < preludeCount
  | .fn _ | .family .. => return false

/-! The next call site of the current item body. -/
def site : M Nat := modifyGet fun s => (s.sites, { s with sites := s.sites + 1 })

/-!
The function `m` of a receiver call: a `fn` item of the item scope, else a prelude function. A
local does not hide it. Another name is `S003` at `m`.
-/
def method (m : Ident) : M Ref := do
  let notFn : M Ref := do
    recordUnknown ⟨.S003, m.pos, s!"`{m.name}` is not a function; a receiver call `a.f()` " ++
      s!"needs a function `f`, so write `{m.name}(a)` to call a type or a function value"⟩
    return default
  match (← read).names.get? m.name with
  | some i => if (← read).items[i]? matches some (.fn ..) then return .item i else notFn
  | none =>
    match ← inPrelude m.name with
    | some (.fn f) => return .fn f
    | some _ => notFn
    | none => missing m.pos m.name; return default

/-!
The parameter of the function `f` that the receiver of a receiver call binds to. It is the first
parameter without a written `comptime` mark, also in a `comptime fn` (section 5.6).
-/
def receiver : Ref → M (Option Nat)
  | .item i => do
    match (← read).items[i]? with
    | some (.fn _ _ _ ps _ _) => return ps.findIdx? (·.mode != .comptime)
    | _ => return none
  | .fn g => return (fnModes g).findIdx? (· != .comptime)
  | _ => return none

/-!
The enum item and the variant index of the path `x::y` at `pos`. `x` resolves by the ordinary
scoping, so a local shadows an enum item. A first part that is not an enum item is `S003` at
`pos`, and a second part that names no variant is `S003` at `y`. After an error, the result is a
placeholder.
-/
def variantRef (pos : Pos) (x y : Ident) : M (Nat × Nat) := do
  let notEnum : M (Nat × Nat) := do
    recordUnknown ⟨.S003, pos, s!"`{x.name}` is not an enum, so `{x.name}::{y.name}` names no " ++
      "variant; use the name of an enum"⟩
    return (0, 0)
  let some ⟨.item i, _, _⟩ := (← get).env.get? x.name | notEnum
  let some (.enum _ _ _ vs) := (← read).items[i]? | notEnum
  match vs.findIdx? (·.name.name == y.name) with
  | some j => return (i, j)
  | none =>
    recordUnknown ⟨.S003, y.pos, s!"`{x.name}` has no variant `{y.name}`; use a variant " ++
      s!"that `{x.name}` declares"⟩
    return (i, 0)

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
    | .call _ (.path q x y) xs => do
      -- A constructor makes no call frame, but its call node keeps its site.
      let _ ← site
      let (i, j) ← variantRef q x y
      return .variant q x y i j (← xs.mapM expr) true
    | .call p f xs => do
      let k ← site
      return .call p (← expr f) (← xs.mapM expr) k
    | .index p b xs => do
      let b ← expr b
      return .index p b (← indexArgs (b matches .name _ _ (.type .instance)) xs)
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
      return .method p r m f (← receiver f) (← xs.mapM expr) k
    | .fnType p ps r => do
      let ps ← ps.mapM fnParam
      return .fnType p ps (← typeExpr r)
    | .path p x y => do
      let (i, j) ← variantRef p x y
      return .variant p x y i j [] false
    | .«match» p x as => do
      let x ← expr x
      return .«match» p x (← as.mapM arm)
    | .builtin p .typeOf [x] => return .typeOf p (← expr x)
    | .builtin p .field [b, k] => return .atField p (← expr b) (← expr k)
    | .builtin p b xs => do
      -- The parser checks the number of operands (`Parse.builtinCheck`), so only a tree that
      -- the parser did not make reaches this case.
      recordUnknown ⟨.S001, p, b.arityText xs.length⟩
      return .unit p

  def typeExpr : Source.TypeExpr → M TypeExpr
    | .name p n => do
      match ← lookup p n with
      | some r =>
        unless ← isType r do wrongKind p n "a type"
        return .name p n r
      | none => return .name p n default
    | .index p b xs => do
      let b ← typeExpr b
      return .index p b (← indexArgs (b matches .name _ _ (.type .instance)) xs)
    | .unit p => return .unit p
    | .tuple p ts => return .tuple p (← ts.mapM typeExpr)
    | .array p t n => return .array p (← typeExpr t) (← expr n)
    | .fn p ps r => do
      let ps ← ps.mapM fnParam
      return .fn p ps (← typeExpr r)

  /--
  The arguments of an index. The first argument of the prelude `Instance` (`inst`) resolves by
  the ordinary scoping to a module item. Another first argument is `S003` at its start. That
  error comes first at its position, so it replaces each `S003` in the argument.
  -/
  def indexArgs (inst : Bool) : List Source.Expr → M (List Expr)
    | x :: xs => do
      if !inst then return (← expr x) :: (← xs.mapM expr)
      let rest (m : Expr) : M (List Expr) := return m :: (← xs.mapM expr)
      if let .name p n := x then
        if let some ⟨.item i, _, _⟩ := (← get).env.get? n then
          if ← isModule i then return ← rest (.name p n (.item i))
      let old := (← get).unknown
      let m ← match x with
        | .name p n => pure (Expr.name p n default)
        | x => expr x
      modify fun s => { s with unknown := earlier old ⟨.S003, m.pos, instanceText⟩ }
      rest m
    | [] => return []

  /-- A parameter type of a function type. It declares no name. -/
  def fnParam : Source.FnParam → M FnParam
    | .mk m t => return .mk m (← typeExpr t)

  /-- An arm: its pattern path, then its binders and its value in a new scope. -/
  def arm : Source.Arm → M Arm
    | .mk q v => do
      match q with
      | .wild p => return .mk (.wild p) (← expr v)
      | .int p n k => return .mk (.int p n k) (← expr v)
      | .bool p b => return .mk (.bool p b) (← expr v)
      | .variant p x y bs =>
        let (i, j) ← variantRef p x y
        inScope do
          let bs ← bs.mapM (·.mapM declare)
          return .mk (.variant p x y i j bs) (← expr v)
end

/-! The module item of an `instance`. -/
def moduleRef (m : Ident) : M Nat := do
  match ← lookup m.pos m.name with
  | some (.item i) => if ← isModule i then return i
  | some _ => pure ()
  | none => return 0
  wrongKind m.pos m.name "a module"
  return 0

/-!
The key and the type of a port, in source order: a family key comes before the type, and an `as`
key after it.
-/
def portParts (k : PortForm Source.Expr) (ty : Source.TypeExpr) :
    M (PortForm Expr × TypeExpr) :=
  match k with
  | .scalar => return (.scalar, ← typeExpr ty)
  | .indexed e => do
    let e ← expr e
    return (.indexed e, ← typeExpr ty)
  | .keyed e => do
    let ty ← typeExpr ty
    return (.keyed (← expr e), ty)

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
    | .mem p n w d => do
      let w ← typeExpr w
      let d ← expr d
      return .mem p (← declare n) w d
    | .input p n k ty => do
      let (k, ty) ← portParts k ty
      return .input p (← port n k) k ty
    | .output p n k ty => do
      let (k, ty) ← portParts k ty
      return .output p (← port n k) k ty
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

/-!
The variants of an enum. A variant name is not a local, so the variants have their own table of
names. A second variant with one name is `S002` at its name.
-/
def variants (vs : List Source.Variant) : M (List Variant) := do
  let mut seen : Std.TreeMap String Unit compare := {}
  let mut out : Array Variant := #[]
  for v in vs do
    if seen.contains v.name.name then
      recordDup ⟨.S002, v.name.pos, s!"the variant `{v.name.name}` is already declared in this " ++
        "enum; rename one of the two variants"⟩
    seen := seen.insert v.name.name ()
    let ps ← v.payload.mapM typeExpr
    out := out.push ⟨v.name, ps, ← expr v.tag⟩
  return out.toList

/-!
The parameters, the domain names, and the body of an item share one new scope. A module body and
the body of a `fn` without `comptime` have port names (`ports`).
-/
def body (act : M α) : M α := do
  modify fun s => { s with locals := 0, ports := {} }
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
    unless c do famStmts b
    return .fn p c n ps r (← bodyStmts b)
  | .module p n ps ds b => body do
    -- The implicit `clock` has no token, so it comes before the parameters.
    let clock ← if ds.isNone then some <$> declare ⟨p, "clock"⟩ else pure none
    let ps ← ps.mapM param
    let ds ← match clock with
      | some c => pure [c]
      | none => (ds.getD []).mapM declare
    famStmts b
    return .module p n ps ds (← bodyStmts b)
  | .struct p n ps fs => body do
    let ps ← ps.mapM param
    return .struct p n ps (← fields fs) false
  | .alias p n t => return .alias p n (← typeExpr t)
  | .enum p n t vs => do
    let t ← typeExpr t
    return .enum p n t (← variants vs)

def itemName : Source.Item → Ident
  | .const _ n .. | .fn _ _ n .. | .module _ n .. | .struct _ n .. | .alias _ n ..
  | .enum _ n .. => n

/-! Runs `act` in the item scope of `items`. The result is the first error, if one occurs. -/
def inFile (items : List Source.Item) (act : M α) : Except Error α :=
  let walk : M α := do
    for (it, i) in items.zipIdx do
      bind (itemName it) (.item i)
    modify fun s => { s with scopes := 1 }
    act
  let names := items.zipIdx.foldl (fun m (it, i) => m.insert (itemName it).name i) {}
  let (out, s) := (walk.run ⟨items.toArray, names⟩).run ⟨{}, 0, 0, 0, 0, {}, none, none⟩
  match s.dup, s.unknown with
  | some e, _ => .error e
  | none, some e => .error e
  | none, none => .ok out

/-!
The resolved items of a file, or the first error. The index of an item in the result is its
index in `items`. The prelude structs follow the user items, so they change no index.
-/
def resolve (items : List Source.Item) : Except Error (Array Item) :=
  inFile items (return (← items.toArray.mapM item) ++ (preludeStructs items.length).toArray)

/-! An expression in the file scope, such as the `EXPR` of `eval`, or its first `S003`. -/
def resolveExpr (items : List Source.Item) (e : Source.Expr) : Except Error Expr :=
  inFile items (expr e)

end Silicon.Source.Resolve
