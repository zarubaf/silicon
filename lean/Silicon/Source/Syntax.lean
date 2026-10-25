-- SPDX-License-Identifier: Apache-2.0
/-!
The source AST of slices 1 to 4, its source positions, the error codes of the front end, and
the prelude type names.
The AST dump prints each constructor name in lowercase, and the Rust front end uses the
same names. Each node keeps the position of the first token of its form.
-/
namespace Silicon.Source

/-! A position is a line and a column. Both start at 1. A column counts characters. -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

/-! A name at a declaration or a selection keeps its own position for `S002` and `S003`. -/
structure Ident where
  pos : Pos
  name : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The prefix operators `!`, `~`, and `-`. -/
inductive UnOp where
  | not | inv | neg
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The infix operators. A name ending in `w` is the wrapping form: `+%`, `-%`, `*%`. -/
inductive BinOp where
  | lor | land | or | xor | and
  | eq | ne | lt | le | gt | ge
  | shl | shr
  | add | sub | addw | subw
  | mul | div | rem | mulw
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
A pattern of a `match` arm (slice 3) is `_`, an integer literal with its sign, `true`, or
`false`. It can also be a variant path with one binder or `_` for each payload value. A binder
`_` is `none`. A
variant pattern without binders has an empty list, so `E::V` and `E::V()` give one AST. The
position of a negative literal is the position of its `-`.
-/
inductive Pattern where
  | wild (pos : Pos)
  | int (pos : Pos) (neg : Bool) (value : Nat)
  | bool (pos : Pos) (value : Bool)
  | variant (pos : Pos) (ty v : Ident) (binders : List (Option Ident))
  deriving Repr, BEq, Inhabited

/-!
A builtin of slice 4 (section 9.3): `@TypeOf` and `@field`. Each phase of section 14.4 adds the
name of its builtin. `@typeInfo`, `@Struct`, and `@ports` are not yet names here.
-/
inductive Builtin where
  | typeOf | field
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The name of a builtin after `@`. -/
def Builtin.name : Builtin → String
  | .typeOf => "TypeOf" | .field => "field"

/-! The builtin of a name after `@`, if the current phase has it. -/
def Builtin.ofName : String → Option Builtin
  | "TypeOf" => some .typeOf
  | "field" => some .field
  | _ => none

/-! The number of operands of a builtin (section 5.6): 2 for `@field`, 1 for each other. -/
def Builtin.arity : Builtin → Nat
  | .typeOf => 1 | .field => 2

/-! The form of a builtin in section 9.3, for the fix of "Builtin arity". -/
def Builtin.form : Builtin → String
  | .typeOf => "@TypeOf(x)" | .field => "@field(x, k)"

/-!
An expression and a type expression. The two are mutually recursive, because an array type
`[T; N]` is also an expression (`arrayType`). Its element `T` is a type expression, and its
length `N` is an expression.

A type in an expression position, such as `UInt[8]`, is an `index`. A `tuple` holds at least one
element: `()` is `unit`. A `select` is the selector `.N` of a tuple. Its `litPos` is the position
of the number literal, for `S013`. A `method` is the receiver call `recv.name(args)`. Its position
is the position of the receiver, the start of the call. A `path` is a variant path `E::V` of
two names (slice 3). A constructor `E::V(args)` is a `call` of a `path`. A `match` holds its
scrutinee and its arms, and an `Arm` holds a pattern and its expression (slice 3). A `builtin`
is `@name(args)` at the position of its `@`, with the operands in source order (slice 4).

A type expression is a type name, a type family with its static arguments, or the unit type
`()`. It can also be a tuple type, an array type `[T; N]`, or a function type
`fn (T, mut U) -> V`. A `tuple` holds at least one element type. A function type in an
expression is a `fnType`, a unary operand. A `FnParam` is a parameter type of a function type,
with its `mut` mark. It has no `comptime` mark, because that mark is `S001`.
-/
mutual
  inductive Expr where
    | num (pos : Pos) (value : Nat)
    | bool (pos : Pos) (value : Bool)
    | str (pos : Pos) (value : String)
    | name (pos : Pos) (name : String)
    | unary (pos : Pos) (op : UnOp) (arg : Expr)
    | binary (pos : Pos) (op : BinOp) (lhs rhs : Expr)
    | cond (pos : Pos) (cond yes no : Expr)
    | call (pos : Pos) (callee : Expr) (args : List Expr)
    | index (pos : Pos) (base : Expr) (args : List Expr)
    | field (pos : Pos) (base : Expr) (field : Ident)
    | unit (pos : Pos)
    | tuple (pos : Pos) (elems : List Expr)
    | array (pos : Pos) (elems : List Expr)
    | select (pos : Pos) (base : Expr) (litPos : Pos) (index : Nat)
    | arrayType (pos : Pos) (elem : TypeExpr) (len : Expr)
    | method (pos : Pos) (recv : Expr) (name : Ident) (args : List Expr)
    | fnType (pos : Pos) (params : List FnParam) (ret : TypeExpr)
    | path (pos : Pos) (ty variant : Ident)
    | «match» (pos : Pos) (scrut : Expr) (arms : List Arm)
    | builtin (pos : Pos) (b : Builtin) (args : List Expr)

  inductive TypeExpr where
    | name (pos : Pos) (name : String)
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

/-!
A place: a name, or a field, an index, a selector, or an `@field` selection of a place (section
9.3). The base of `@field` is its first operand.
-/
def Expr.place : Expr → Bool
  | .name .. => true
  | .field _ b _ | .index _ b _ | .select _ b .. => b.place
  | .builtin _ .field [b, _] => b.place
  | _ => false

/-!
The operands `xs` fit the builtin `b` (section 9.3): their number is the arity of `b`, and the
operand of `@TypeOf` is a place.
-/
def Builtin.operandsOk (b : Builtin) (xs : List Expr) : Bool :=
  xs.length == b.arity && match b with
    | .typeOf => xs.all Expr.place
    | .field => true

/-!
The name form of a port (section 5.6). A `scalar` port has a name only. An `indexed` port has its
family key in `[ ]` after the name. A `keyed` port has an `as` key after the type. A port has one
form, so no port has both an index and an `as` key.
-/
inductive PortForm (α : Type) where
  | scalar
  | indexed (key : α)
  | keyed (key : α)
  deriving Repr, BEq, Inhabited

/-! The form of a port with the family key `k`, if it has one, and no `as` key. -/
def PortForm.ofIndex : Option α → PortForm α
  | some k => .indexed k
  | none => .scalar

/-! The family key of an indexed port. -/
def PortForm.index? : PortForm α → Option α
  | .indexed k => some k
  | _ => none

def PortForm.map (f : α → β) : PortForm α → PortForm β
  | .scalar => .scalar
  | .indexed k => .indexed (f k)
  | .keyed k => .keyed (f k)

/-!
A statement. A target of `assign` or `connect` is a `name` or a `field` expression. An `alias` is
the statement `type N = T;`.
-/
inductive Stmt where
  | local (pos : Pos) (mutable : Bool) (name : Ident) (ty : Option TypeExpr) (value : Expr)
  | assign (pos : Pos) (target value : Expr)
  | connect (pos : Pos) (target value : Expr)
  | reg (pos : Pos) (name : Ident) (ty : TypeExpr) (init : Expr)
  | wire (pos : Pos) (name : Ident) (ty : TypeExpr)
  | mem (pos : Pos) (name : Ident) (word : TypeExpr) (depth : Expr)
  | input (pos : Pos) (name : Ident) (form : PortForm Expr) (ty : TypeExpr)
  | output (pos : Pos) (name : Ident) (form : PortForm Expr) (ty : TypeExpr)
  | inst (pos : Pos) (name module : Ident) (args : List Expr)
  | ret (pos : Pos) (value : Option Expr)
  | ctIf (pos : Pos) (cond : Expr) (yes : List Stmt) (no : Option (List Stmt))
  | ctFor (pos : Pos) (var : Ident) (lo hi : Expr) (body : List Stmt)
  | block (pos : Pos) (body : List Stmt)
  | expr (pos : Pos) (value : Expr)
  | alias (pos : Pos) (name : Ident) (ty : TypeExpr)
  deriving Repr, BEq, Inhabited

/-! The mode of a parameter: no mark, `comptime`, or `mut`. -/
inductive ParamMode where
  | none | comptime | mut
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
A parameter of a function, a module, or a struct. A module parameter and a struct parameter always
have the mode `comptime`.
-/
structure Param where
  pos : Pos
  mode : ParamMode
  name : Ident
  ty : TypeExpr
  deriving Repr, BEq, Inhabited

/-! A field of a struct: `name: ty`. -/
structure StructField where
  name : Ident
  ty : TypeExpr
  deriving Repr, BEq, Inhabited

/-!
A variant of an enum: `name(payload) = tag`. A variant without payload types has an empty
`payload`, so `Add` and `Add()` give one AST.
-/
structure Variant where
  name : Ident
  payload : List TypeExpr
  tag : Expr
  deriving Repr, BEq, Inhabited

/-!
A top-level item. A `struct` without parameters has an empty list of parameters. An `alias` is
the item `type N = T;`. The `domains` of a module are `none` without a `domains` clause, which
means the one default domain `clock`. An empty list means no domain: a combinational module.
The list holds at most one name in slice 1. An `enum` has its tag type and its variants.
-/
inductive Item where
  | const (pos : Pos) (name : Ident) (ty : TypeExpr) (value : Expr)
  | fn (pos : Pos) (comptime : Bool) (name : Ident) (params : List Param) (ret : TypeExpr)
      (body : List Stmt)
  | module (pos : Pos) (name : Ident) (params : List Param) (domains : Option (List Ident))
      (body : List Stmt)
  | struct (pos : Pos) (name : Ident) (params : List Param) (fields : List StructField)
  | alias (pos : Pos) (name : Ident) (ty : TypeExpr)
  | enum (pos : Pos) (name : Ident) (tag : TypeExpr) (variants : List Variant)
  deriving Repr, BEq, Inhabited

/-! The front-end error codes of the spec. The spec defines no `S009`. -/
inductive ErrorCode where
  | S001 | S002 | S003 | S004 | S005 | S006 | S007 | S008
  | S010 | S011 | S012 | S013 | S014 | S015 | S016 | S017 | S018 | S019 | S020
  | S021 | S022
  deriving Repr, DecidableEq, BEq, Inhabited

def ErrorCode.toString : ErrorCode → String
  | .S001 => "S001" | .S002 => "S002" | .S003 => "S003" | .S004 => "S004"
  | .S005 => "S005" | .S006 => "S006" | .S007 => "S007" | .S008 => "S008"
  | .S010 => "S010" | .S011 => "S011" | .S012 => "S012" | .S013 => "S013"
  | .S014 => "S014" | .S015 => "S015" | .S016 => "S016" | .S017 => "S017"
  | .S018 => "S018" | .S019 => "S019" | .S020 => "S020" | .S021 => "S021"
  | .S022 => "S022"

instance : ToString ErrorCode := ⟨ErrorCode.toString⟩

/-! An error has a code, the position of section 6.2 of the front-end spec, and a message. -/
structure Error where
  code : ErrorCode
  pos : Pos
  msg : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-! A string in a message: at most 64 characters, then a note of the full length. -/
def strText (m : String) : String :=
  if m.length ≤ 64 then m else s!"{(m.take 64).toString}... ({m.length} characters)"

/-!
The prelude type names of section 5.6: the builtin types of `Resolve.prelude`, then the prelude
structs of `Resolve.preludeStructs`. A message names a user struct or enum with one of these
names as `crate::X`. The tests of the resolver hold this list equal to its two tables.
-/
def preludeTypeNames : List String :=
  ["Bool", "UInt", "SInt", "Nat", "Int", "Unit", "Type", "String", "List", "Reg", "Wire",
   "Input", "Mem", "Instance", "ReadResponse", "FieldInfo", "TypeInfo", "VariantInfo",
   "PortKey", "PortInfo"]

end Silicon.Source
