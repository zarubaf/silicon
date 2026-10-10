/-!
The source AST of slice 1, its source positions, and the error codes of the front end.
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

/-! An expression. A type in an expression position, such as `UInt[8]`, is an `index`. -/
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
  deriving Repr, BEq, Inhabited

/-! A type expression: a type name, or a type family with its static arguments. -/
inductive TypeExpr where
  | name (pos : Pos) (name : String)
  | index (pos : Pos) (base : TypeExpr) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-! A statement. A target of `assign` or `connect` is a `name` or a `field` expression. -/
inductive Stmt where
  | local (pos : Pos) (mutable : Bool) (name : Ident) (ty : Option TypeExpr) (value : Expr)
  | assign (pos : Pos) (target value : Expr)
  | connect (pos : Pos) (target value : Expr)
  | reg (pos : Pos) (name : Ident) (ty : TypeExpr) (init : Expr)
  | wire (pos : Pos) (name : Ident) (ty : TypeExpr)
  | input (pos : Pos) (name : Ident) (ty : TypeExpr)
  | output (pos : Pos) (name : Ident) (ty : TypeExpr)
  | inst (pos : Pos) (name module : Ident) (args : List Expr)
  | ret (pos : Pos) (value : Option Expr)
  | ctIf (pos : Pos) (cond : Expr) (yes : List Stmt) (no : Option (List Stmt))
  | ctFor (pos : Pos) (var : Ident) (lo hi : Expr) (body : List Stmt)
  | block (pos : Pos) (body : List Stmt)
  | expr (pos : Pos) (value : Expr)
  deriving Repr, BEq, Inhabited

/-! A parameter of a function or a module. A module parameter always has `comptime`. -/
structure Param where
  pos : Pos
  comptime : Bool
  name : Ident
  ty : TypeExpr
  deriving Repr, BEq, Inhabited

/-!
A top-level item. The `domains` of a module are `none` without a `domains` clause, which
means the one default domain `clock`. An empty list means no domain: a combinational module.
The list holds at most one name in slice 1.
-/
inductive Item where
  | const (pos : Pos) (name : Ident) (ty : TypeExpr) (value : Expr)
  | fn (pos : Pos) (comptime : Bool) (name : Ident) (params : List Param) (ret : TypeExpr)
      (body : List Stmt)
  | module (pos : Pos) (name : Ident) (params : List Param) (domains : Option (List Ident))
      (body : List Stmt)
  deriving Repr, BEq, Inhabited

/-! The front-end error codes of the spec. The spec defines no `S009`. -/
inductive ErrorCode where
  | S001 | S002 | S003 | S004 | S005 | S006 | S007 | S008
  | S010 | S011 | S012 | S013 | S014 | S015 | S016 | S017 | S018 | S019 | S020
  deriving Repr, DecidableEq, BEq, Inhabited

def ErrorCode.toString : ErrorCode → String
  | .S001 => "S001" | .S002 => "S002" | .S003 => "S003" | .S004 => "S004"
  | .S005 => "S005" | .S006 => "S006" | .S007 => "S007" | .S008 => "S008"
  | .S010 => "S010" | .S011 => "S011" | .S012 => "S012" | .S013 => "S013"
  | .S014 => "S014" | .S015 => "S015" | .S016 => "S016" | .S017 => "S017"
  | .S018 => "S018" | .S019 => "S019" | .S020 => "S020"

instance : ToString ErrorCode := ⟨ErrorCode.toString⟩

/-! An error has a code, the position of section 6.2 of the front-end spec, and a message. -/
structure Error where
  code : ErrorCode
  pos : Pos
  msg : String
  deriving Repr, DecidableEq, BEq, Inhabited

end Silicon.Source
