/-!
This AST defines the MLIR subset for the reference lowering and memory models.
Value names have no percent sign. The printer adds it.
A well-formed constant has `value < 2^w`. Operand types match the widths of each operation.
`Lower` and `memModel` emit only such operations for valid source designs and memory configurations.
Phase 4b makes evaluation partial or adds a typing judgment to enforce these conditions.
Module outputs follow the output port order and have the types of those ports.
Each operation in a module body except `instance` has exactly one result name.
`Lower` and `memModel` emit only such bodies. Phase 4b checks this condition.
-/

namespace Silicon.Core.Mlir

inductive Ty where
  | int (w : Nat)
  | clock
  | array (n w : Nat)
  deriving DecidableEq, Repr

inductive Pred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr

inductive CombOp where
  | add | sub | mul | and | or | xor | shl | shru | shrs
  deriving DecidableEq, Repr

inductive Op where
  | constant (w value : Nat)
  | comb (op : CombOp) (a b : String) (w : Nat)
  | icmp (p : Pred) (a b : String) (w : Nat)
  | mux (c a b : String) (ty : Ty)
  | extract (a : String) (lo : Nat) (wIn wOut : Nat)
  | concat (a b : String) (wa wb : Nat)
  | replicate (a : String) (wIn wOut : Nat)
  | compreg (next clk : String) (reset : Option (String × String)) (ty : Ty)
  | arrayGet (arr idx : String) (n w a : Nat)
  | arrayInject (arr idx v : String) (n w a : Nat)
  | instance (inst callee : String) (args : List (String × String × Ty))
      (results : List (String × Ty))
  deriving DecidableEq, Repr

inductive Dir where
  | input | output
  deriving DecidableEq, Repr

structure Port where
  dir : Dir
  name : String
  ty : Ty
  deriving DecidableEq, Repr

structure Module where
  name : String
  ports : List Port
  body : List (List String × Op)
  outputs : List String
  deriving DecidableEq, Repr

inductive Item where
  | module (m : Module)
  | extern (name : String) (ports : List Port)
  deriving DecidableEq, Repr

structure Design where
  items : List Item
  deriving DecidableEq, Repr

end Silicon.Core.Mlir
