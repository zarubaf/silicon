namespace Silicon.Core.Mlir

inductive Ty where
  | int (w : Nat)
  | clock
  | array (n w : Nat)
  deriving DecidableEq, Repr

inductive Pred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr

/-! Value names have no percent sign. The printer adds it. -/
inductive Op where
  | constant (w value : Nat)
  | comb (name : String) (args : List String) (w : Nat)
  | icmp (p : Pred) (a b : String) (w : Nat)
  | mux (c a b : String) (w : Nat)
  | arrayMux (c a b : String) (n w : Nat)
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
  outputs : List (String × Ty)
  deriving DecidableEq, Repr

inductive Item where
  | module (m : Module)
  | extern (name : String) (ports : List Port)
  deriving DecidableEq, Repr

structure Design where
  items : List Item
  deriving DecidableEq, Repr

end Silicon.Core.Mlir
