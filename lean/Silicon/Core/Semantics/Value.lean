import Silicon.Core.Syntax

/-!
Data values have two states per bit. Arithmetic keeps the declared width.
Memory addresses use natural numbers and never wrap to the memory depth.
-/
namespace Silicon.Core.Semantics

abbrev Value (width : Nat) := BitVec width

/-! Concatenation has its own typed form because its result has a different width. -/
def evalOp (op : BinOp) (ordinary : op ≠ .concat) (a b : Value width) : Value width :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shl => a <<< b.toNat
  | .shru => a >>> b.toNat
  | .shrs => a.sshiftRight b.toNat
  | .concat => False.elim (ordinary rfl)

/-! Comparisons return one bit. Signed comparisons use two's complement values. -/
def evalPred (pred : Pred) (a b : Value width) : Value 1 :=
  BitVec.ofBool <| match pred with
  | .eq => a == b
  | .ne => a != b
  | .ult => a.ult b
  | .ule => a.ule b
  | .ugt => b.ult a
  | .uge => b.ule a
  | .slt => a.slt b
  | .sle => a.sle b
  | .sgt => b.slt a
  | .sge => b.sle a

/-! These operations also serve consumers with explicit runtime widths. -/
def evalConcat (a : Value wa) (b : Value wb) : Value (wa + wb) := a.append b

def evalExtract (a : Value w) (lo count : Nat) : Value count := a.extractLsb' lo count

def evalReplicate (a : Value w) (count : Nat) : Value (w * count) := a.replicate count

def evalMux (c : Value 1) (yes no : α) : α := if c = 1 then yes else no

/-! A read outside the finite memory returns zero. -/
def memoryRead (memory : Fin depth → Value width) (address : Nat) : Value width :=
  if h : address < depth then memory ⟨address, h⟩ else 0

/-! A write changes one cell only when its address is valid and its enable is set. -/
def memoryWrite (memory : Fin depth → Value width) (address : Nat)
    (value : Value width) (enable : Value 1) : Fin depth → Value width :=
  fun index => if enable = 1 && index.val = address then value else memory index

end Silicon.Core.Semantics
