import Silicon.Core.Semantics

/-! Primitive tests fix the boundary rules for shifts, signs, and memory addresses. -/
namespace Silicon.Core.Test.Semantics

open Core.Semantics

/-! Shifts use the full unsigned amount, including amounts at or above the width. -/
example : evalOp .shl (by decide) (1#8) (8#8) = 0#8 := by decide
example : evalOp .shl (by decide) (1#8) (255#8) = 0#8 := by decide
example : evalOp .shru (by decide) (255#8) (8#8) = 0#8 := by decide
example : evalOp .shru (by decide) (255#8) (255#8) = 0#8 := by decide
example : evalOp .shrs (by decide) (127#8) (8#8) = 0#8 := by decide
example : evalOp .shrs (by decide) (127#8) (255#8) = 0#8 := by decide
example : evalOp .shrs (by decide) (128#8) (8#8) = 255#8 := by decide
example : evalOp .shrs (by decide) (128#8) (255#8) = 255#8 := by decide
example : evalOp .shl (by decide) (3#8) (2#8) = 12#8 := by decide
example : evalOp .shru (by decide) (128#8) (2#8) = 32#8 := by decide
example : evalOp .shrs (by decide) (128#8) (2#8) = 224#8 := by decide

/-! Arithmetic wraps, and signed comparison reads the high bit as a sign bit. -/
example : evalOp .add (by decide) (255#8) (1#8) = 0#8 := by decide
example : evalOp .sub (by decide) (0#8) (1#8) = 255#8 := by decide
example : evalOp .mul (by decide) (128#8) (2#8) = 0#8 := by decide
example : evalOp .and (by decide) (10#4) (12#4) = 8#4 := by decide
example : evalOp .or (by decide) (10#4) (12#4) = 14#4 := by decide
example : evalOp .xor (by decide) (10#4) (12#4) = 6#4 := by decide
example : evalPred .slt (2#2) (1#2) = 1#1 := by decide
example : evalPred .slt (255#8) (0#8) = 1#1 := by decide
example : evalPred .slt (0#8) (255#8) = 0#1 := by decide
example : evalPred .ult (255#8) (0#8) = 0#1 := by decide

/-! Concatenation puts the left operand in the high bits; extraction counts from zero. -/
example : BitVec.append (10#4) (3#4) = 163#8 := by decide
example : BitVec.extractLsb' 4 4 (163#8) = 10#4 := by decide
example : BitVec.extractLsb' 0 4 (163#8) = 3#4 := by decide

private def memory : Fin 3 → BitVec 8 := fun i => BitVec.ofNat 8 (i.val + 10)

/-! Invalid reads return zero. Invalid or disabled writes preserve each cell. -/
example : memoryRead memory 2 = 12#8 := by decide
example : memoryRead memory 3 = 0#8 := by decide
example : memoryRead memory 255 = 0#8 := by decide
example : ∀ i, memoryWrite memory 3 (42#8) (1#1) i = memory i := by decide
example : ∀ i, memoryWrite memory 255 (42#8) (1#1) i = memory i := by decide
example : ∀ i, memoryWrite memory 1 (42#8) (0#1) i = memory i := by decide
example : memoryWrite memory 1 (42#8) (1#1) ⟨1, by decide⟩ = 42#8 := by decide
example : memoryWrite memory 1 (42#8) (1#1) ⟨2, by decide⟩ = 12#8 := by decide

private def noValues : Valuation [] := fun _ _ h => nomatch h
private def noMemories : Memories [] := fun _ _ _ h => nomatch h
private def const (width value : Nat) : Typed.Expr [] (.bits width) :=
  .const ⟨1, 1, []⟩ width value

/-! Typed forms use the same high-bit order and low-bit offsets as the core operations. -/
example : evalExpr noValues noMemories
    (.concat ⟨1, 1, []⟩ (const 4 10) (const 4 3) (by decide)) = 163#8 := by decide
example : evalExpr noValues noMemories
    (.extract ⟨1, 1, []⟩ (const 8 163) 4 4 (by decide)) = 10#4 := by decide
example : evalExpr noValues noMemories
    (.extract ⟨1, 1, []⟩ (const 8 163) 0 4 (by decide)) = 3#4 := by decide
example : evalExpr noValues noMemories
    (.replicate ⟨1, 1, []⟩ (const 2 2) 3 (by decide)) = 42#6 := by decide
example : evalExpr noValues noMemories
    (.mux ⟨1, 1, []⟩ (const 1 1) (const 8 17) (const 8 42)) = 17#8 := by decide
example : evalExpr noValues noMemories
    (.mux ⟨1, 1, []⟩ (const 1 0) (const 8 17) (const 8 42)) = 42#8 := by decide

/-! A reset wins over the next value; a clear reset leaves that value in effect. -/
example : nextRegister noValues noMemories
    (some ⟨.sync, const 1 1, const 8 17⟩) (const 8 42) = 17#8 := by decide
example : nextRegister noValues noMemories
    (some ⟨.sync, const 1 0, const 8 17⟩) (const 8 42) = 42#8 := by decide
example : nextRegister noValues noMemories none (const 8 42) = 42#8 := by decide

private def write (port address value enable : Nat) : Typed.Write [] 8 3 :=
  ⟨port, ⟨1, 1, []⟩, port, const 2 address, const 8 value, const 1 enable⟩

/-! Write priority follows the port number even when the source order differs. -/
example : nextMemory noValues noMemories memory
    [write 2 1 42 1, write 0 1 10 1, write 1 1 20 1] ⟨1, by decide⟩ = 42#8 := by
  simp +decide [nextMemory, List.mergeSort, write]
example : nextMemory noValues noMemories memory
    [write 2 1 42 0, write 0 1 10 1, write 1 1 20 1] ⟨1, by decide⟩ = 20#8 := by
  simp +decide [nextMemory, List.mergeSort, write]
example : nextMemory noValues noMemories memory
    [write 2 3 42 1, write 0 1 10 1, write 1 1 20 1] ⟨1, by decide⟩ = 20#8 := by
  simp +decide [nextMemory, List.mergeSort, write]

end Silicon.Core.Test.Semantics
