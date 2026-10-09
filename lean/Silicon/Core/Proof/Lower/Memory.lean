import Silicon.Core.Proof.Lower.Expressions

/-!
The parent guards the data of each read and the enable of each write.
The model can receive every address of its array, including padding addresses.
-/
namespace Silicon.Core.LowerProof

open MemModelProof

def guardedInputs (input : Inputs c) : Inputs c :=
  { input with writeEnable := fun w =>
      input.writeEnable w &&& BitVec.ofBool ((input.writeAddr w).toNat < c.depth) }

theorem guarded_enable_inRange (input : Inputs c) (w : Nat)
    (h : (input.writeAddr w).toNat < c.depth) :
    (guardedInputs input).writeEnable w = input.writeEnable w := by
  simp only [guardedInputs, h, decide_true]
  change input.writeEnable w &&& BitVec.allOnes 1 = input.writeEnable w
  exact BitVec.and_allOnes

theorem guarded_stages_agree (c : MemConfig) (input : Inputs c) (words) (memory)
    (agree : Agrees c words memory) (n : Nat) :
    Agrees c (stages (guardedInputs input) words n) (stages input memory n) := by
  induction n with
  | zero => exact agree
  | succ n ih =>
    intro i
    change (if (guardedInputs input).writeEnable n = 1 &&
        i.val = (input.writeAddr n).toNat then input.writeData n
      else stages (guardedInputs input) words n _) =
      (if input.writeEnable n = 1 && i.val = (input.writeAddr n).toNat then input.writeData n
       else stages input memory n i)
    by_cases inside : (input.writeAddr n).toNat < c.depth
    · rw [guarded_enable_inRange input n inside]
      rw [ih i]
    · have different : i.val ≠ (input.writeAddr n).toNat := by
        have hi := i.isLt
        omega
      simp only [different, decide_false,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact ih i

end Silicon.Core.LowerProof
