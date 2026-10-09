import Silicon.Core.Proof.MemModel

/-!
The examples include free words, full depth, and writes to the same address.
-/
namespace Silicon.Core.Test.MemModelCorrect

open MemModelProof

private def state (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) : Mlir.ModuleState :=
  ⟨fun _ name => if name = "silicon_reg_mem" then some (.array _ _ words) else none⟩

private def collision : Inputs ⟨12, 8, 1, 2⟩ :=
  ⟨fun _ => 5, fun _ => 5, fun w => if w = 0 then 7 else 9, fun _ => 1⟩

/-! A free tail can contain any values. Both ports write word 5; port 1 wins. -/
example (tail : Nat → BitVec 8) :
    let c : MemConfig := ⟨12, 8, 1, 2⟩
    let words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec 8 :=
      fun i => if i.val < 12 then 3 else tail i.val
    ∃ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) (state c words)
      (inputEnv c collision) vals ∧ vals "r0_data" = some (.bits 8 3) ∧
      ∃ nextWords : Fin (2 ^ Typed.addressWidth c.depth) → BitVec 8,
        (Mlir.nextState ⟨[.module (memModel c)]⟩ (memModel c) (state c words) vals).regs
          "silicon_reg_mem" = some (.array _ 8 nextWords) ∧ nextWords ⟨5, by decide⟩ = 9 := by
  intro c words
  have h := mem_model_correct c (fun _ => 3) words (state c words) collision
    (by rfl) (by intro i; have hi : i.val < 12 := i.isLt; simp only [words, ite_eq_left hi])
    (by constructor <;> intro i hi <;> change (5#4).toNat < 12 <;> decide)
  obtain ⟨⟨vals, hv⟩, correct⟩ := h
  obtain ⟨reads, nextWords, hn, ha⟩ := correct vals hv
  refine ⟨vals, hv, ?_, nextWords, hn, ?_⟩
  · exact reads 0 (by decide)
  · have h := ha ⟨5, by decide⟩
    exact h.trans (by rw [coreNext_eq]; dsimp only [c]; decide)

private def single : Inputs ⟨1, 4, 1, 1⟩ :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 9, fun _ => 1⟩

/-! Depth 1 uses two model words. The second word can hold any value. -/
example (freeWord : BitVec 4) :
    let c : MemConfig := ⟨1, 4, 1, 1⟩
    let words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec 4 :=
      fun i => if i.val = 0 then 3 else freeWord
    ∃ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) (state c words)
      (inputEnv c single) vals ∧ vals "r0_data" = some (.bits 4 3) ∧
      ∃ nextWords : Fin (2 ^ Typed.addressWidth c.depth) → BitVec 4,
        (Mlir.nextState ⟨[.module (memModel c)]⟩ (memModel c) (state c words) vals).regs
          "silicon_reg_mem" = some (.array _ 4 nextWords) ∧ nextWords ⟨0, by decide⟩ = 9 := by
  intro c words
  have h := mem_model_correct c (fun _ => 3) words (state c words) single
    (by rfl) (by
      intro i
      have hi : i.val < 1 := i.isLt
      have hz : i.val = 0 := by omega
      simp only [words, hz, ↓reduceIte])
    (by constructor <;> intro i hi <;> change (0#1).toNat < 1 <;> decide)
  obtain ⟨⟨vals, hv⟩, correct⟩ := h
  obtain ⟨reads, nextWords, hn, ha⟩ := correct vals hv
  refine ⟨vals, hv, ?_, nextWords, hn, ?_⟩
  · exact reads 0 (by decide)
  · have h := ha ⟨0, by decide⟩
    exact h.trans (by rw [coreNext_eq]; dsimp only [c]; decide)

private def full : Inputs ⟨16, 8, 1, 1⟩ :=
  ⟨fun _ => 15, fun _ => 15, fun _ => 9, fun _ => 1⟩

/-! Every address is valid at full depth, including the last word. -/
example :
    let c : MemConfig := ⟨16, 8, 1, 1⟩
    let words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec 8 := fun _ => 3
    ∃ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) (state c words)
      (inputEnv c full) vals ∧ vals "r0_data" = some (.bits 8 3) ∧
      ∃ nextWords : Fin (2 ^ Typed.addressWidth c.depth) → BitVec 8,
        (Mlir.nextState ⟨[.module (memModel c)]⟩ (memModel c) (state c words) vals).regs
          "silicon_reg_mem" = some (.array _ 8 nextWords) ∧ nextWords ⟨15, by decide⟩ = 9 := by
  intro c words
  have h := mem_model_correct c (fun _ => 3) words (state c words) full
    (by rfl) (by intro i; rfl)
    (by constructor <;> intro i hi <;> change (15#4).toNat < 16 <;> decide)
  obtain ⟨⟨vals, hv⟩, correct⟩ := h
  obtain ⟨reads, nextWords, hn, ha⟩ := correct vals hv
  refine ⟨vals, hv, ?_, nextWords, hn, ?_⟩
  · exact reads 0 (by decide)
  · have h := ha ⟨15, by decide⟩
    exact h.trans (by rw [coreNext_eq]; dsimp only [c]; decide)

#guard Typed.addressWidth 1 = 1
#guard 2 ^ Typed.addressWidth 16 = 16
#guard collision.coreNext (fun _ => 3) ⟨5, by decide⟩ = 9

end Silicon.Core.Test.MemModelCorrect
