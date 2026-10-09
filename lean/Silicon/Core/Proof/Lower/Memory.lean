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

theorem guarded_enable_outside (input : Inputs c) (w : Nat)
    (h : ¬ (input.writeAddr w).toNat < c.depth) :
    (guardedInputs input).writeEnable w = 0 := by
  simp [guardedInputs, h]

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

theorem guarded_stages_padding (c : MemConfig) (input : Inputs c)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) (n : Nat)
    (i : Fin (2 ^ Typed.addressWidth c.depth)) (outside : c.depth ≤ i.val) :
    stages (guardedInputs input) words n i = words i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stages]
    by_cases inside : (input.writeAddr n).toNat < c.depth
    · have different : i.val ≠ (input.writeAddr n).toNat := by omega
      simpa [guardedInputs, Semantics.memoryWrite, different] using ih
    · rw [guarded_enable_outside input n inside]
      simpa [Semantics.memoryWrite] using ih

theorem mem_model_guarded_correct (c : MemConfig)
    (memory : Fin c.depth → BitVec c.width)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (σ : Mlir.ModuleState) (input : Inputs c)
    (state : σ.regs "silicon_reg_mem" = some (.array _ _ words))
    (agree : Agrees c words memory) :
    (∃ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) σ
      (inputEnv c (guardedInputs input)) vals) ∧
    ∀ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) σ
      (inputEnv c (guardedInputs input)) vals →
      (∀ r < c.reads,
        (if (input.readAddr r).toNat < c.depth then vals s!"r{r}_data"
         else some (.bits c.width 0)) =
          some (.bits c.width (Semantics.memoryRead memory (input.readAddr r).toNat))) ∧
      ∃ nextWords, (Mlir.nextState ⟨[.module (memModel c)]⟩ (memModel c) σ vals).regs
        "silicon_reg_mem" = some (.array _ _ nextWords) ∧
        Agrees c nextWords (input.coreNext memory) ∧
        ∀ i, c.depth ≤ i.val → nextWords i = words i := by
  refine ⟨⟨values c words (guardedInputs input),
    solution c words (guardedInputs input) σ state⟩, ?_⟩
  intro vals solved
  have root : ∃ children, Mlir.LocalSolution ⟨[.module (memModel c)]⟩ (memModel c)
      σ.regs (inputEnv c (guardedInputs input)) vals children := by
    obtain ⟨all, same, h⟩ := solved
    exact ⟨fun name => all [name], same ▸ h.1⟩
  obtain ⟨children, equations⟩ := root
  constructor
  · intro r hr
    have read := reads_value c words (guardedInputs input) equations state r hr
    change vals s!"r{r}_data" =
      some (.bits c.width (Semantics.memoryRead words (input.readAddr r).toNat)) at read
    rw [read]
    have guard := guarded_read c words memory agree (input.readAddr r)
    split <;> simp_all
  · refine ⟨stages (guardedInputs input) words c.writes,
      next_value c words (guardedInputs input) σ vals solved state, ?_, ?_⟩
    · rw [coreNext_eq]
      exact guarded_stages_agree c input words memory agree c.writes
    · exact guarded_stages_padding c input words c.writes

end Silicon.Core.LowerProof
