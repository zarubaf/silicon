import Silicon.Core.Semantics

/-! Checked designs test cycle outputs and state through the public hierarchy interface. -/
namespace Silicon.Core.Test.Step

open Core.Semantics

private def pos : Pos := ⟨1, 1, []⟩
private def counterRaw : Core.Module := ⟨pos, "counter",
  [⟨pos, .input, "clk", .clock⟩, ⟨pos, .input, "rst", .bits 1⟩,
    ⟨pos, .output, "q", .bits 8⟩],
  [.reg pos "r" 8 "clk" (some ⟨.sync, .ref pos "rst", .const pos 8 17⟩),
    .next pos "r" (.bin pos .add (.ref pos "r") (.const pos 8 1)),
    .assign pos "q" (.ref pos "r")]⟩

private def raw : Core.Design := ⟨"counter", [.module counterRaw], pos⟩
private def ctx : Typed.Ctx := Typed.context raw counterRaw
private def reg : Typed.Equation ctx (Typed.portsOf raw) :=
  .reg 0 pos "r" 8 "clk" rfl
    (some ⟨.sync, .ref pos (.name "rst") rfl, .const pos 8 17⟩) 1 pos
    (.bin pos .add (by decide) (.ref pos (.name "r") rfl) (.const pos 8 1))
private def assign : Typed.Equation ctx (Typed.portsOf raw) :=
  .assign 2 pos "q" 8 rfl (.ref pos (.name "r") rfl)

private def counter : Typed.Module where
  pos := pos
  name := "counter"
  ports := counterRaw.ports
  ctx := ctx
  interfaces := Typed.portsOf raw
  body := [reg, assign]
  children := Typed.designDeps raw raw.depsFuel
  ranks := [(.name "q", 1)]
  acyclic := by
    simp [Typed.equationsErase, reg, assign, List.mergeSort, Typed.Ranked,
      Deps.graph, Deps.equations, Deps.reads, Typed.rank, Typed.Equation.parts,
      Typed.Stmt.erase, Typed.Expr.erase]
    intro _
    rfl
  context_eq := by
    simp [Typed.equationsErase, reg, assign, List.mergeSort, Typed.Equation.parts,
      Typed.Stmt.erase, Typed.Expr.erase]
    rfl

private theorem counter_erase : counter.erase = counterRaw := by
  simp [counter, Typed.Module.erase, Typed.equationsErase, reg, assign,
    List.mergeSort, Typed.Equation.parts, Typed.Stmt.erase, Typed.Expr.erase,
    Typed.Reset.erase, counterRaw]

private def counterTyped : Typed.Design where
  top := "counter"
  itemNames := ["counter"]
  externs := []
  bodies := [counter]
  topPos := pos
  hierarchy := by simp [counter_erase, Typed.ordered, Typed.childNames, counterRaw]
  environments := by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have erased : Typed.assembleDesign "counter" ["counter"] [] [counter] pos = raw := by
        simp [Typed.assembleDesign, counter, Typed.Module.erase, Typed.equationsErase,
          reg, assign, List.mergeSort, Typed.Equation.parts, Typed.Stmt.erase,
          Typed.Expr.erase, Typed.Reset.erase, raw, counterRaw]
      rw [erased]
      exact ⟨rfl, rfl, by rw [counter_erase]; exact List.mem_cons_self ..⟩
    · contradiction

private theorem counter_wf : WellFormed counterTyped.erase := by
  have hn := (Check.e002_spec raw).mp (by rfl)
  have hr := (Check.e003_spec raw).mp (by rfl)
  have erased : counterTyped.erase = raw := by
    change Typed.assembleDesign "counter" ["counter"] [] [counter] pos = raw
    simp only [Typed.assembleDesign, List.filterMap_cons, List.filterMap_nil,
      List.find?_cons, show (counter.name == "counter") = true from rfl,
      counter_erase]
    rfl
  rw [erased]
  refine ⟨hn, hr, (Check.e004_spec raw hn hr
      ((Check.e009_spec raw).mp rfl) ((Check.e011_spec raw).mp rfl)).mp (by rfl),
    (Check.e005_spec raw).mp (by rfl), (Check.e006_spec raw).mp (by rfl),
    (Check.e007_spec raw).mp (by rfl), ?_, (Check.e009_spec raw).mp (by rfl),
    ?_, (Check.e011_spec raw).mp (by rfl), (Check.e012_spec raw).mp (by rfl),
    (Check.e013_spec raw).mp (by rfl)⟩
  · intro m hm
    change m ∈ [counterRaw] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨counter.ranks, ?_⟩
      have h := counter.acyclic
      change Typed.Ranked (Deps.graph counter.erase counter.children) counter.ranks at h
      rw [counter_erase] at h
      exact h
    · contradiction
  · refine ⟨[], ?_⟩
    change ∀ row ∈ ([(Deps.Node.name "counter", [])] : Typed.Graph), ∀ dep ∈ row.2, _
    simp

private def counterDesign : CertifiedDesign := ⟨counterTyped, counter_wf⟩

theorem counter_checked : ∃ typed, check counterTyped.erase = .ok typed :=
  check_complete counterTyped.erase counter_wf

private theorem counter_member : counter ∈ counterDesign.design.bodies := by
  exact List.mem_cons_self ..

private def noExterns : Env counterDesign.design := fun e h => by
  change e ∈ [] at h
  contradiction

private def counterState (value : BitVec 8) :
    State counterDesign noExterns counter counter_member := fun ⟨eq, member⟩ => by
  cases eq with
  | reg index pos name width clock target reset ni np next => exact BitVec.ofNat width value.toNat
  | let_ | assign => exact ()
  | mem index pos name width depth clock target writes => exact fun _ => BitVec.ofNat width 0
  | inst =>
    change _ ∈ [reg, assign] at member
    exact False.elim (by
      rcases List.mem_cons.mp member with h | h
      · cases h
      · rcases List.mem_cons.mp h with h | h <;> cases h)

private def counterInput (reset : BitVec 1) : Input counter := fun p =>
  match p.val.ty with
  | .clock => ()
  | .bits width => BitVec.ofNat width reset.toNat

private def counterQ : PortRef counter.ports .output :=
  ⟨⟨pos, .output, "q", .bits 8⟩, by decide, rfl⟩

private def regRef : EquationRef counter := ⟨reg, List.mem_cons_self ..⟩

private theorem counter_output (state : State counterDesign noExterns counter counter_member)
    (input : Input counter) :
    (step counterDesign noExterns counter counter_member state input).2 counterQ =
      state regRef := by
  obtain ⟨values, hv, unique⟩ :=
    solution_unique counterDesign noExterns counter counter_member state input
  have solved : solution counterDesign noExterns counter counter_member state input = values :=
    unique _ (localSolution_isSolution counterDesign counter counter_member
      (designChildren counterDesign noExterns counter counter_member) state input)
  change solution counterDesign noExterns counter counter_member state input (.name "q") 8 rfl = _
  rw [solved]
  have q := hv (.name "q") 8 rfl
    (.assign 2 pos "q" 8 rfl (.ref pos (.name "r") rfl) (by
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have r := hv (.name "r") 8 rfl
    (.reg 0 pos "r" 8 "clk" rfl
      (some ⟨.sync, .ref pos (.name "rst") rfl, .const pos 8 17⟩) 1 pos
      (.bin pos .add (by decide) (.ref pos (.name "r") rfl) (.const pos 8 1))
      (List.mem_cons_self ..))
  exact q.trans r

theorem counter_current_output :
    (step counterDesign noExterns counter counter_member
      (counterState (5#8)) (counterInput (1#1))).2 counterQ = 5#8 :=
  counter_output _ _

theorem counter_reset_output :
    (step counterDesign noExterns counter counter_member
      (step counterDesign noExterns counter counter_member
        (counterState (5#8)) (counterInput (1#1))).1 (counterInput (0#1))).2 counterQ =
      17#8 := by
  rw [counter_output]
  have reset := localSolution_isSolution counterDesign counter counter_member
    (designChildren counterDesign noExterns counter counter_member)
    (counterState (5#8)) (counterInput (1#1)) (.name "rst") 1 rfl
    (.input ⟨pos, .input, "rst", .bits 1⟩
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl rfl)
  simp only [step, stepWithValues, localStepWithValues, nextLocalState, regRef, reg]
  change (if solution counterDesign noExterns counter counter_member
    (counterState (5#8)) (counterInput (1#1)) (.name "rst") 1 rfl = 1#1
    then 17#8 else
      solution counterDesign noExterns counter counter_member
        (counterState (5#8)) (counterInput (1#1)) (.name "r") 8 rfl + 1#8) = _
  rw [show solution counterDesign noExterns counter counter_member
    (counterState (5#8)) (counterInput (1#1)) (.name "rst") 1 rfl = 1#1 from reset]
  rfl

theorem counter_increment_output :
    (step counterDesign noExterns counter counter_member
      (step counterDesign noExterns counter counter_member
        (counterState (5#8)) (counterInput (0#1))).1 (counterInput (0#1))).2 counterQ =
      6#8 := by
  rw [counter_output]
  have values := localSolution_isSolution counterDesign counter counter_member
    (designChildren counterDesign noExterns counter counter_member)
    (counterState (5#8)) (counterInput (0#1))
  have reset := values (.name "rst") 1 rfl
    (.input ⟨pos, .input, "rst", .bits 1⟩
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl rfl)
  have reg := values (.name "r") 8 rfl
    (.reg 0 pos "r" 8 "clk" rfl
      (some ⟨.sync, .ref pos (.name "rst") rfl, .const pos 8 17⟩) 1 pos
      (.bin pos .add (by decide) (.ref pos (.name "r") rfl) (.const pos 8 1))
      (List.mem_cons_self ..))
  simp only [step, stepWithValues, localStepWithValues, nextLocalState, regRef, Core.Test.Step.reg]
  change (if solution counterDesign noExterns counter counter_member
    (counterState (5#8)) (counterInput (0#1)) (.name "rst") 1 rfl = 1#1
    then 17#8 else solution counterDesign noExterns counter counter_member
      (counterState (5#8)) (counterInput (0#1)) (.name "r") 8 rfl + 1#8) = _
  rw [show solution counterDesign noExterns counter counter_member
    (counterState (5#8)) (counterInput (0#1)) (.name "rst") 1 rfl = 0#1 from reset]
  rw [show solution counterDesign noExterns counter counter_member
    (counterState (5#8)) (counterInput (0#1)) (.name "r") 8 rfl = 5#8 from reg]
  decide

end Silicon.Core.Test.Step
