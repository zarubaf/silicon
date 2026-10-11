-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics

/-! A two-level design exposes its child's output and admits an explicit start state. -/
namespace Silicon.Core.Test.Hierarchy

open Core.Semantics

private def pos : Pos := ⟨1, 1, []⟩
private def q : Port := ⟨pos, .output, "q", .bits 8⟩
private def leafRaw : Core.Module :=
  ⟨pos, "leaf", [q], [.assign pos "q" (.const pos 8 42)]⟩
private def topRaw : Core.Module :=
  ⟨pos, "top", [q], [.inst pos "u" "leaf" [], .assign pos "q" (.port pos "u" "q")]⟩
private def raw : Core.Design := ⟨"top", [.module topRaw, .module leafRaw], pos⟩
private def leafCtx := Typed.context raw leafRaw
private def topCtx := Typed.context raw topRaw
private def leafAssign : Typed.Equation leafCtx (Typed.portsOf raw) :=
  .assign 0 pos "q" 8 rfl (.const pos 8 42)
private def inst : Typed.Equation topCtx (Typed.portsOf raw) := .inst 0 pos "u" "leaf" []
private def topAssign : Typed.Equation topCtx (Typed.portsOf raw) :=
  .assign 1 pos "q" 8 rfl (.ref pos (.port "u" "q") rfl)

private def leaf : Typed.Module where
  pos := pos
  name := "leaf"
  ports := [q]
  ctx := leafCtx
  interfaces := Typed.portsOf raw
  body := [leafAssign]
  children := Typed.designDeps raw raw.depsFuel
  ranks := [(.name "q", 1)]
  acyclic := by
    simp [Typed.equationsErase, leafAssign, Typed.Equation.parts, Typed.Stmt.erase,
      Typed.Expr.erase, Deps.graph, Deps.equations, Deps.reads, Typed.Ranked]
  context_eq := by
    simp [Typed.equationsErase, leafAssign, Typed.Equation.parts, Typed.Stmt.erase,
      Typed.Expr.erase]
    rfl

private theorem leaf_erase : leaf.erase = leafRaw := by
  simp [leaf, Typed.Module.erase, Typed.equationsErase, leafAssign,
    Typed.Equation.parts, Typed.Stmt.erase, Typed.Expr.erase, leafRaw]

private def top : Typed.Module where
  pos := pos
  name := "top"
  ports := [q]
  ctx := topCtx
  interfaces := Typed.portsOf raw
  body := [inst, topAssign]
  children := Typed.designDeps raw raw.depsFuel
  ranks := [(.port "u" "q", 1), (.name "q", 2)]
  acyclic := by
    simp [Typed.equationsErase, inst, topAssign, Typed.Equation.parts,
      List.mergeSort, Typed.Stmt.erase, Typed.Expr.erase]
    change Typed.Ranked [(.port "u" "q", []), (.name "q", [.port "u" "q"])] _
    intro row hr dep hd
    rcases List.mem_cons.mp hr with rfl | hr
    · cases hd
    · rcases List.mem_cons.mp hr with rfl | hr
      · rcases List.mem_cons.mp hd with rfl | hd
        · decide
        · contradiction
      · contradiction
  context_eq := by
    simp [Typed.equationsErase, inst, topAssign, List.mergeSort, Typed.Equation.parts,
      Typed.Stmt.erase, Typed.Expr.erase]
    rfl

private theorem top_erase : top.erase = topRaw := by
  simp [top, Typed.Module.erase, Typed.equationsErase, inst, topAssign,
    List.mergeSort, Typed.Equation.parts, Typed.Stmt.erase, Typed.Expr.erase, topRaw]

private theorem assembled : Typed.assembleDesign "top" ["top", "leaf"] [] [leaf, top] pos =
    raw := by
  simp only [Typed.assembleDesign, List.filterMap_cons, List.filterMap_nil, List.find?_cons,
    show (leaf.name == "top") = false from rfl,
    show (top.name == "top") = true from rfl,
    show (leaf.name == "leaf") = true from rfl,
    top_erase, leaf_erase]
  rfl

private def typed : Typed.Design where
  top := "top"
  itemNames := ["top", "leaf"]
  externs := []
  bodies := [leaf, top]
  topPos := pos
  hierarchy := by simp [top_erase, leaf_erase, Typed.ordered, Typed.childNames, leafRaw, topRaw]
  environments := by
    intro m hm
    rw [assembled]
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨rfl, rfl, ?_⟩
      rw [leaf_erase]
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases List.mem_cons.mp hm with rfl | hm
      · refine ⟨rfl, rfl, ?_⟩
        rw [top_erase]
        exact List.mem_cons_self ..
      · contradiction

private theorem wf : WellFormed typed.erase := by
  change WellFormed (Typed.assembleDesign "top" ["top", "leaf"] [] [leaf, top] pos)
  rw [assembled]
  have hn := (Check.e002_spec raw).mp (by cbv)
  have hr := (Check.e003_spec raw).mp (by rfl)
  have hc := (Check.e009_spec raw).mp (by rfl)
  have hi := (Check.e011_spec raw).mp (by rfl)
  refine ⟨hn, hr, (Check.e004_spec raw hn hr hc hi).mp (by rfl),
    (Check.e005_spec raw).mp (by rfl), (Check.e006_spec raw).mp (by rfl),
    (Check.e007_spec raw).mp (by rfl), ?_, hc, ?_, hi,
    (Check.e012_spec raw).mp (by rfl), (Check.e013_spec raw).mp (by rfl)⟩
  · intro m hm
    change m ∈ [topRaw, leafRaw] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨top.ranks, ?_⟩
      have h := top.acyclic
      change Typed.Ranked (Deps.graph top.erase top.children) top.ranks at h
      rw [top_erase] at h
      exact h
    · rcases List.mem_cons.mp hm with rfl | hm
      · refine ⟨leaf.ranks, ?_⟩
        have h := leaf.acyclic
        change Typed.Ranked (Deps.graph leaf.erase leaf.children) leaf.ranks at h
        rw [leaf_erase] at h
        exact h
      · contradiction
  · refine ⟨[(.name "top", 2), (.name "leaf", 1)], ?_⟩
    change Typed.Ranked [(.name "top", [.name "leaf"]), (.name "leaf", [])] _
    intro row hr dep hd
    rcases List.mem_cons.mp hr with rfl | hr
    · rcases List.mem_cons.mp hd with rfl | hd
      · decide
      · contradiction
    · rcases List.mem_cons.mp hr with rfl | hr <;> contradiction

private def design : CertifiedDesign := ⟨typed, wf⟩
private def env : Env typed := fun _ h => nomatch h
private theorem leaf_member : leaf ∈ typed.bodies := List.mem_cons_self ..
private theorem top_member : top ∈ typed.bodies := List.mem_cons_of_mem _ (List.mem_cons_self ..)
private def leafQ : PortRef leaf.ports .output := ⟨q, List.mem_cons_self .., rfl⟩
private def topQ : PortRef top.ports .output := ⟨q, List.mem_cons_self .., rfl⟩
private def instRef : EquationRef top := ⟨inst, List.mem_cons_self ..⟩

private theorem leaf_output (state : State design env leaf leaf_member) (input : Input leaf) :
    (step design env leaf leaf_member state input).2 leafQ = 42#8 := by
  have h := localSolution_isSolution design leaf leaf_member
    (designChildren design env leaf leaf_member) state input (.name "q") 8 rfl
    (.assign 0 pos "q" 8 rfl (.const pos 8 42) (List.mem_cons_self ..))
  exact h

private def leafState : State design env leaf leaf_member := fun ⟨eq, member⟩ => by
  have same : eq = leafAssign := (List.mem_singleton.mp member)
  subst eq
  exact ()

private theorem inst_state :
    CellState top inst (designChildren design env top top_member instRef) =
      State design env leaf leaf_member :=
  State_inst_module design env top top_member 0 pos "u" "leaf" []
    (List.mem_cons_self ..) leaf rfl

private def start : State design env top top_member := fun ⟨eq, member⟩ => by
  cases eq with
  | assign => exact ()
  | inst index p name child inputs =>
    have same : Typed.Equation.inst index p name child inputs = inst := by
      rcases List.mem_cons.mp member with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h <;> cases h
    cases same
    exact cast inst_state.symm leafState
  | let_ | reg | mem =>
    exact False.elim (by
      rcases List.mem_cons.mp member with h | h
      · cases h
      · rcases List.mem_cons.mp h with h | h <;> cases h)

private def input : Input top := fun ⟨p, member, dir⟩ => by
  have same : p = q := List.mem_singleton.mp member
  subst p
  contradiction

theorem hierarchy_checked : ∃ result, check typed.erase = .ok result :=
  check_complete typed.erase wf

theorem hierarchy_output :
    (step design env top top_member start input).2 topQ = 42#8 := by
  have values := localSolution_isSolution design top top_member
    (designChildren design env top top_member) start input
  have out := values (.name "q") 8 rfl
    (.assign 1 pos "q" 8 rfl (.ref pos (.port "u" "q") rfl)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have child := values (.port "u" "q") 8 rfl
    (.inst 0 pos "u" "leaf" [] (List.mem_cons_self ..) q (List.mem_cons_self ..) rfl rfl)
  change solution design env top top_member start input (.name "q") 8 rfl = _
  apply out.trans
  apply child.trans
  have component := designChildren_inst_module design env top top_member
    0 pos "u" "leaf" [] (List.mem_cons_self ..) leaf (by rfl)
  have constant (model : ChildModel top inst)
      (equal : model = moduleChild design.design design.wellFormed top leaf
        top_member leaf_member "leaf" rfl
        (localComponent design leaf leaf_member (designChildren design env leaf leaf_member))) :
      ∀ s i, model.out s i leafQ = 42#8 := by
    subst model
    exact leaf_output
  exact constant _ component _ _

end Silicon.Core.Test.Hierarchy
