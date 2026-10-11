-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleMemory

/-!
The MLIR next state of a solution corresponds to the core next state. Registers take their
reset or next value. Memories apply the guarded writes. Instances follow their children.
-/
namespace Silicon.Core.LowerProof

open Semantics

/-- A named cell belongs to one register, memory, or instance equation. -/
theorem namedState_cases (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (name : String) (rest : List String) (cell : NamedCell)
    (h : namedState d env noExterns m hm state (name :: rest) = some cell) :
    ∃ eq ∈ m.body, equationName eq = name ∧ match eq with
      | .let_ .. | .assign .. => False
      | .reg .. | .mem .. => rest = []
      | .inst .. => True := by
  rw [namedState] at h
  split at h
  · cases h
  · rename_i equation he
    refine ⟨equation, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, ?_⟩
    revert h
    generalize List.mem_of_find?_eq_some he = member
    cases equation <;> simp
    all_goals intros; assumption

theorem namedState_nil (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) : namedState d env noExterns m hm state [] = none := by
  rw [namedState]

theorem entry_names_nodup (d : Mlir.Design) (M : Mlir.Module) (wf : M.WellFormed d) :
    (M.body.flatMap Prod.fst).Nodup := by
  have defs := wf.2.1
  unfold Mlir.Module.definitions at defs
  rw [List.map_append] at defs
  have right := (List.nodup_append.mp defs).2.1
  rw [List.map_flatMap] at right
  have same : M.body.flatMap (fun entry => (entry.1.zip entry.2.resultTypes).map Prod.fst) =
      M.body.flatMap Prod.fst := by
    simp only [List.flatMap]
    congr 1
    apply List.map_congr_left
    intro entry he
    exact List.map_fst_zip (Nat.le_of_eq (wf.2.2.2.1 entry he).1)
  rw [← same]
  exact right

theorem find_entry (body : List (List String × Mlir.Op)) (unique : (body.flatMap Prod.fst).Nodup)
    (entry : List String × Mlir.Op) (he : entry ∈ body) (y : String) (named : entry.1 = [y]) :
    body.find? (fun e => e.1 == [y]) = some entry := by
  induction body with
  | nil => cases he
  | cons first rest ih =>
    rw [List.flatMap_cons] at unique
    rcases List.mem_cons.mp he with rfl | he
    · simp [named]
    · have ne : first.1 ≠ [y] := by
        intro eq
        rw [eq] at unique
        exact (List.nodup_cons.mp unique).1 (List.mem_flatMap.mpr ⟨entry, he, by simp [named]⟩)
      rw [List.find?_cons, show (first.1 == [y]) = false from beq_eq_false_iff_ne.mpr ne]
      exact ih (List.nodup_append.mp unique).2.1 he

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)

include h hm in
theorem next_statement_unique (np np' : Pos) (n : String) (w w' : Nat) (target target')
    (e : Typed.Expr m.ctx (.bits w)) (e' : Typed.Expr m.ctx (.bits w'))
    (hs : Typed.Stmt.next np n w target e ∈ Lower.statements m)
    (hs' : Typed.Stmt.next np' n w' target' e' ∈ Lower.statements m) :
    w' = w ∧ HEq e' e := by
  obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
  obtain ⟨eq', he', part', hp', same'⟩ := (statement_of_eq m _).mp hs'
  cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  all_goals try (rcases hp with rfl | rfl <;> cases same)
  all_goals try (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases same)
  all_goals try (subst hp; cases same)
  cases eq' <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp'
  all_goals try (rcases hp' with rfl | rfl <;> cases same')
  all_goals try (rcases hp' with rfl | ⟨_, _, rfl⟩ <;> cases same')
  all_goals try (subst hp'; cases same')
  have f := find_equation (certified raw t h) m hm _ he
  have f' := find_equation (certified raw t h) m hm _ he'
  simp only [equationName] at f f'
  rw [f] at f'
  cases f'
  exact ⟨rfl, HEq.rfl⟩

include h hm in
theorem reg_statement_unique (p p' : Pos) (n : String) (w w' : Nat) (clk clk' : String)
    (r : Option (Typed.Reset m.ctx w)) (r' : Option (Typed.Reset m.ctx w'))
    (hs : Typed.Stmt.reg p n w clk r ∈ Lower.statements m)
    (hs' : Typed.Stmt.reg p' n w' clk' r' ∈ Lower.statements m) :
    w' = w ∧ HEq r' r := by
  obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
  obtain ⟨eq', he', part', hp', same'⟩ := (statement_of_eq m _).mp hs'
  cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  all_goals try (rcases hp with rfl | rfl <;> cases same)
  all_goals try (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases same)
  all_goals try (subst hp; cases same)
  cases eq' <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp'
  all_goals try (rcases hp' with rfl | rfl <;> cases same')
  all_goals try (rcases hp' with rfl | ⟨_, _, rfl⟩ <;> cases same')
  all_goals try (subst hp'; cases same')
  have f := find_equation (certified raw t h) m hm _ he
  have f' := find_equation (certified raw t h) m hm _ he'
  simp only [equationName] at f f'
  rw [f] at f'
  cases f'
  exact ⟨rfl, HEq.rfl⟩

omit raw t h noExterns hm in
theorem read_has {d : Mlir.Design} {state inputs V : Mlir.Env} {children : String → Mlir.Env}
    (hv : Mlir.LocalSolution d (Lower.module m).1 state inputs V children) (x : String)
    (ty : Mlir.Ty) (has : Has m x ty) : ∃ v, (V ∘ rename m) x = some v ∧ v.ty = ty :=
  local_types hv _ _ (mem_of_lookup has)

variable (env : Env (certified raw t h).design)

theorem next_register_value (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ)
    (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (i : Nat) (p : Pos) (n : String) (w : Nat) (clk : String) (target) (reset)
    (ni : Nat) (np : Pos) (next : Typed.Expr m.ctx (.bits w))
    (member : Typed.Equation.reg i p n w clk target reset ni np next ∈ m.body) :
    (Mlir.nextHierarchyState ((lower t).withModels (memoryConfigs t)) (Lower.module m).1
      all).cells []
      (regName n) = some (.bits w (nextRegister (readBack m (all []))
        (stateMemories m (designChildren (certified raw t h) env m hm) s) reset next)) := by
  let MU := readMeaning raw t h noExterns m hm env s σ corr inputs all hv
  obtain ⟨nextName, hnext, entry⟩ := register_entry_body m i p n w clk target reset ni np next
    member
  have wf := body_wellFormed raw t h noExterns m hm
  have fe := find_entry _ (entry_names_nodup _ _ wf) _ entry _ rfl
  simp only [Mlir.nextHierarchyState, Mlir.Module.atPath, Option.bind_eq_bind,
    Option.bind_some, fe]
  rw [substitute_nextValue]
  have good := (MU.step_statements (Lower.statements m) (Lower.statements m) (fun _ h => h)
    (fun x hx => stmt_legal raw t h m hm x hx) {}).2 (Grows.refl _)
  have hs := statement_of_part m _ member (ni, .next np n w target next) (by
    simp [Typed.Equation.parts])
  have hsr := statement_of_part m _ member (i, .reg p n w clk reset) (by
    simp [Typed.Equation.parts])
  rcases good.2.2.1 _ (mem_of_lookup hnext) with absent | ⟨np', w', target', e, hs', value⟩
  · cases absent
  obtain ⟨same, heq⟩ := next_statement_unique raw t h m hm np np' n w w' target target' next e
    hs hs'
  subst w'
  have heq := eq_of_heq heq
  subst e
  obtain ⟨s', grows⟩ := presence m _ hsr
  obtain ⟨opt₀, pushed⟩ : ∃ opt₀, (n, opt₀) ∈
      (Lower.statement (ports := m.interfaces) (Lower.registers m) (.reg p n w clk reset)
        s').2.resets := ⟨_, List.mem_cons_self ..⟩
  obtain ⟨opt, hopt⟩ := lookup_some_of_mem (grows.resets.subset pushed)
  rcases good.2.2.2 _ (mem_of_lookup hopt) with absent | ⟨p'', w'', clk'', r, hs'', resets⟩
  · cases absent
  obtain ⟨same, heq⟩ := reg_statement_unique raw t h m hm p p'' n w w'' clk clk'' reset r hsr
    hs''
  subst w''
  have heq := eq_of_heq heq
  subst r
  have clock : MU.env clk = some .clock := by
    have stmt := typed_erase_member m (Typed.Stmt.reg p n w clk reset) _ member
      (i, Typed.Stmt.reg p n w clk reset) (by simp [Typed.Equation.parts]) rfl
    obtain ⟨v, hv', ty⟩ := read_has m hv.1 clk .clock
      (clock_has raw t h m hm clk (resolved_target raw t h m hm _ stmt))
    cases v <;> cases ty
    exact hv'
  change (finalState m).nexts.lookup n = some nextName at hnext
  change (finalState m).resets.lookup n = some opt at hopt
  rw [hopt]
  cases reset with
  | none =>
    cases opt with
    | none => exact next_register MU.env MU.values MU.memories next nextName clk clock value
    | some pair => cases resets
  | some rr =>
    cases opt with
    | none => cases resets
    | some pair =>
      obtain ⟨sig, val⟩ := pair
      exact next_register_reset MU.env MU.values MU.memories next rr nextName clk sig val clock
        value resets.1 resets.2

theorem read_next (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m)
    (inputs : Mlir.Env) (agree : InputsAgree m.ports input inputs) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (children : ∀ i p n child inputs, Typed.Equation.inst i p n child inputs ∈ m.body →
      ∀ c (found : t.bodies.find? (·.name == child) = some c),
        ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found)) :
    Corresponds (certified raw t h) env noExterns m hm (step (certified raw t h) env m hm s input).1
      (Mlir.nextHierarchyState ((lower t).withModels (memoryConfigs t)) (Lower.module m).1
        all) := by
  let d := certified raw t h
  have same := backTranslation_eq_solution d env m hm s input _
    (read_solution raw t h noExterns m hm env s σ corr input inputs agree all hv children)
  have stepEq : (step d env m hm s input).1 = nextLocalState m (designChildren d env m hm) s
      (readBack m (all [])) (stateMemories m (designChildren d env m hm) s)
      (connectionValues d m hm (readBack m (all []))
        (stateMemories m (designChildren d env m hm) s))
      := by
    rw [same]
    rfl
  rw [stepEq]
  intro path name cell named
  cases path with
  | nil =>
    simp only [List.nil_append] at named
    obtain ⟨eq, he, hname, shape⟩ := namedState_cases _ _ _ _ _ _ name [] cell named
    cases eq with
    | let_ | assign => exact shape.elim
    | reg i p n w clk target reset ni np next =>
      simp only [equationName] at hname
      subst hname
      rw [namedState_register d env noExterns m hm _ i p n w clk target reset ni np next he]
        at named
      cases named
      exact next_register_value raw t h noExterns m hm env s σ corr inputs all hv i p n w clk
        target reset ni np next he
    | mem i p n w depth clk target ws =>
      simp only [equationName] at hname
      subst hname
      rw [namedState_memory d env noExterns m hm _ i p n w depth clk target ws he] at named
      cases named
      exact next_memory_value raw t h noExterns m hm env s σ corr inputs all hv i p n w depth clk
        target ws he
    | inst i p n child conns =>
      obtain ⟨c, found⟩ := instance_child_exists d noExterns m hm i p n child conns he
      simp only [equationName] at hname
      subst hname
      rw [namedState_instance d env noExterns m hm _ i p n child conns he c found []] at named
      rw [namedState_nil d env noExterns c (List.mem_of_find?_eq_some found)] at named
      cases named
  | cons first rest =>
    simp only [List.cons_append] at named
    obtain ⟨eq, he, hname, shape⟩ := namedState_cases _ _ _ _ _ _ first _ cell named
    cases eq with
    | let_ | assign => exact shape.elim
    | reg | mem => simp at shape
    | inst i p n child conns =>
      obtain ⟨c, found⟩ := instance_child_exists d noExterns m hm i p n child conns he
      simp only [equationName] at hname
      subst hname
      rw [namedState_instance d env noExterns m hm _ i p n child conns he c found] at named
      obtain ⟨args', fi, hfind, childSolution, agreeInputs, _⟩ := instance_facts raw t h noExterns
        m hm env s σ corr inputs all hv i p n child conns he c found
      have corr' := corresponds_instance d env noExterns m hm s σ corr i p n child conns he c
        found
      obtain ⟨_, childNext⟩ := (children i p n child conns he c found _ _ corr' _ _
        agreeInputs).2 _ childSolution
      apply (cellCorresponds_instance _ n rest name cell).mp
      rw [nextHierarchyState_child _ _ all n child args' fi _ hfind]
      apply childNext rest name cell
      exact (child_next d env m hm i p n child conns he c found _ _) ▸ named

end

end Silicon.Core.LowerProof
