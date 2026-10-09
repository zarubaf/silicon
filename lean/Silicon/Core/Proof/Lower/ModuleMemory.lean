import Silicon.Core.Proof.Lower.ModuleUnique

/-!
The write ports of a lowered memory are the source writes of the memory in port order.
The model applies them to its array as the core memory applies them to its words.
-/
namespace Silicon.Core.LowerProof

open Semantics
open MemModelProof

theorem statements_perm (m : Typed.Module) :
    (Lower.statements m).Perm ((m.body.flatMap Typed.Equation.parts).map Prod.snd) :=
  (List.mergeSort_perm _ _).map _

def eqWrites (n : String) (e : Typed.Equation ctx ports) : List (String × Nat) :=
  ((e.parts.map Prod.snd).flatMap stmtWrites).filter (·.1 == n)

theorem eqWrites_other (n : String) (e : Typed.Equation ctx ports) (other : equationName e ≠ n) :
    eqWrites n e = [] := by
  cases e <;> simp [eqWrites, Typed.Equation.parts, stmtWrites, equationName] at other ⊢
  all_goals intros; simp_all

theorem eqWrites_mem (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String) (target)
    (ws : List (Typed.Write ctx w depth)) :
    eqWrites (ports := ports) n (.mem i p n w depth clk target ws) =
      ws.map (fun wr => (n, wr.port)) := by
  simp only [eqWrites, Typed.Equation.parts, List.map_cons, List.map_map, List.flatMap_cons,
    stmtWrites, List.nil_append]
  induction ws with
  | nil => rfl
  | cons wr ws ih => simp [List.flatMap_cons, stmtWrites, ih]

theorem filter_flatMap_writes (stmts : List (Typed.Stmt ctx ports)) (n : String) :
    (stmts.flatMap stmtWrites).filter (·.1 == n) =
      stmts.flatMap (fun s => (stmtWrites s).filter (·.1 == n)) := by
  induction stmts with
  | nil => rfl
  | cons s rest ih => simp [List.flatMap_cons, List.filter_append, ih]

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)

include h hm in
theorem body_writes (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String) (target)
    (ws : List (Typed.Write m.ctx w depth))
    (member : Typed.Equation.mem i p n w depth clk target ws ∈ m.body) :
    m.body.flatMap (eqWrites n) = ws.map (fun wr => (n, wr.port)) := by
  have names := equation_names_nodup t (certified raw t h).wellFormed m hm
  obtain ⟨l₁, l₂, split⟩ := List.append_of_mem member
  rw [split] at names ⊢
  simp only [List.map_append, List.map_cons, equationName] at names
  have free (e : Typed.Equation m.ctx m.interfaces) (he : e ∈ l₁ ++ l₂) : equationName e ≠ n := by
    intro same
    rcases List.mem_append.mp he with he | he
    · exact (List.nodup_append.mp names).2.2 _ (List.mem_map.mpr ⟨e, he, same⟩) _
        (List.mem_cons_self ..) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp names).2.1).1
        (List.mem_map.mpr ⟨e, he, same⟩)
  rw [List.flatMap_append, List.flatMap_cons, eqWrites_mem]
  have empty (l : List (Typed.Equation m.ctx m.interfaces)) (hl : ∀ e ∈ l, equationName e ≠ n) :
      l.flatMap (eqWrites n) = [] := by
    induction l with
    | nil => rfl
    | cons e l ih =>
      rw [List.flatMap_cons, eqWrites_other n e (hl e (List.mem_cons_self ..)),
        ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
      rfl
  rw [empty l₁ (fun e he => free e (List.mem_append_left _ he)),
    empty l₂ (fun e he => free e (List.mem_append_right _ he))]
  simp

include h hm in
/-- The write ports of the lowered memory have the source write ports. -/
theorem memWrites_ports (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String)
    (target) (ws : List (Typed.Write m.ctx w depth))
    (member : Typed.Equation.mem i p n w depth clk target ws ∈ m.body) :
    ((memWrites (finalState m) n).map (·.index)).Perm (ws.map (·.port)) := by
  obtain ⟨_, _, new, hwrites, keys⟩ :=
    statements_step (Lower.registers m) (Lower.statements m) {}
  rw [← run_state] at hwrites
  simp only [List.append_nil] at hwrites
  have filtered := keys.filter (·.1 == n)
  rw [filter_flatMap_writes] at filtered
  have stmts : ((Lower.statements m).flatMap (fun s => (stmtWrites s).filter (·.1 == n))).Perm
      (m.body.flatMap (eqWrites n)) := by
    refine ((statements_perm m).flatMap_right _).trans (List.Perm.of_eq ?_)
    simp only [List.flatMap_map, List.flatMap_assoc]
    congr 1
    funext e
    rw [eqWrites, filter_flatMap_writes, List.flatMap_map]
  have filtered := filtered.trans stmts
  rw [body_writes raw t h m hm i p n w depth clk target ws member] at filtered
  have mapped := filtered.map Prod.snd
  unfold memWrites
  refine ((List.mergeSort_perm _ _).map _).trans ?_
  rw [hwrites]
  simpa [List.filter_map, Function.comp_def, List.map_map] using mapped

omit noExterns in
include h hm in
theorem write_statement_of (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String)
    (target) (ws : List (Typed.Write m.ctx w depth))
    (member : Typed.Equation.mem i p n w depth clk target ws ∈ m.body)
    (p' : Pos) (n' : String) (same : n' = n) (k w' depth' : Nat) (target') (a d e)
    (hs : Typed.Stmt.write p' n' k w' depth' target' a d e ∈ Lower.statements m) :
    ∃ wr ∈ ws, (Typed.Stmt.write p' n' k w' depth' target' a d e :
      Typed.Stmt m.ctx m.interfaces) =
        .write wr.pos n wr.port w depth target wr.addr wr.data wr.enable := by
  subst same
  obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
  cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  all_goals try (rcases hp with rfl | rfl <;> cases same)
  all_goals try (subst hp; cases same)
  case mem i' p'' n' w'' depth'' clk' target'' ws' =>
    rcases hp with rfl | ⟨wr, hwr, rfl⟩
    · cases same
    · cases same
      have f := find_equation (certified raw t h) m hm _ he
      have f' := find_equation (certified raw t h) m hm _ member
      simp only [equationName] at f f'
      rw [f] at f'
      cases f'
      exact ⟨wr, hwr, rfl⟩

theorem sorted_index {α : Type} (l : List α) (key : α → Nat)
    (indexed : l.map key = List.range l.length) (x : α) (hx : x ∈ l) :
    ∃ hk : key x < l.length, l[key x] = x := by
  obtain ⟨j, hj, same⟩ := List.mem_iff_getElem.mp hx
  have := congrArg (fun l => l[j]?) indexed
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_range hj,
    Option.map_some, Option.some.injEq] at this
  subst same
  rw [this]
  exact ⟨hj, rfl⟩

include h hm in
theorem sorted_writes (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String)
    (target) (ws : List (Typed.Write m.ctx w depth))
    (member : Typed.Equation.mem i p n w depth clk target ws ∈ m.body) :
    let sorted := ws.mergeSort (fun a b => a.port ≤ b.port)
    sorted.length = (memWrites (finalState m) n).length ∧
      sorted.map (·.port) = List.range sorted.length := by
  intro sorted
  have stmt := typed_erase_member m (Typed.Stmt.mem p n w depth clk) _ member
    (i, Typed.Stmt.mem p n w depth clk) (by simp [Typed.Equation.parts]) rfl
  have range := writes_indices raw t h m hm n p w depth clk stmt
  have perm : (sorted.map (·.port)).Perm (List.range (memWrites (finalState m) n).length) := by
    refine ((List.mergeSort_perm _ _).map _).trans ?_
    rw [← range]
    exact (memWrites_ports raw t h m hm i p n w depth clk target ws member).symm
  have length : sorted.length = (memWrites (finalState m) n).length := by
    simpa using perm.length_eq
  refine ⟨length, sorted_range _ _ (mergeSort_sorted _ _) ?_⟩
  rw [length]
  exact perm

theorem foldl_stages (c : MemConfig) (input : Inputs c) (L : List β)
    (F : (Fin c.depth → BitVec c.width) → β → (Fin c.depth → BitVec c.width))
    (hF : ∀ k (hk : k < L.length) cur, F cur L[k] = Semantics.memoryWrite cur
      (input.writeAddr k).toNat (input.writeData k) (input.writeEnable k))
    (start : Fin c.depth → BitVec c.width) : L.foldl F start = stages input start L.length := by
  have step : ∀ k ≤ L.length, (L.take k).foldl F start = stages input start k := by
    intro k
    induction k with
    | zero => intro; rfl
    | succ k ih =>
      intro hk
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, stages]
      exact hF k (by omega) _
  have := step L.length (Nat.le_refl _)
  rwa [List.take_length] at this

theorem stages_congr (a b : Inputs c) (n : Nat)
    (agree : ∀ k < n, a.writeAddr k = b.writeAddr k ∧ a.writeData k = b.writeData k ∧
      a.writeEnable k = b.writeEnable k) (words : Fin q → BitVec c.width) :
    stages a words n = stages b words n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stages]
    obtain ⟨ha, hd, he⟩ := agree n (by omega)
    rw [ih (fun k hk => agree k (by omega)), ha, hd, he]

include h noExterns hm in
theorem memory_lookup (σ : Mlir.ModuleState) (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (i : Nat) (p : Pos) (memory : String) (w depth : Nat) (clk : String)
    (target) (ws) (he : Typed.Equation.mem i p memory w depth clk target ws ∈ m.body) :
    (Lower.module m).1.findInstance memory = some
      ((memConfig (finalState m) memory w depth).moduleName,
        (memArgs (finalState m) memory w depth clk).map (renameArg (rename m))) ∧
    ((lower t).withModels (memoryConfigs t)).findModule (memConfig (finalState m) memory w
      depth).moduleName =
      some (memModel (memConfig (finalState m) memory w depth)) := by
  have entry := memory_entry_body m i p memory w depth clk target ws he
  have hc := memory_config t m hm i p memory w depth clk target ws he
  obtain ⟨child, found, _⟩ := hv.1.2.1 _ entry
  have same := memory_child raw t h noExterns _ hc child found
  subst same
  exact ⟨findInstance_mem _ (module_instNames raw t h noExterns m hm _ rfl) _ _ _ _ _ entry, found⟩

theorem stateMemories_member (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String)
    (target) (ws) (member : Typed.Equation.mem i p n w depth clk target ws ∈ m.body) :
    stateMemories m (designChildren d env m hm) state n w depth target =
      state ⟨.mem i p n w depth clk target ws, member⟩ := by
  have a := namedState_memories d env noExterns m hm state n w depth target
  rw [namedState_memory d env noExterns m hm state i p n w depth clk target ws member] at a
  exact (eq_of_heq (NamedCell.memory.inj (Option.some.inj a)).2.2).symm

variable (env : Env (certified raw t h).design)

theorem next_memory_value (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ)
    (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (i : Nat) (p : Pos) (n : String) (w depth : Nat) (clk : String) (target) (ws)
    (member : Typed.Equation.mem i p n w depth clk target ws ∈ m.body) :
    CellCorresponds
      (Mlir.nextHierarchyState ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 all)
      [] n
      (.memory w depth (nextMemory (readBack m (all []))
        (stateMemories m (designChildren (certified raw t h) env m hm) s)
        (s ⟨.mem i p n w depth clk target ws, member⟩) ws)) := by
  let MU := readMeaning raw t h noExterns m hm env s σ corr inputs all hv
  let c := memConfig (finalState m) n w depth
  let args := (memArgs (finalState m) n w depth clk).map (renameArg (rename m))
  obtain ⟨fi, fm⟩ := memory_lookup raw t h noExterns m hm σ inputs all hv i p n w depth clk
    target ws member
  obtain ⟨solved, _⟩ := memory_solution raw t h noExterns m hm σ inputs all hv i p n w depth clk
    target ws member
  let input' := Inputs.ofEnv c (Mlir.instanceInputs args (all []))
  have local' := localSolution_inputs (ofEnv_agrees c _ (fun q hq => by
    obtain ⟨v, hv, ty, _⟩ := solved.1 q hq
    exact ⟨v, hv, ty⟩)) solved
  let words := stateWords raw t h noExterns m hm env s σ corr n w depth target
  have spec := stateWords_spec raw t h noExterns m hm env s σ corr n w depth target
  have nextVal := local_next c words input' local' spec.1
  refine ⟨stages input' words c.writes, ?_, ?_⟩
  · simp only [List.nil_append, Mlir.nextHierarchyState, Mlir.Module.atPath, fi, fm,
      Option.bind_eq_bind, Option.bind_some]
    exact nextVal
  · obtain ⟨len, indexed⟩ := sorted_writes raw t h m hm i p n w depth clk target ws member
    let sorted := ws.mergeSort (fun a b => a.port ≤ b.port)
    let coreInput : Inputs c := ⟨fun _ => 0,
      fun k => (sorted[k]?.map fun wr => MU.core wr.addr).getD 0,
      fun k => (sorted[k]?.map fun wr => MU.core wr.data).getD 0,
      fun k => (sorted[k]?.map fun wr => MU.core wr.enable).getD 0⟩
    have good := (MU.step_statements (Lower.statements m) (Lower.statements m) (fun _ h => h)
      (fun x hx => stmt_legal raw t h m hm x hx) {}).2 (Grows.refl _)
    have agreeW : ∀ k < c.writes, input'.writeAddr k = (guardedInputs coreInput).writeAddr k ∧
        input'.writeData k = (guardedInputs coreInput).writeData k ∧
        input'.writeEnable k = (guardedInputs coreInput).writeEnable k := by
      intro k hk
      have hk' : k < (memWrites (finalState m) n).length := hk
      have inMem := List.getElem_mem hk'
      generalize hwp : (memWrites (finalState m) n)[k] = wp at inMem
      have index : wp.index = k := by
        rw [← hwp]
        exact memWrites_index raw t h m hm i p n w depth clk target ws member k hk'
      have filtered := (List.mergeSort_perm _ _).mem_iff.mp inMem
      have inWrites : wp ∈ (finalState m).writes := (List.mem_filter.mp filtered).1
      have named : wp.memory = n := by simpa using (List.mem_filter.mp filtered).2
      rcases good.2.1 wp inWrites with absent | ⟨p', w', depth', target', a, dd, e, hs, ha, hd, he⟩
      · cases absent
      obtain ⟨wr, hwr, eqn⟩ := write_statement_of raw t h m hm i p n w depth clk target ws member
        p' wp.memory named wp.index w' depth' target' a dd e hs
      injection eqn with _ _ hport hw hdepth haddr hdata hen
      subst w'
      subst depth'
      have := eq_of_heq haddr
      subst this
      have := eq_of_heq hdata
      subst this
      subst hen
      have inSorted : wr ∈ sorted := (List.mergeSort_perm _ _).mem_iff.mpr hwr
      obtain ⟨hsk, hsorted⟩ := sorted_index sorted (·.port) indexed wr inSorted
      have portK : wr.port = k := hport.symm.trans index
      have sortedK : sorted[k]? = some wr := by
        rw [← portK, List.getElem?_eq_getElem hsk, hsorted]
      have arg (pin : String) (v : String) (ty : Mlir.Ty)
          (hmem : (pin, v, ty) ∈ memArgs (finalState m) n w depth clk) (width : Nat)
          (hty : ty = .int width) (x : BitVec width) (hval : MU.env v = some (.bits width x)) :
          (Mlir.instanceInputs args (all [])).bits pin width = some x := by
        have find := memArgs_find raw t h m hm i p n w depth clk target ws member (rename m) _ hmem
        unfold Mlir.Env.bits
        have at' := instanceInputs_find args (all []) (renameArg (rename m) (pin, v, ty)) find
        change Mlir.instanceInputs args (all []) pin = _ at at'
        rw [at']
        subst hty
        change (all []).typed (rename m v) _ >>= _ = _
        change (all []) (rename m v) = _ at hval
        simp [Mlir.Env.typed, hval, Mlir.Value.ty, renameArg, Mlir.Value.asBits]
      have writeArg (pin : String → String) (field : Lower.WritePort → String) (ty : Mlir.Ty)
          (hpin : ∀ x ∈ memWrites (finalState m) n,
            (pin s!"{x.index}", field x, ty) ∈ memArgs (finalState m) n w depth clk) :
          (pin s!"{k}", field wp, ty) ∈ memArgs (finalState m) n w depth clk := by
        have := hpin wp inMem
        rwa [index] at this
      have inArgs (j : Fin 3) : ∀ x ∈ memWrites (finalState m) n,
          ([(s!"w{x.index}_addr", x.addr, Mlir.Ty.int (Typed.addressWidth depth)),
            (s!"w{x.index}_data", x.data, .int w), (s!"w{x.index}_en", x.enable, .int 1)][j]) ∈
            memArgs (finalState m) n w depth clk := by
        intro x hx
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨x, hx, List.getElem_mem _⟩
      refine ⟨?_, ?_, ?_⟩
      · have value := arg s!"w{k}_addr" wp.addr _ (writeArg (fun i => s!"w{i}_addr") (·.addr)
          _ (inArgs 0)) _ rfl _ ha
        simp only [input', Inputs.ofEnv, guardedInputs, coreInput, sortedK,
          Option.map_some, Option.getD_some]
        exact congrArg (·.getD 0) value
      · have value := arg s!"w{k}_data" wp.data _ (writeArg (fun i => s!"w{i}_data") (·.data)
          _ (inArgs 1)) _ rfl _ hd
        simp only [input', Inputs.ofEnv, guardedInputs, coreInput, sortedK,
          Option.map_some, Option.getD_some]
        exact congrArg (·.getD 0) value
      · have value := arg s!"w{k}_en" wp.enable _ (writeArg (fun i => s!"w{i}_en") (·.enable)
          _ (inArgs 2)) _ rfl _ he
        simp only [input', Inputs.ofEnv, guardedInputs, coreInput, sortedK,
          Option.map_some, Option.getD_some]
        exact congrArg (·.getD 0) value
    rw [stages_congr input' (guardedInputs coreInput) c.writes agreeW words]
    have agree := spec.2
    rw [stateMemories_member _ env noExterns m hm s i p n w depth clk target ws member] at agree
    have staged := guarded_stages_agree c coreInput words _ agree c.writes
    have folded : nextMemory (readBack m (all []))
        (stateMemories m (designChildren (certified raw t h) env m hm) s)
        (s ⟨.mem i p n w depth clk target ws, member⟩) ws =
          stages coreInput (s ⟨.mem i p n w depth clk target ws, member⟩) c.writes := by
      unfold nextMemory
      change _ = stages coreInput _ (memWrites (finalState m) n).length
      rw [← len]
      apply foldl_stages c coreInput sorted
      intro k hk cur
      simp only [coreInput, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
      rfl
    rw [folded]
    exact staged

end

end Silicon.Core.LowerProof
