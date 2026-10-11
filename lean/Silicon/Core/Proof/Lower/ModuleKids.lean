-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleExist

/-!
Each instance op of the image has a child solution whose outputs are the instance results.
-/
namespace Silicon.Core.LowerProof

open Semantics

/-- A child valuation that solves an instance op. -/
def KidProp (D : Mlir.Design) (σ : Mlir.ModuleState) (vals : Mlir.Env) (names : List String)
    (inst callee : String) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty)) (v : Mlir.Valuation) : Prop :=
  ∃ child, D.findModule callee = some child ∧ names.length = results.length ∧
    child.outputs.length = results.length ∧
    Mlir.IsHierarchySolution D child (σ.instance inst) (Mlir.instanceInputs args vals) v ∧
    ∀ k : Fin names.length, ∃ val, vals names[k] = some val ∧
      (∃ source, child.outputs[k.val]? = some source ∧ v [] source = some val) ∧
      (results[k.val]?.map Prod.snd) = some val.ty

theorem getElem_of_map {α β : Type} (L : List α) (g : α → β) (l : List β) (hl : l = L.map g)
    (k : Nat) (hk : k < l.length) (hk' : k < L.length) : l[k] = g L[k] := by
  subst hl
  simp

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)
  (env : Env (certified raw t h).design)

theorem source_kid (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m)
    (F : ImageFacts raw t h m hm env s input)
    (i : Nat) (p : Pos) (n child : String)
    (conns : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
    (member : Typed.Equation.inst i p n child conns ∈ m.body)
    (c : Typed.Module) (found : t.bodies.find? (·.name == child) = some c)
    (correct : ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found))
    (names : List String) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty))
    (he : (names, Mlir.Op.instance n child args results) ∈ (Lower.module m).1.body) :
    ∃ v, KidProp ((lower t).withModels (memoryConfigs t)) σ F.env0 names n child args
      results v := by
  let d := certified raw t h
  let sol := solution d env m hm s input
  let memories := stateMemories m (designChildren d env m hm) s
  have hc := List.mem_of_find?_eq_some found
  have hports := child_ports d m hm child c found
  have hV : ∀ y, F.env0 (rename m y) = F.meaning.env y := fun y => by
    rw [F.isEnv]
    exact F.renamed y
  obtain ⟨args₁, he₁, agreeIn⟩ := connection_agree raw t h m hm F.meaning F.registers F.final
    F.env0 hV i p n child conns member c found
  rw [F.values, F.memories] at agreeIn
  have canonical : ((instResults m.interfaces child).map (fun q => s!"{n}.{q.1}"),
      Mlir.Op.instance n child ((instArgs m.interfaces child args₁).map (renameArg (rename m)))
        (instResults m.interfaces child)) ∈ (Lower.module m).1.body := by
    rw [module_body]
    exact List.mem_map.mpr ⟨_, List.mem_append_left _ (List.mem_append_left _ he₁),
      by simp only [substitute_instance]⟩
  obtain ⟨rfl, -, rfl, rfl⟩ := inst_entry_unique raw t h noExterns m hm _ _ n _ _ _ _ _ _ he
    canonical
  have corr' := corresponds_instance d env noExterns m hm s σ corr i p n child conns member c found
  obtain ⟨vals', solved', outs⟩ := (correct _ _ corr' _ _ agreeIn).1
  have hfind :
      ((lower t).withModels (memoryConfigs t)).findModule child = some (Lower.module c).1 := by
    have name : (Lower.module c).1.name = child := by
      rw [module_name]
      simpa using List.find?_some found
    rw [← name]
    exact findModule_mem _ (design_names raw t h noExterns) _ (body_in_design t noExterns c hc)
  have outputsEq : (Lower.module c).1.outputs =
      ((m.interfaces child).filter (·.dir == .output)).map (fun q => rename c q.name) := by
    rw [outputs_filter, hports]
  have namesEq : (instResults m.interfaces child).map (fun q => s!"{n}.{q.1}") =
      ((m.interfaces child).filter (·.dir == .output)).map (fun q => s!"{n}.{q.name}") := by
    rw [instResults_filter, List.map_map]
    rfl
  refine ⟨vals', (Lower.module c).1, hfind, by simp, ?_, solved', ?_⟩
  · rw [outputsEq, instResults_filter]
    simp
  · intro ⟨kv, hkv⟩
    have hk : kv < ((m.interfaces child).filter (·.dir == .output)).length := by
      have := hkv
      simp only [List.length_map, instResults_filter] at this
      exact this
    let q := ((m.interfaces child).filter (·.dir == .output))[kv]
    have hq : q ∈ (m.interfaces child).filter (·.dir == .output) := List.getElem_mem hk
    have qMember : q ∈ m.interfaces child := (List.mem_filter.mp hq).1
    have qDir : q.dir = .output := by simpa using (List.mem_filter.mp hq).2
    have h₂ : q ∈ c.ports := by rw [← hports]; exact qMember
    have notClock := output_not_clock raw t h c hc q h₂ qDir
    obtain ⟨w, bits⟩ : ∃ w, q.ty = .bits w := by
      cases hty : q.ty with
      | clock => exact absurd hty notClock
      | bits w => exact ⟨w, rfl⟩
    have lookupQ := port_lookup raw t h m hm i p n child conns member q qMember qDir
    rw [bits] at lookupQ
    have refs := F.meaning.refs (.port n q.name) w lookupQ
    rw [F.isEnv, F.registers, F.values] at refs
    simp only [Lower.valueName] at refs
    have solvedQ := localSolution_isSolution d m hm (designChildren d env m hm) s input
      (.port n q.name) w lookupQ (.inst i p n child conns member q qMember qDir bits)
    change sol (.port n q.name) w lookupQ = cast (congrArg TyValue bits)
      ((designChildren d env m hm ⟨.inst i p n child conns, member⟩).out
        (s ⟨.inst i p n child conns, member⟩)
        (connectionValues d m hm sol memories ⟨.inst i p n child conns, member⟩)
        ⟨q, qMember, qDir⟩) at solvedQ
    replace solvedQ := solvedQ.trans (congrArg (cast (congrArg TyValue bits))
      (child_out d env m hm i p n child conns member c found _ _ q qMember h₂ qDir))
    have outQ := outs ⟨q, h₂, qDir⟩
    refine ⟨coreValue q.ty ((step d env c hc
      (cast (State_inst_module d env m hm i p n child conns member c found)
        (s ⟨.inst i p n child conns, member⟩))
      (transportInput hports (connectionValues d m hm sol memories
        ⟨.inst i p n child conns, member⟩))).2 ⟨q, h₂, qDir⟩), ?_, ?_, ?_⟩
    · have nameK := getElem_of_map _ (fun q : Port => s!"{n}.{q.name}") _ namesEq kv hkv hk
      refine (congrArg F.env0 nameK).trans ?_
      exact refs.trans ((congrArg (fun v => some (Mlir.Value.bits w v)) solvedQ).trans
        (congrArg some (coreValue_cast bits _).symm))
    · refine ⟨rename c q.name, ?_, outQ⟩
      simp only [outputsEq, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some]
      rfl
    · have resK : (instResults m.interfaces child)[kv]? = some (q.name, Lower.type q.ty) := by
        rw [instResults_filter]
        simp [List.getElem?_map, List.getElem?_eq_getElem hk, q]
      refine (congrArg (Option.map Prod.snd) resK).trans ?_
      exact congrArg some (coreValue_ty _ _).symm


theorem memory_kid (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m)
    (F : ImageFacts raw t h m hm env s input)
    (hw : F.words = stateWords raw t h noExterns m hm env s σ corr)
    (models : ∀ c ∈ memoryConfigs t,
      ((lower t).withModels (memoryConfigs t)).findModule c.moduleName = some (memModel c))
    (i : Nat) (p : Pos) (mem : String) (w depth : Nat) (clk : String) (target) (ws)
    (member : Typed.Equation.mem i p mem w depth clk target ws ∈ m.body)
    (names : List String) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty))
    (he : (names, Mlir.Op.instance mem (memConfig (finalState m) mem w depth).moduleName args
      results) ∈ (Lower.module m).1.body) :
    ∃ v, KidProp ((lower t).withModels (memoryConfigs t)) σ F.env0 names mem
      (memConfig (finalState m) mem w depth).moduleName args results v := by
  let c := memConfig (finalState m) mem w depth
  have canonical := memory_entry_body m i p mem w depth clk target ws member
  obtain ⟨rfl, -, rfl, rfl⟩ := inst_entry_unique raw t h noExterns m hm _ _ mem _ _ _ _ _ _ he
    canonical
  let args := (memArgs (finalState m) mem w depth clk).map (renameArg (rename m))
  have hfind := models c (memory_config t m hm i p mem w depth clk target ws member)
  let words := stateWords raw t h noExterns m hm env s σ corr mem w depth target
  have spec := stateWords_spec raw t h noExterns m hm env s σ corr mem w depth target
  have envAt (y : String) (ty : Mlir.Ty) (val : Mlir.Value) (hy : F.meaning.env y = some val)
      (hty : val.ty = ty) : F.env0.typed (rename m y) ty = some val := by
    simp only [Mlir.Env.typed]
    rw [F.renamed, ← F.isEnv]
    simp [hy, hty]
  have argAt (a : String × String × Mlir.Ty) (ha : a ∈ memArgs (finalState m) mem w depth clk) :
      Mlir.instanceInputs args F.env0 a.1 = F.env0.typed (rename m a.2.1) a.2.2 :=
    instanceInputs_find args F.env0 (renameArg (rename m) a)
      (memArgs_find raw t h m hm i p mem w depth clk target ws member (rename m) a ha)
  have readArg (k : Nat) (hk : k < (memReads (finalState m) mem).length) :
      ((s!"r{k}_addr", (memReads (finalState m) mem)[k].addr,
        Mlir.Ty.int (Typed.addressWidth depth)) ∈ memArgs (finalState m) mem w depth clk) := by
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, List.getElem_mem hk, by
      rw [memReads_index m mem k hk]⟩
  have readFacts (k : Nat) (hk : k < (memReads (finalState m) mem).length) :
      ∃ address : BitVec (Typed.addressWidth depth),
        F.meaning.env (memReads (finalState m) mem)[k].addr = some (.bits _ address) ∧
        F.meaning.env s!"{mem}.r{k}_data" = some (.bits w (Semantics.memoryRead
          (F.meaning.words mem w depth target) address.toNat)) := by
    have inMem := List.getElem_mem hk
    have index := memReads_index m mem k hk
    generalize (memReads (finalState m) mem)[k] = r at inMem index ⊢
    obtain ⟨rm, ri, ra⟩ := r
    simp only at index ⊢
    have filtered := (List.mergeSort_perm _ _).mem_iff.mp inMem
    have inReads := (List.mem_filter.mp filtered).1
    have named : rm = mem := by simpa using (List.mem_filter.mp filtered).2
    subst named
    subst index
    obtain ⟨w', depth', found', address, ha, hd⟩ := F.meaning.reads _ (by
      rw [F.final]; exact inReads)
    obtain ⟨hw', hd'⟩ := lookup_memory_unique target found'
    subst w' depth'
    exact ⟨address, ha, hd⟩
  have writeFacts (k : Nat) (hk : k < (memWrites (finalState m) mem).length) :
      ∃ wa wd we, (s!"w{k}_addr", wa, Mlir.Ty.int (Typed.addressWidth depth)) ∈
          memArgs (finalState m) mem w depth clk ∧
        (s!"w{k}_data", wd, Mlir.Ty.int w) ∈ memArgs (finalState m) mem w depth clk ∧
        (s!"w{k}_en", we, Mlir.Ty.int 1) ∈ memArgs (finalState m) mem w depth clk ∧
        (∃ x : BitVec (Typed.addressWidth depth), F.meaning.env wa = some (.bits _ x)) ∧
        (∃ x : BitVec w, F.meaning.env wd = some (.bits w x)) ∧
        (∃ x : BitVec 1, F.meaning.env we = some (.bits 1 x)) := by
    have inMem := List.getElem_mem hk
    have index := memWrites_index raw t h m hm i p mem w depth clk target ws member k hk
    generalize (memWrites (finalState m) mem)[k] = wp at inMem index
    obtain ⟨wm, wi, wa, wd, we⟩ := wp
    simp only at index
    have filtered := (List.mergeSort_perm _ _).mem_iff.mp inMem
    have inWrites := (List.mem_filter.mp filtered).1
    have named : wm = mem := by simpa using (List.mem_filter.mp filtered).2
    subst named
    subst index
    have flat (j : Nat) (hj : j < 3) :
        [(s!"w{wi}_addr", wa, Mlir.Ty.int (Typed.addressWidth depth)),
          (s!"w{wi}_data", wd, Mlir.Ty.int w), (s!"w{wi}_en", we, Mlir.Ty.int 1)][j] ∈
          memArgs (finalState m) wm w depth clk := by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨⟨wm, wi, wa, wd, we⟩, inMem, List.getElem_mem _⟩
    rcases F.good.2.1 _ inWrites with absent | ⟨p', w', depth', target', a, dd, e, _, ha, hd, hen⟩
    · cases absent
    obtain ⟨hw', hd'⟩ := lookup_memory_unique target target'
    subst w' depth'
    exact ⟨wa, wd, we, flat 0 (by decide), flat 1 (by decide), flat 2 (by decide), ⟨_, ha⟩,
      ⟨_, hd⟩, ⟨_, hen⟩⟩
  have stmtMem := typed_erase_member m (Typed.Stmt.mem p mem w depth clk) _ member
    (i, Typed.Stmt.mem p mem w depth clk) (by simp [Typed.Equation.parts]) rfl
  have typed : ∀ q ∈ (memModel c).inputPorts, ∃ val,
      Mlir.instanceInputs args F.env0 q.name = some val ∧ val.ty = q.ty := by
    intro q hq
    rcases MemModelProof.input_port_cases c q hq with rfl | ⟨r, hr, rfl⟩ |
      ⟨k, hk, rfl | rfl | rfl⟩
    · have clkArg : ("clk", clk, Mlir.Ty.clock) ∈ memArgs (finalState m) mem w depth clk :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))
      have clockAt : F.meaning.env clk = some .clock := F.meaning.clocks clk
        (clock_lookup raw t h m hm clk (resolved_target raw t h m hm _ stmtMem))
      exact ⟨.clock, (argAt _ clkArg).trans (envAt clk .clock .clock clockAt rfl), rfl⟩
    · obtain ⟨address, ha, _⟩ := readFacts r hr
      exact ⟨_, (argAt _ (readArg r hr)).trans (envAt _ _ _ ha rfl), rfl⟩
    · obtain ⟨wa, _, _, ma, _, _, ⟨x, hx⟩, _, _⟩ := writeFacts k hk
      exact ⟨_, (argAt _ ma).trans (envAt _ _ _ hx rfl), rfl⟩
    · obtain ⟨_, wd, _, _, md, _, _, ⟨x, hx⟩, _⟩ := writeFacts k hk
      exact ⟨_, (argAt _ md).trans (envAt _ _ _ hx rfl), rfl⟩
    · obtain ⟨_, _, we, _, _, me, _, _, ⟨x, hx⟩⟩ := writeFacts k hk
      exact ⟨_, (argAt _ me).trans (envAt _ _ _ hx rfl), rfl⟩
  let input' := MemModelProof.Inputs.ofEnv c (Mlir.instanceInputs args F.env0)
  have agreeIn := MemModelProof.ofEnv_agrees c _ typed
  have baseLocal := MemModelProof.local_values c words input' _ spec.1
    ((lower t).withModels (memoryConfigs t))
    (fun _ _ => none)
  have localSol := localSolution_inputs (fun q hq => (agreeIn q hq).symm) baseLocal
  refine ⟨fun path => match path with
    | [] => MemModelProof.values c words input'
    | _ :: _ => fun _ => none, memModel c, hfind, by simp [memResults], by simp [c, memModel,
      memConfig, memResults], ⟨localSol, ?_⟩, ?_⟩
  · intro path parent found inst callee args' fi
    cases path with
    | nil =>
      simp only [Mlir.Module.atPath, Option.some.injEq] at found
      subst found
      rw [MemModelProof.findInstance_none] at fi
      cases fi
    | cons x rest =>
      rw [MemModelProof.atPath_cons] at found
      cases found
  · intro ⟨kv, hkv⟩
    have hk : kv < (memReads (finalState m) mem).length := by simpa using hkv
    obtain ⟨n₁, n₂⟩ := memory_outputs m mem w depth kv hk
    obtain ⟨address, ha, hd⟩ := readFacts kv hk
    have value := MemModelProof.reads_value c words input' baseLocal spec.1 kv hk
    have addrValue : input'.readAddr kv = address := by
      have hin : Mlir.instanceInputs args F.env0 s!"r{kv}_addr" = some (.bits _ address) :=
        (argAt _ (readArg kv hk)).trans (envAt _ _ _ ha rfl)
      show ((Mlir.instanceInputs args F.env0) s!"r{kv}_addr" >>=
        Mlir.Value.asBits (Typed.addressWidth depth)).getD 0 = address
      rw [hin]
      simp [Mlir.Value.asBits]
    rw [addrValue] at value
    refine ⟨.bits w (Semantics.memoryRead words address.toNat), ?_, ⟨_, n₂, value⟩, ?_⟩
    · exact (congrArg F.env0 n₁).trans ((congrFun F.isEnv.symm _).trans (hd.trans (by
        rw [F.isWords, hw])))
    · simp [memResults, List.getElem?_map, List.getElem?_eq_getElem hk, memReads_index m mem kv hk,
        Mlir.Value.ty]


theorem findInstance_entry (M : Mlir.Module) (inst callee : String)
    (args : List (String × String × Mlir.Ty)) (found : M.findInstance inst = some (callee, args)) :
    ∃ names results, (names, Mlir.Op.instance inst callee args results) ∈ M.body := by
  unfold Mlir.Module.findInstance at found
  obtain ⟨⟨names, op⟩, he, hop⟩ := List.exists_of_findSome?_eq_some found
  cases op with
  | «instance» inst' callee' args' results =>
    simp only at hop
    split at hop
    · cases hop
      rename_i same
      subst same
      exact ⟨names, results, he⟩
    · cases hop
  | _ => simp at hop

theorem ports_output_filter (ports : List Port) :
    (ports.map Lower.port).filter (·.dir == .output) =
      (ports.filter (·.dir == .output)).map Lower.port := by
  induction ports with
  | nil => rfl
  | cons q qs ih =>
    cases hd : q.dir <;> simp [Lower.port, hd, ih]

theorem ports_input_filter (ports : List Port) :
    (ports.map Lower.port).filter (·.dir == .input) =
      (ports.filter (·.dir == .input)).map Lower.port := by
  induction ports with
  | nil => rfl
  | cons q qs ih =>
    cases hd : q.dir <;> simp [Lower.port, hd, ih]

end

end Silicon.Core.LowerProof
