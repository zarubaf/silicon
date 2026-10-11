-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleKids

/-!
One lowered module is correct when its children are correct. The image of the core solution
solves it. Every solution has the core outputs. Every next state corresponds to the core
next state. Memories use the models of their configurations.
-/
namespace Silicon.Core.LowerProof

open Semantics

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)
  (env : Env (certified raw t h).design)

theorem coreValue_clock {ty : Ty} (hc : ty = .clock) (x : TyValue ty) :
    coreValue ty x = .clock := by
  subst hc
  rfl

theorem module_exists (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m)
    (inputs : Mlir.Env) (agree : InputsAgree m.ports input inputs)
    (models : ∀ c ∈ memoryConfigs t,
      ((lower t).withModels (memoryConfigs t)).findModule c.moduleName = some (memModel c))
    (children : ∀ i p n child inputs, Typed.Equation.inst i p n child inputs ∈ m.body →
      ∀ c (found : t.bodies.find? (·.name == child) = some c),
        ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found)) :
    ∃ vals, Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs vals ∧
      OutputsAgree m (step (certified raw t h) env m hm s input).2 (vals []) := by
  classical
  obtain ⟨F, hw⟩ := image_facts raw t h noExterns m hm env s σ corr input
  let d := certified raw t h
  let sol := solution d env m hm s input
  have solved : IsLocalSolution d m hm (designChildren d env m hm) s input sol :=
    localSolution_isSolution d m hm (designChildren d env m hm) s input
  have refs : ∀ node w found, F.env0 (Lower.valueName (Lower.registers m) node) =
      some (.bits w (sol node w found)) := by
    intro node w found
    have := F.meaning.refs node w found
    rw [F.isEnv, F.registers, F.values] at this
    exact this
  have kidAll : ∀ names inst callee args results,
      (names, Mlir.Op.instance inst callee args results) ∈ (Lower.module m).1.body →
        ∃ v, KidProp ((lower t).withModels (memoryConfigs t)) σ F.env0 names inst callee args
          results v := by
    intro names inst callee args results he
    rcases instance_entry_cases m names inst callee args results he with
      ⟨i, p, conns, member⟩ | ⟨i, p, w, depth, clk, target, ws, member, rfl⟩
    · obtain ⟨c, found⟩ := instance_child_exists d noExterns m hm i p inst callee conns member
      exact source_kid raw t h noExterns m hm env s σ corr input F i p inst callee conns member
        c found (children i p inst callee conns member c found) names args results he
    · exact memory_kid raw t h noExterns m hm env s σ corr input F hw models i p inst w depth
        clk target ws member names args results he
  let KidOk : String → Mlir.Valuation → Prop := fun inst v =>
    ∀ names callee args results,
      (names, Mlir.Op.instance inst callee args results) ∈ (Lower.module m).1.body →
        KidProp ((lower t).withModels (memoryConfigs t)) σ F.env0 names inst callee args results v
  have kidExists : ∀ names inst callee args results,
      (names, Mlir.Op.instance inst callee args results) ∈ (Lower.module m).1.body →
        ∃ v, KidOk inst v := by
    intro names inst callee args results he
    obtain ⟨v, hv⟩ := kidAll _ _ _ _ _ he
    refine ⟨v, fun names' callee' args' results' he' => ?_⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inst_entry_unique raw t h noExterns m hm _ _ inst _ _ _ _ _ _
      he he'
    exact hv
  let kids : String → Mlir.Valuation := fun inst =>
    if hk : ∃ v, KidOk inst v then hk.choose else fun _ _ => none
  have kidSpec : ∀ names inst callee args results,
      (names, Mlir.Op.instance inst callee args results) ∈ (Lower.module m).1.body →
        KidProp ((lower t).withModels (memoryConfigs t)) σ F.env0 names inst callee args results
          (kids inst) := by
    intro names inst callee args results he
    have ex := kidExists _ _ _ _ _ he
    have pick : kids inst = ex.choose := by
      simp only [kids]
      split
      · rfl
      · contradiction
    rw [pick]
    exact ex.choose_spec names callee args results he
  have wf := body_wellFormed raw t h noExterns m hm
  have inputsClause : ∀ p ∈ (Lower.module m).1.inputPorts, ∃ v, inputs p.name = some v ∧
      v.ty = p.ty ∧ F.env0 p.name = some v := by
    intro p hp
    simp only [Mlir.Module.inputPorts, module_ports, ports_input_filter, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hqm, hqd⟩ := List.mem_filter.mp hq
    have dir : q.dir = .input := by simpa using hqd
    have ha := agree ⟨q, hqm, dir⟩
    refine ⟨coreValue q.ty (input ⟨q, hqm, dir⟩), ha, coreValue_ty _ _, ?_⟩
    change F.env0 q.name = _
    rw [F.outside q.name (input_not_allocated raw t h m hm q hqm dir)]
    have kinds : q.ty = .clock ∨ ∃ w, q.ty = .bits w := by
      cases q.ty with
      | clock => exact Or.inl rfl
      | bits w => exact Or.inr ⟨w, rfl⟩
    rcases kinds with hty | ⟨w, hty⟩
    · have found : m.ctx.lookup (.name q.name) = some .clock :=
        lookup_name raw t h m hm _ _ (by
          have := port_in_context m q hqm
          simpa [portKind, hty, dir] using this)
      rw [coreAt_clock raw t h m hm sol _ found, coreValue_clock hty]
    · have found := port_found t d.wellFormed m hm q hqm hty
      have value := coreAt_node raw t h m hm sol (.name q.name) w found
      rw [valueName_plain _ _ (port_not_register raw t h m hm q hqm)] at value
      rw [value, solved (.name q.name) w found (.input q hqm dir hty), coreValue_cast hty]
      rfl
  have bodyClause : ∀ entry ∈ (Lower.module m).1.body, match entry with
      | (names, .instance inst callee args results) =>
        ∃ child, ((lower t).withModels (memoryConfigs t)).findModule callee = some child ∧
          names.length = results.length ∧ child.outputs.length = results.length ∧
          (∀ p ∈ child.inputPorts,
            (fun inst => kids inst []) inst p.name = Mlir.instanceInputs args F.env0 p.name) ∧
          (∀ i : Fin names.length, ∃ v,
            F.env0 names[i] = some v ∧
            (∃ source, child.outputs[i.val]? = some source ∧
              (fun inst => kids inst []) inst source = some v) ∧
            (results[i.val]?.map Prod.snd) = some v.ty)
      | (names, .compreg _ _ _ ty) =>
        ∃ name v, names = [name] ∧ σ.regs name = some v ∧ v.ty = ty ∧ F.env0 name = some v
      | (names, op) => ∃ name v, names = [name] ∧ op.eval F.env0 = some v ∧
          F.env0 name = some v := by
    intro entry he
    have he' := he
    rw [module_body] at he'
    obtain ⟨⟨names, op⟩, hraw, rfl⟩ := List.mem_map.mp he'
    have notPlain (plain : isInstance op = false) (stateless : isCompreg op = false) :
        (names, op) ∈ (finalState m).body.toList := by
      unfold rawBody at hraw
      rcases List.mem_append.mp hraw with hraw | hraw
      · rcases List.mem_append.mp hraw with hraw | hraw
        · exact hraw
        · obtain ⟨x, hx, same⟩ := List.mem_map.mp hraw
          obtain ⟨_, _, memory, w, depth, clk, _, _, _, rfl⟩ := memoryEntries_mem m _ x hx
          simp only [memEntry, Prod.mk.injEq] at same
          obtain ⟨_, rfl⟩ := same
          cases plain
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := registerEntries_mem m _ _ hraw
        simp only [Prod.mk.injEq] at same
        obtain ⟨_, rfl⟩ := same
        cases stateless
    cases op with
    | «instance» inst callee args results =>
      simp only [substitute_instance] at he ⊢
      obtain ⟨child, hfind, l₁, l₂, hier, outs⟩ := kidSpec _ _ _ _ _ he
      refine ⟨child, hfind, l₁, l₂, fun q hq => ?_, outs⟩
      obtain ⟨v, hi, _, hv⟩ := hier.1.1 q hq
      exact hv.trans hi.symm
    | compreg next clk reset ty =>
      unfold rawBody at hraw
      rcases List.mem_append.mp hraw with hraw | hraw
      · rcases List.mem_append.mp hraw with hraw | hraw
        · obtain ⟨_, _, stateless, _⟩ := final_entries m _ hraw
          cases stateless
        · obtain ⟨x, hx, same⟩ := List.mem_map.mp hraw
          obtain ⟨_, _, memory, w, depth, clk, _, _, _, rfl⟩ := memoryEntries_mem m _ x hx
          simp only [memEntry, Prod.mk.injEq, reduceCtorEq, and_false] at same
      · obtain ⟨i, p, n, w, clk', target, reset', ni, np, next', nextName, member, _, same⟩ :=
          registerEntries_mem m _ _ hraw
        simp only [Prod.mk.injEq, Mlir.Op.compreg.injEq] at same
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
        have hreg := corresponds_register d env noExterns m hm s σ corr i p n w clk target reset'
          ni np next' member
        refine ⟨_, _, rfl, hreg, rfl, ?_⟩
        rw [F.outside _ (register_not_allocated raw t h m hm i p n w clk target reset' ni np next'
          member)]
        have found := valueTy_lookup _ _ _ target
        have value := coreAt_node raw t h m hm sol (.name n) w found
        have inRegs : n ∈ Lower.registers m := List.mem_filterMap.mpr ⟨_, member, rfl⟩
        have contains : (Lower.registers m).contains n = true := by simpa using inRegs
        simp only [Lower.valueName, contains, ↓reduceIte] at value
        rw [value, solved (.name n) w found (.reg i p n w clk target reset' ni np next' member)]
        rfl
    | _ =>
      obtain ⟨name, v, hn, hv, hop⟩ := F.meaning.ops _ _ (F.final ▸ notPlain rfl rfl) rfl rfl
      refine ⟨name, v, hn, ?_, F.isEnv ▸ hv⟩
      rw [substitute_eval]
      have same : F.env0 ∘ rename m = F.env0 := funext F.renamed
      rw [same, ← F.isEnv]
      exact hop
  have portValue (q : Port) (hq : q ∈ m.ports) (dir : q.dir = .output) (w : Nat)
      (bits : q.ty = .bits w) :
      F.env0 (rename m q.name) = some (.bits w (sol (.name q.name) w
        (port_found t d.wellFormed m hm q hq bits))) := by
    rw [F.renamed]
    have value := refs (.name q.name) w (port_found t d.wellFormed m hm q hq bits)
    rw [valueName_plain _ _ (port_not_register raw t h m hm q hq)] at value
    exact value
  have outputsClause : ∀ i : Fin (Lower.module m).1.outputs.length, ∃ v,
      F.env0 (Lower.module m).1.outputs[i] = some v ∧
      ((Lower.module m).1.outputPorts[i.val]?.map Mlir.Port.ty) = some v.ty := by
    intro ⟨kv, hkv⟩
    have outputsEq := outputs_filter m
    have portsEq : (Lower.module m).1.outputPorts =
        (m.ports.filter (·.dir == .output)).map Lower.port := by
      simp only [Mlir.Module.outputPorts, module_ports]
      exact ports_output_filter m.ports
    have hk : kv < (m.ports.filter (·.dir == .output)).length := by
      have := hkv
      simp only [outputsEq, List.length_map] at this
      exact this
    have hq := List.getElem_mem hk
    have qMember := (List.mem_filter.mp hq).1
    have qDir : (m.ports.filter (·.dir == .output))[kv].dir = .output := by
      simpa using (List.mem_filter.mp hq).2
    obtain ⟨w, bits⟩ : ∃ w, (m.ports.filter (·.dir == .output))[kv].ty = .bits w := by
      cases hty : (m.ports.filter (·.dir == .output))[kv].ty with
      | clock => exact absurd hty (output_not_clock raw t h m hm _ qMember qDir)
      | bits w => exact ⟨w, rfl⟩
    refine ⟨.bits w (sol (.name _) w (port_found t d.wellFormed m hm _ qMember bits)), ?_, ?_⟩
    · have name := getElem_of_map _ (fun q : Port => rename m q.name) _ outputsEq kv hkv hk
      exact (congrArg F.env0 name).trans (portValue _ qMember qDir w bits)
    · rw [portsEq]
      simp [List.getElem?_map, List.getElem?_eq_getElem hk, Lower.port, bits, Lower.type,
        Mlir.Value.ty]
  have root : Mlir.LocalSolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1
      σ.regs inputs F.env0 (fun inst => kids inst []) :=
    ⟨inputsClause, bodyClause, wf.2.2.2.2.1, outputsClause⟩
  have hier := hierarchy_compose _ _ σ inputs F.env0 kids root (fun inst callee args fi => by
    obtain ⟨names, results, he⟩ := findInstance_entry _ inst callee args fi
    obtain ⟨child, hfind, _, _, hier, _⟩ := kidSpec _ _ _ _ _ he
    exact ⟨child, hfind, hier⟩)
  refine ⟨_, hier, ?_⟩
  intro q
  obtain ⟨⟨pos, qdir, name, ty⟩, hq, dir⟩ := q
  cases ty with
  | clock => exact absurd rfl (output_not_clock raw t h m hm _ hq dir)
  | bits w =>
    exact portValue ⟨pos, qdir, name, .bits w⟩ hq dir w rfl


include h noExterns in
/-- Each memory configuration names its model module. -/
theorem config_module (c : MemConfig) (hc : c ∈ memoryConfigs t) :
    ((lower t).withModels (memoryConfigs t)).findModule c.moduleName = some (memModel c) := by
  have member := config_in_design t noExterns c hc
  rw [image_config _ c hc] at member
  exact findModule_mem _ (design_names raw t h noExterns) _ member

/-- The step for one module, given its children.
`children` is the hypothesis of the hierarchy step: every child module of an instance in `m`
satisfies `ModuleCorrect`. -/
theorem module_correct
    (children : ∀ i p n child inputs, Typed.Equation.inst i p n child inputs ∈ m.body →
      ∀ c (found : t.bodies.find? (·.name == child) = some c),
        ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found)) :
    ModuleCorrect raw t h noExterns env m hm := by
  intro s σ corr input inputs agree
  refine ⟨module_exists raw t h noExterns m hm env s σ corr input inputs agree
    (config_module raw t h noExterns) children, fun vals hv => ?_⟩
  exact ⟨read_outputs raw t h noExterns m hm env s σ corr input inputs agree vals hv children,
    read_next raw t h noExterns m hm env s σ corr input inputs agree vals hv children⟩

end

end Silicon.Core.LowerProof
