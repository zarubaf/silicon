import Silicon.Core.Proof.Lower.MemoryArgs

/-!
Each source instance and each memory becomes one instance op of the lowered module.
Each memory instance calls the memory model of its configuration.
-/
namespace Silicon.Core.LowerProof

open Semantics

theorem substitute_instance (f : String → String) (inst callee : String)
    (args : List (String × String × Mlir.Ty)) (results : List (String × Mlir.Ty)) :
    Lower.substitute f (.instance inst callee args results) =
      .instance inst callee (args.map (renameArg f)) results := by
  simp only [Lower.substitute, Mlir.Op.instance.injEq, true_and, and_true]
  apply List.map_congr_left
  intro a _
  rfl

theorem findModule_some (d : Mlir.Design) (name : String) (M : Mlir.Module)
    (found : d.findModule name = some M) : Mlir.Item.module M ∈ d.items ∧ M.name = name := by
  unfold Mlir.Design.findModule at found
  obtain ⟨item, hi, hm⟩ := List.exists_of_findSome?_eq_some found
  cases item with
  | module other =>
    simp only at hm
    split at hm
    · cases hm
      exact ⟨hi, by assumption⟩
    · cases hm
  | extern => cases hm

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)

theorem memory_entry_body (i : Nat) (p : Pos) (memory : String) (w depth : Nat) (clk : String)
    (target) (ws) (he : Typed.Equation.mem i p memory w depth clk target ws ∈ m.body) :
    (((memReads (finalState m) memory).map fun r => s!"{memory}.r{r.index}_data"),
      Mlir.Op.instance memory (memConfig (finalState m) memory w depth).moduleName
        ((memArgs (finalState m) memory w depth clk).map (renameArg (rename m)))
        (memResults (finalState m) memory w)) ∈ (Lower.module m).1.body := by
  rw [module_body]
  apply List.mem_map.mpr
  refine ⟨(memEntry (finalState m) memory w depth clk).1, ?_, ?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨_, he, rfl⟩, rfl⟩
  · simp only [memEntry, substitute_instance]

include hm in
theorem memory_config (i : Nat) (p : Pos) (memory : String) (w depth : Nat) (clk : String)
    (target) (ws) (he : Typed.Equation.mem i p memory w depth clk target ws ∈ m.body) :
    memConfig (finalState m) memory w depth ∈ memoryConfigs t := by
  apply (memoryConfigs_mem t _).mpr
  refine ⟨m, hm, ?_⟩
  change _ ∈ ((Lower.memoryEntries m (Lower.statementState m)).map Prod.snd).reverse
  rw [List.mem_reverse]
  exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨_, he, rfl⟩, rfl⟩

include h noExterns in
theorem memory_child (c : MemConfig) (hc : c ∈ memoryConfigs t) (child : Mlir.Module)
    (found : ((lower t).withModels (memoryConfigs t)).findModule c.moduleName = some child) :
    child = memModel c := by
  obtain ⟨member, named⟩ := findModule_some _ _ _ found
  have image := config_in_design t noExterns c hc
  have unique := design_names raw t h noExterns
  have same : Mlir.Item.module child =
      Mlir.Item.withModels (memoryConfigs t) (.extern c.moduleName c.ports) := by
    have hfind := find_unique _ unique _ member
    have hfind' := find_unique _ unique _ image
    rw [image_name] at hfind'
    change ((lower t).withModels (memoryConfigs t)).items.find? (·.name == child.name) = _ at hfind
    rw [named] at hfind
    exact Option.some.inj (hfind.symm.trans hfind')
  rcases image_module _ _ same.symm with bad | ⟨c', rfl⟩
  · cases bad
  · have : c'.moduleName = c.moduleName := named
    rw [moduleName_injective this]

include h noExterns hm in
theorem module_instNames (M : Mlir.Module) (same : M = (Lower.module m).1) :
    (instNames M).Nodup := by
  subst same
  exact (body_wellFormed raw t h noExterns m hm).2.2.1

theorem memory_outputs (memory : String) (w depth : Nat) (k : Nat)
    (hk : k < (memReads (finalState m) memory).length) :
    ((memReads (finalState m) memory).map fun r => s!"{memory}.r{r.index}_data")[k]'(by
      simpa using hk) = s!"{memory}.r{k}_data" ∧
    (memModel (memConfig (finalState m) memory w depth)).outputs[k]? = some s!"r{k}_data" := by
  constructor
  · simp only [List.getElem_map]
    rw [memReads_index m memory k hk]
  · simp [memModel, memConfig, List.getElem?_map, List.getElem?_range hk]

end

end Silicon.Core.LowerProof
