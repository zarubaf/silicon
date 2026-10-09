import Silicon.Core.Proof.Lower.DesignItems

/-!
Model replacement keeps each item name and port list. A memory model has no instance.
-/
namespace Silicon.Core.LowerProof

theorem withModels_items (configs : List MemConfig) (d : Mlir.Design) :
    (d.withModels configs).items = d.items.map (Mlir.Item.withModels configs) := rfl

theorem find_config (configs : List MemConfig) (c : MemConfig) (hc : c ∈ configs) :
    configs.find? (·.moduleName == c.moduleName) = some c := by
  cases found : configs.find? (·.moduleName == c.moduleName) with
  | none =>
    have := List.find?_eq_none.mp found c hc
    simp at this
  | some c' =>
    have same : c'.moduleName = c.moduleName := by simpa using List.find?_some found
    rw [moduleName_injective same]

theorem image_config (configs : List MemConfig) (c : MemConfig) (hc : c ∈ configs) :
    Mlir.Item.withModels configs (.extern c.moduleName c.ports) = .module (memModel c) := by
  simp [Mlir.Item.withModels, find_config configs c hc]

theorem image_name {configs : List MemConfig} (item : Mlir.Item) :
    (Mlir.Item.withModels configs item).name = item.name := by
  cases item with
  | module m => rfl
  | extern name ports =>
    dsimp only [Mlir.Item.withModels]
    cases hc : configs.find? (·.moduleName == name) with
    | none => rfl
    | some c =>
      simp only
      split
      · have named : c.moduleName = name := by simpa using List.find?_some hc
        exact named
      · rfl

theorem image_ports {configs : List MemConfig} (item : Mlir.Item) :
    (Mlir.Item.withModels configs item).ports = item.ports := by
  cases item with
  | module m => rfl
  | extern name ports =>
    dsimp only [Mlir.Item.withModels]
    cases hc : configs.find? (·.moduleName == name) with
    | none => rfl
    | some c =>
      simp only
      split
      · rename_i same
        exact same.symm
      · rfl

theorem image_module {configs : List MemConfig} (item : Mlir.Item) (m : Mlir.Module)
    (h : Mlir.Item.withModels configs item = .module m) :
    item = .module m ∨ ∃ c, m = memModel c := by
  cases item with
  | module m' => exact Or.inl h
  | extern name ports =>
    dsimp only [Mlir.Item.withModels] at h
    cases hc : configs.find? (·.moduleName == name) with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      simp only at h
      split at h
      · cases h
        exact Or.inr ⟨c, rfl⟩
      · cases h

theorem find_unique (items : List Mlir.Item) (unique : (items.map Mlir.Item.name).Nodup)
    (item : Mlir.Item) (hi : item ∈ items) :
    items.find? (·.name == item.name) = some item := by
  induction items with
  | nil => cases hi
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · have ne : first.name ≠ item.name := fun eq =>
        unique.1 (eq ▸ List.mem_map_of_mem hi)
      simp [ne, ih unique.2 hi]

theorem signature_of_mem (d : Mlir.Design) (unique : (d.items.map Mlir.Item.name).Nodup)
    (item : Mlir.Item) (hi : item ∈ d.items) : d.signature item.name = some item.ports := by
  unfold Mlir.Design.signature
  rw [find_unique d.items unique item hi]
  rfl

theorem memModel_plain (c : MemConfig) :
    ∀ entry ∈ (memModel c).body, isInstance entry.2 = false := by
  intro entry he
  simp only [memModel, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with (⟨r, _, rfl⟩ | ⟨w, _, rfl | rfl⟩) | rfl <;> rfl

theorem module_transport (d₁ d₂ : Mlir.Design) (m : Mlir.Module) (wf : m.WellFormed d₁)
    (plain : ∀ entry ∈ m.body, isInstance entry.2 = false) : m.WellFormed d₂ := by
  obtain ⟨ports, defs, insts, entries, outputs, types⟩ := wf
  refine ⟨ports, defs, insts, fun entry he => ?_, outputs, types⟩
  obtain ⟨length, valid, operands, _⟩ := entries entry he
  refine ⟨length, valid, operands, ?_⟩
  have := plain entry he
  obtain ⟨names, op⟩ := entry
  cases op <;> simp_all [isInstance]

theorem memModel_wf (d : Mlir.Design) (c : MemConfig) : (memModel c).WellFormed d :=
  module_transport _ d _ ((memModel_wellFormed c).2.2.1 _ (List.mem_singleton_self _))
    (memModel_plain c)

theorem memModel_ports (c : MemConfig) : ((c.ports).map Mlir.Port.name).Nodup :=
  (memModel_wellFormed c).2.1 _ (List.mem_singleton_self _)

theorem ordered_children (seen : List String) (modules : List Core.Module)
    (h : Typed.ordered seen modules = true) (j : Nat) (hj : j < modules.length)
    (child : String) (hc : child ∈ Typed.childNames modules[j]) :
    child ∈ seen ∨ ∃ k, ∃ hk : k < j, modules[k].name = child := by
  induction modules generalizing seen j with
  | nil => cases hj
  | cons first rest ih =>
    simp only [Typed.ordered, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    cases j with
    | zero => exact Or.inl (h.1 child hc)
    | succ j =>
      rcases ih (first.name :: seen) h.2 j (by simpa using hj) hc with hs | ⟨k, hk, named⟩
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inr ⟨0, Nat.zero_lt_succ _, rfl⟩
        · exact Or.inl hs
      · exact Or.inr ⟨k + 1, Nat.succ_lt_succ hk, named⟩

end Silicon.Core.LowerProof
