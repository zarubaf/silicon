-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.DesignNames

/-!
A checked design without externs lowers to its source modules and one memory model per
memory configuration.
-/
namespace Silicon.Core.LowerProof

theorem check_elaborate (d : Core.Design) (t : Typed.Design) (h : check d = .ok t) :
    Typed.elaborateDesign d = some t := by
  unfold check at h
  split at h
  · contradiction
  · rename_i he
    split at h
    · rename_i typed accepted
      cases h
      exact accepted
    · rename_i failure
      obtain ⟨typed, accepted⟩ := Check.elaborate_complete d ((Check.no_errors d).mp he)
      rw [failure] at accepted
      contradiction

theorem bodies_perm (d : Core.Design) (t : Typed.Design) (h : Typed.elaborateDesign d = some t) :
    (t.bodies.map Typed.Module.erase).Perm (Typed.modules d) := by
  simp only [Typed.elaborateDesign, bind, Option.bind_eq_some_iff] at h
  obtain ⟨sorted, _, h⟩ := h
  split at h <;> try contradiction
  rename_i perm
  split at h <;> try contradiction
  rename_i bodies hb
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rw [Typed.elaborateModules_erase d sorted bodies hb]
  exact perm

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
include h

theorem body_names_nodup : (t.bodies.map Typed.Module.name).Nodup := by
  have perm := bodies_perm raw t (check_elaborate raw t h)
  have names := (module_wf raw t h).1.1.1
  have modules : ((Typed.modules raw).map Core.Module.name).Sublist (raw.items.map Item.name) := by
    unfold Typed.modules
    generalize raw.items = items
    induction items with
    | nil => exact List.Sublist.refl _
    | cons item items ih =>
      cases item <;> simp only [List.filterMap_cons, List.map_cons]
      · exact ih.cons_cons _
      · exact ih.cons _
  have same : t.bodies.map Typed.Module.name =
      (t.bodies.map Typed.Module.erase).map Core.Module.name := by
    rw [List.map_map]
    rfl
  rw [same]
  exact (perm.map _).nodup_iff.mpr (names.sublist modules)

theorem body_name_legal (b : Typed.Module) (hb : b ∈ t.bodies) :
    Rules.invalidName b.name = false :=
  (module_wf raw t h).1.1.2 b.name (List.mem_map.mpr ⟨.module b.erase,
    module_item raw t h b hb, rfl⟩)

theorem raw_item_module (noExterns : t.externs = []) (item : Item) (hi : item ∈ raw.items) :
    ∃ b ∈ t.bodies, item = .module b.erase := by
  have erase := check_sound_erase raw t h
  rw [← erase] at hi
  obtain ⟨n, _, found⟩ := List.mem_filterMap.mp hi
  split at found
  · rename_i b hb
    cases found
    exact ⟨b, List.mem_of_find?_eq_some hb, rfl⟩
  · rw [noExterns] at found
    cases found

end

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  generalize hn : l.length = n
  induction n using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => exact List.nodup_nil
    | cons a as =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        have := (List.mem_filter.mp (List.mem_eraseDups.mp member)).2
        simp at this
      · subst hn
        exact ih _ (Nat.lt_succ_of_le (List.length_filter_le _ _)) _ rfl

theorem memoryConfigs_mem (t : Typed.Design) (c : MemConfig) :
    c ∈ memoryConfigs t ↔ ∃ b ∈ t.bodies, c ∈ (Lower.module b).2 := by
  unfold memoryConfigs Lower.uniqueConfigs
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_eraseDups, List.mem_flatMap]

theorem memoryConfigs_nodup (t : Typed.Design) : (memoryConfigs t).Nodup := by
  unfold memoryConfigs Lower.uniqueConfigs
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (eraseDups_nodup _)

theorem lower_items (t : Typed.Design) (noExterns : t.externs = []) :
    (lower t).items.Perm (t.bodies.map (fun b => Mlir.Item.module (Lower.module b).1) ++
      (memoryConfigs t).map (fun c => Mlir.Item.extern c.moduleName c.ports)) := by
  unfold lower
  simp only [noExterns, List.map_nil, List.append_nil]
  refine (List.mergeSort_perm _ _).trans ?_
  rw [List.map_map]
  apply List.Perm.of_eq
  congr 2
  unfold memoryConfigs
  rw [List.flatMap_map]

end Silicon.Core.LowerProof
