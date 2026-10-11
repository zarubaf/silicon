-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Order
import Silicon.Core.Reassemble
import Silicon.Core.StatementOrder

/-! The final checks follow from the ordering and exact module erasures. -/
namespace Silicon.Core.Typed

theorem elaborateDesign_of_modules (d : Core.Design) (sorted : List Core.Module)
    (bodies : List Module) (names : (d.items.map Item.name).Nodup)
    (order : orderModules (modules d).length (externNames d) (modules d) = some sorted)
    (permutation : sorted.Perm (modules d)) (hierarchy : ordered (externNames d) sorted = true)
    (elaborated : elaborateModules d sorted = some bodies)
    (erased : bodies.map Module.erase = sorted) :
    ∃ t, elaborateDesign d = some t := by
  have extnames : (d.items.filterMap (fun i => match i with
      | .extern e => some e | _ => none)).map (·.name) = externNames d := by
    simp only [List.map_filterMap, externNames]
    congr 1
    funext i
    cases i <;> rfl
  unfold elaborateDesign
  simp only [order, bind, Option.bind_some, dite_eq_left permutation]
  have orderedBodies : ordered ((d.items.filterMap (fun i => match i with
      | .extern e => some e | _ => none)).map (·.name)) (bodies.map Module.erase) = true := by
    rw [extnames, erased]
    exact hierarchy
  split
  · rename_i impossible
    rw [elaborated] at impossible
    contradiction
  · rename_i bs found
    rw [elaborated] at found
    cases found
    split
    · split
      · exact ⟨_, rfl⟩
      · rename_i failure
        exfalso
        apply failure
        apply assembleDesign_erase_of_modules d _ _ _ _ _ names rfl rfl rfl rfl
        rw [erased]
        exact permutation
    · rename_i failure
      exact False.elim (failure orderedBodies)

/-! Each module succeeds once grouping preserves its statements and its graph has ranks. -/
theorem elaborateModules_of_groups (d : Core.Design) (ms : List Core.Module)
    (ready : ∀ m ∈ ms, ∃ body groups,
      m.body.mapM (statement d (context d m)) = some body ∧
      groupStatements (context d m) (portsOf d) body = some groups ∧
      equationsErase groups = m.body ∧
      ∃ ranks, FastRanks.certificate (Deps.graph m (designDeps d d.depsFuel)) =
        some ranks) :
    ∃ bodies, elaborateModules d ms = some bodies ∧ bodies.map Module.erase = ms := by
  induction ms with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨body, groups, hb, hg, he, ranks, hr⟩ := ready m (by simp)
    simp only [designDeps] at hr
    obtain ⟨rest, hrest, erased⟩ := ih (fun m hm => ready m (by simp [hm]))
    unfold elaborateModules
    simp only [statements, hb, bind, Option.bind_some]
    split
    · rename_i failure
      rw [hr] at failure
      contradiction
    · simp only [hg, Option.bind_some]
      split
      · simp only [hrest, Option.bind_some, pure]
        refine ⟨_, rfl, ?_⟩
        simp only [List.map_cons, Module.erase, he, erased]
      · contradiction

end Silicon.Core.Typed
