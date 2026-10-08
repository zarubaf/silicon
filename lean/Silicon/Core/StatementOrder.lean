import Silicon.Core.Typed

/-! Source indices recover statement order after grouping of state updates. -/
namespace Silicon.Core.Typed

theorem sortIndexed_of_perm (parts : List (Nat × α)) (body : List α)
    (perm : parts.Perm (body.zipIdx.map fun (s, i) => (i, s))) :
    parts.mergeSort (fun a b => decide (a.1 ≤ b.1)) =
      body.zipIdx.map (fun (s, i) => (i, s)) := by
  let indexed := body.zipIdx.map fun (s, i) => (i, s)
  have sorted : ∀ (xs : List α) start,
      (xs.zipIdx start).Pairwise (fun a b => a.2 ≤ b.2) := by
    intro xs start
    induction xs generalizing start with
    | nil => simp
    | cons s ss ih =>
      simp only [List.zipIdx_cons, List.pairwise_cons]
      refine ⟨?_, ih _⟩
      intro x hx
      have := List.le_snd_of_mem_zipIdx hx
      omega
  have ordered : indexed.Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa [indexed, List.pairwise_map] using sorted body 0
  have merged := List.pairwise_mergeSort
    (le := fun a b : Nat × α => decide (a.1 ≤ b.1))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    parts
  have totalperm := (List.mergeSort_perm parts
    (fun a b => decide (a.1 ≤ b.1))).trans perm
  have exact_order := List.Perm.eq_of_pairwise (le := fun a b => a.1 ≤ b.1)
    (l₁ := parts.mergeSort (fun a b => decide (a.1 ≤ b.1)))
    (l₂ := indexed) (by
      intro a b ha hb hab hba
      have ha := totalperm.mem_iff.mp ha
      obtain ⟨⟨sa, ia⟩, hsa, ea⟩ := List.mem_map.mp ha
      obtain ⟨⟨sb, ib⟩, hsb, eb⟩ := List.mem_map.mp hb
      cases ea
      cases eb
      have idx : ia = ib := by simpa using Nat.le_antisymm hab hba
      subst ib
      have hsa := List.mk_mem_zipIdx_iff_getElem?.mp hsa
      have hsb := List.mk_mem_zipIdx_iff_getElem?.mp hsb
      rw [hsa] at hsb
      cases hsb
      rfl)
    (by simpa using merged) ordered totalperm
  exact exact_order

theorem equationsErase_of_raw_perm (groups : List (Equation ctx ports))
    (body : List Core.Stmt)
    (perm : ((groups.flatMap Equation.parts).map indexedErase).Perm
      (body.zipIdx.map fun (s, i) => (i, s))) : equationsErase groups = body := by
  have sorted := sortIndexed_of_perm _ body perm
  have commute := List.map_mergeSort
    (r := fun a b : Nat × Stmt ctx ports => decide (a.1 ≤ b.1))
    (s := fun a b : Nat × Core.Stmt => decide (a.1 ≤ b.1))
    (f := indexedErase) (l := groups.flatMap Equation.parts) (by intros; rfl)
  rw [← commute] at sorted
  have result := congrArg (List.map Prod.snd) sorted
  simp only [List.map_map, Function.comp_def, indexedErase] at result
  change equationsErase groups = body.zipIdx.map Prod.fst at result
  simpa only [List.zipIdx_map_fst] using result

end Silicon.Core.Typed
