import Silicon.Core.Typed

/-! A ranked hierarchy has a child whose prerequisites are available. -/
namespace Silicon.Core.Typed

private theorem minimum_member (xs : List α) (q : α → Nat) (h : xs ≠ []) :
    ∃ x ∈ xs, ∀ y ∈ xs, q x ≤ q y := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    by_cases ht : xs = []
    · subst xs
      exact ⟨a, by simp, by simp⟩
    · obtain ⟨b, hb, hm⟩ := ih ht
      by_cases hab : q a ≤ q b
      · refine ⟨a, by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans hab (hm y hy)
      · refine ⟨b, by simp [hb], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact hm y hy

private theorem ready_member (pending : List Core.Module) (seen : List String)
    (q : String → Nat) (nonempty : pending ≠ [])
    (closed : ∀ m ∈ pending, ∀ c ∈ childNames m,
      c ∈ seen ∨ ∃ child ∈ pending, child.name = c ∧ q c < q m.name) :
    ∃ m ∈ pending, (childNames m).all seen.contains = true := by
  obtain ⟨m, hm, least⟩ := minimum_member pending (fun m => q m.name) nonempty
  refine ⟨m, hm, List.all_eq_true.mpr ?_⟩
  intro c hc
  rcases closed m hm c hc with hs | ⟨child, hchild, he, hl⟩
  · simpa using hs
  · have := least child hchild
    rw [he] at this
    omega

theorem orderModules_complete (fuel : Nat) (seen : List String)
    (pending : List Core.Module) (q : String → Nat) (bound : pending.length ≤ fuel)
    (closed : ∀ m ∈ pending, ∀ c ∈ childNames m,
      c ∈ seen ∨ ∃ child ∈ pending, child.name = c ∧ q c < q m.name) :
    ∃ sorted, orderModules fuel seen pending = some sorted ∧
      sorted.Perm pending ∧ ordered seen sorted = true := by
  induction fuel generalizing seen pending with
  | zero =>
    have hp : pending = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst pending
    exact ⟨[], rfl, .refl _, rfl⟩
  | succ fuel ih =>
    by_cases hp : pending = []
    · subst pending
      exact ⟨[], rfl, .refl _, rfl⟩
    · obtain ⟨m, hm, ready⟩ := ready_member pending seen q hp closed
      have exists_find : (pending.find? fun m => (childNames m).all seen.contains).isSome := by
        rw [List.isSome_find?]
        exact List.any_eq_true.mpr ⟨m, hm, ready⟩
      obtain ⟨chosen, hc⟩ := Option.isSome_iff_exists.mp exists_find
      have chosen_mem := List.mem_of_find?_eq_some hc
      have chosen_ready := List.find?_some hc
      have smaller : (pending.erase chosen).length ≤ fuel := by
        have := List.length_erase_of_mem chosen_mem
        omega
      have closed' : ∀ m ∈ pending.erase chosen, ∀ c ∈ childNames m,
          c ∈ chosen.name :: seen ∨
            ∃ child ∈ pending.erase chosen, child.name = c ∧ q c < q m.name := by
        intro m hm c hc
        rcases closed m (List.mem_of_mem_erase hm) c hc with hs | ⟨child, hch, he, hl⟩
        · exact Or.inl (List.mem_cons_of_mem _ hs)
        · by_cases hsame : child = chosen
          · subst child
            exact Or.inl (by simp [he])
          · exact Or.inr ⟨child, List.mem_erase_of_ne hsame |>.mpr hch, he, hl⟩
      obtain ⟨rest, hr, perm, ho⟩ := ih (chosen.name :: seen) (pending.erase chosen)
        smaller closed'
      refine ⟨chosen :: rest, ?_, ?_, ?_⟩
      · simp [orderModules, hp, hc, hr]
      · exact (List.Perm.cons chosen perm).trans (List.perm_cons_erase chosen_mem).symm
      · simp [ordered, chosen_ready, ho]

end Silicon.Core.Typed
