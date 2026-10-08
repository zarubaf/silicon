import Std

/-! Distinct owners give disjoint lists of entries. -/
namespace List

theorem flatMap_nodup_owners {α β κ : Type} (xs : List α) (f : α → List β)
    (label : α → Option κ) (owner : β → κ)
    (labels : (xs.filterMap label).Nodup)
    (within : ∀ a ∈ xs, (f a).Nodup)
    (owns : ∀ a ∈ xs, ∀ b ∈ f a, label a = some (owner b)) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have wt : ∀ a ∈ xs, (f a).Nodup := fun a ha => within a (List.mem_cons_of_mem _ ha)
    have ot : ∀ a ∈ xs, ∀ b ∈ f a, label a = some (owner b) :=
      fun a ha => owns a (List.mem_cons_of_mem _ ha)
    have lt : (xs.filterMap label).Nodup := by
      cases hl : label a with
      | none => simpa [List.filterMap_cons, hl] using labels
      | some v => exact (List.nodup_cons.mp (by simpa [List.filterMap_cons, hl] using labels)).2
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨within a (List.mem_cons_self ..), ih lt wt ot, ?_⟩
    intro x hx y hy he
    subst y
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    have ha := owns a (List.mem_cons_self ..) x hx
    have hb := ot b hb x hxb
    simp only [List.filterMap_cons, ha, List.nodup_cons] at labels
    apply labels.1
    exact List.mem_filterMap.mpr ⟨b, by assumption, hb⟩

end List
