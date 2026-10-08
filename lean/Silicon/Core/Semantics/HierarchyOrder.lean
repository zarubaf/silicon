import Silicon.Core.Check

/-! The checker supplies a concrete child-first order for the certified design. -/
namespace Silicon.Core.Semantics

open Typed

private theorem order_exists (d : Core.Design) (wf : WellFormed d) :
    ∃ sorted, orderModules (modules d).length (externNames d) (modules d) = some sorted := by
  obtain ⟨sorted, hs, _, _⟩ := Check.hierarchy_order d wf.2.1 wf.2.2.2.2.2.2.2.2.1
  exact ⟨sorted, hs⟩

def moduleOrder (d : Core.Design) (wf : WellFormed d) : List Core.Module :=
  (orderModules (modules d).length (externNames d) (modules d)).get
    (by obtain ⟨sorted, hs⟩ := order_exists d wf; simp [hs])

theorem moduleOrder_spec (d : Core.Design) (wf : WellFormed d) :
    (moduleOrder d wf).Perm (modules d) ∧ ordered (externNames d) (moduleOrder d wf) = true := by
  obtain ⟨sorted, hs, hp, ho⟩ := Check.hierarchy_order d wf.2.1 wf.2.2.2.2.2.2.2.2.1
  simpa [moduleOrder, hs] using And.intro hp ho

private def level (names : List String) (name : String) : Nat :=
  if name ∈ names then names.idxOf name + 1 else 0

private theorem level_pos (names : List String) (name : String) (hm : name ∈ names) :
    0 < level names name := by simp [level, hm]

private theorem level_cons (names : List String) (first name : String) (hne : name ≠ first) :
    level (first :: names) name = if name ∈ names then level names name + 1 else 0 := by
  simp [level, List.idxOf_cons, hne, Ne.symm hne]
  split <;> simp_all

private theorem ordered_lower (seen : List String) (ms : List Core.Module)
    (ho : ordered seen ms = true) (hn : (ms.map (·.name)).Nodup)
    (disjoint : ∀ n ∈ seen, n ∉ ms.map (·.name))
    (m : Core.Module) (hm : m ∈ ms) (child : String) (hc : child ∈ childNames m) :
    level (ms.map (·.name)) child < level (ms.map (·.name)) m.name := by
  induction ms generalizing seen with
  | nil => simp at hm
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [ordered, Bool.and_eq_true] at ho
    rcases List.mem_cons.mp hm with rfl | hm
    · have hs : child ∈ seen := by simpa using List.all_eq_true.mp ho.1 child hc
      have ha := disjoint child hs
      rw [level, ite_eq_right ha]
      simp [level]
    · have member : m.name ∈ rest.map (·.name) := List.mem_map.mpr ⟨m, hm, rfl⟩
      have ne : m.name ≠ first.name := by intro he; exact hn.1 (he ▸ member)
      have lower := ih (first.name :: seen) ho.2 hn.2 (by
        intro n h
        rcases List.mem_cons.mp h with rfl | h
        · exact hn.1
        · exact fun hx => disjoint n h (List.mem_cons_of_mem _ hx)) hm
      rw [List.map_cons, level_cons _ _ _ ne]
      simp only [member, ↓reduceIte]
      by_cases he : child = first.name
      · subst child
        simp only [level, List.mem_cons_self, ↓reduceIte, List.idxOf_cons_self]
        have := level_pos _ _ member
        unfold level at this
        omega
      · rw [level_cons _ _ _ he]
        split <;> omega

/-! Module names receive their list position; extern names receive zero. -/
def moduleLevel (d : Core.Design) (wf : WellFormed d) (name : String) : Nat :=
  level ((moduleOrder d wf).map (·.name)) name

private theorem partition_names (items : List Item) :
    ((items.filterMap fun i => match i with
      | .module m => some m | _ => none).map (·.name) ++
      items.filterMap (fun i => match i with | .extern e => some e.name | _ => none)).Perm
        (items.map itemName) := by
  induction items with
  | nil => exact .refl _
  | cons item rest ih =>
    cases item with
    | module m => exact List.Perm.cons m.name ih
    | extern e => exact List.perm_middle.trans (List.Perm.cons e.name ih)

theorem moduleLevel_lower (d : Core.Design) (wf : WellFormed d)
    (m : Core.Module) (hm : m ∈ modules d) (child : String) (hc : child ∈ childNames m) :
    moduleLevel d wf child < moduleLevel d wf m.name := by
  have parts := (partition_names d.items).nodup_iff.mpr wf.1.1.1
  have names := List.nodup_append.mp parts
  have order := moduleOrder_spec d wf
  have perm := order.1.map (fun m => m.name)
  apply ordered_lower (externNames d) (moduleOrder d wf) order.2
    (perm.nodup_iff.mpr names.1)
  · intro n he hm
    exact names.2.2 n (perm.mem_iff.mp hm) n he rfl
  · exact order.1.mem_iff.mpr hm
  · exact hc

end Silicon.Core.Semantics
