import Std.Data.HashMap.Lemmas

/-! A hash index answers association-list queries in constant expected time. -/
namespace Silicon.Core

variable {β α : Type} [BEq β] [Hashable β]

/-! The first source entry wins when a key occurs more than once. -/
def firstIndex (entries : List (β × α)) : Std.HashMap β α :=
  entries.foldr (fun (k, v) index => index.insert k v) {}

/-! Each key collects its values in source order. -/
def groupIndex (entries : List (β × α)) : Std.HashMap β (List α) :=
  entries.foldr (fun (k, v) index => index.insert k (v :: (index[k]?).getD [])) {}

variable [LawfulBEq β] [LawfulHashable β]

theorem firstIndex_lookup (entries : List (β × α)) (k : β) :
    (firstIndex entries)[k]? = entries.lookup k := by
  induction entries with
  | nil => simp [firstIndex]
  | cons a rest ih =>
    rcases a with ⟨key, v⟩
    simp only [firstIndex, List.foldr_cons] at ih ⊢
    simp only [Std.HashMap.getElem?_insert, List.lookup_cons, ih, beq_iff_eq]
    by_cases h : key = k
    · subst key; simp
    · simp [h, show (k == key) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]

theorem groupIndex_values (entries : List (β × α)) (k : β) :
    ((groupIndex entries)[k]?).getD [] =
      entries.filterMap fun e => if e.1 == k then some e.2 else none := by
  induction entries with
  | nil => simp [groupIndex]
  | cons a rest ih =>
    rcases a with ⟨key, v⟩
    simp only [groupIndex, List.foldr_cons] at ih ⊢
    simp only [Std.HashMap.getElem?_insert, List.filterMap_cons, beq_iff_eq]
    by_cases h : key = k
    · subst key; simp [ih]
    · simp [h, ih]

theorem groupIndex_filterMap {γ : Type} (xs : List γ) (f : γ → Option (β × α)) (k : β) :
    ((groupIndex (xs.filterMap f))[k]?).getD [] =
      xs.filterMap fun x => (f x).bind fun e => if e.1 == k then some e.2 else none := by
  rw [groupIndex_values, List.filterMap_filterMap]

end Silicon.Core
