import Std.Data.HashMap.Lemmas

/-! A hash index answers association-list lookups in constant expected time. -/
namespace Silicon.Core

/-! The first source entry wins when a key occurs more than once. -/
def firstIndex {β α : Type} [BEq β] [Hashable β] : List (β × α) → Std.HashMap β α
  | [] => {}
  | (k, v) :: rest => (firstIndex rest).insert k v

theorem firstIndex_lookup {β α : Type} [BEq β] [LawfulBEq β] [Hashable β] [LawfulHashable β]
    (entries : List (β × α)) (k : β) : (firstIndex entries)[k]? = entries.lookup k := by
  induction entries with
  | nil => simp [firstIndex]
  | cons a rest ih =>
    rcases a with ⟨key, v⟩
    simp only [firstIndex, Std.HashMap.getElem?_insert, List.lookup_cons, ih, beq_iff_eq]
    by_cases h : key = k
    · subst key; simp
    · simp [h, show (k == key) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]

end Silicon.Core
