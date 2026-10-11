-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.GraphReach

/-! Indexed graph edges retain the first row for each source. -/
namespace Silicon.Core.GraphIndex

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]

abbrev Index (α : Type) [BEq α] [Hashable α] := Std.HashMap α (List α)

omit [Hashable α] [LawfulHashable α] in
theorem lookup_mem {g : List (α × List α)} {x : α} {ys : List α}
    (h : g.lookup x = some ys) : (x, ys) ∈ g := by
  obtain ⟨pre, post, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

omit [LawfulHashable α] in
theorem toList_lookup (index : Index α) (x : α) :
    index.toList.lookup x = index[x]? := by
  cases hl : index.toList.lookup x with
  | some ys =>
    exact (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (lookup_mem hl)).symm
  | none =>
    cases hi : index[x]? with
    | none => rfl
    | some ys =>
      have hm := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hi
      have hs : (index.toList.lookup x).isSome = true :=
        List.lookup_isSome_iff.mpr ⟨(x, ys), hm, by simp⟩
      simp [hl] at hs

def add (index : Index α) (source target : α) : Index α :=
  index.insert target (source :: (index[target]?).getD [])

theorem add_mem (index : Index α) (source target x y : α) :
    x ∈ ((add index source target)[y]?).getD [] ↔
      (x = source ∧ y = target) ∨ x ∈ (index[y]?).getD [] := by
  simp only [add, Std.HashMap.getElem?_insert]
  by_cases h : target = y
  · subst y
    simp
  · simp [h, Ne.symm h]

def addRow (index : Index α) (source : α) (targets : List α) : Index α :=
  targets.foldl (fun index target => add index source target) index

theorem addRow_mem (index : Index α) (source : α) (targets : List α) (x y : α) :
    x ∈ ((addRow index source targets)[y]?).getD [] ↔
      (x = source ∧ y ∈ targets) ∨ x ∈ (index[y]?).getD [] := by
  induction targets generalizing index with
  | nil => simp [addRow]
  | cons target targets ih =>
    simp only [addRow, List.foldl_cons]
    change x ∈ ((addRow (add index source target) source targets)[y]?).getD [] ↔ _
    rw [ih, add_mem]
    simp only [List.mem_cons]
    grind

def addRows (index : Index α) (rows : List (α × List α)) : Index α :=
  rows.foldl (fun index row => addRow index row.1 row.2) index

theorem addRows_mem (index : Index α) (rows : List (α × List α)) (x y : α) :
    x ∈ ((addRows index rows)[y]?).getD [] ↔
      (∃ row ∈ rows, x = row.1 ∧ y ∈ row.2) ∨ x ∈ (index[y]?).getD [] := by
  induction rows generalizing index with
  | nil => simp [addRows]
  | cons row rows ih =>
    simp only [addRows, List.foldl_cons]
    change x ∈ ((addRows (addRow index row.1 row.2) rows)[y]?).getD [] ↔ _
    rw [ih, addRow_mem]
    simp only [List.mem_cons]
    grind

def reverse (index : Index α) : Index α := addRows {} index.toList

theorem reverse_mem (index : Index α) (x y : α) :
    x ∈ ((reverse index)[y]?).getD [] ↔ y ∈ (index[x]?).getD [] := by
  rw [reverse, addRows_mem]
  simp only [Std.HashMap.getElem?_empty, Option.getD_none, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨source, targets⟩, hm, rfl, hy⟩
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm]
    exact hy
  · intro hy
    cases hi : index[x]? with
    | none => simp [hi] at hy
    | some targets =>
      refine ⟨(x, targets), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hi, rfl, ?_⟩
      simpa [hi] using hy

theorem reverses (index : Index α) :
    GraphReach.Reverses index.toList (reverse index).toList := by
  intro x y
  rw [toList_lookup, toList_lookup, reverse_mem]

theorem reverses_of_lookup (g : List (α × List α)) (index : Index α)
    (he : ∀ x, index[x]? = g.lookup x) : GraphReach.Reverses g (reverse index).toList := by
  intro x y
  rw [toList_lookup, reverse_mem, he]

def nodes (rows : List (α × List α)) : List α := rows.flatMap fun row => row.1 :: row.2

omit [Hashable α] [LawfulHashable α] in
theorem edge_nodes (g : List (α × List α)) (x y : α)
    (h : y ∈ (g.lookup x).getD []) : x ∈ nodes g ∧ y ∈ nodes g := by
  cases he : g.lookup x with
  | none => simp [he] at h
  | some targets =>
    have hm := lookup_mem he
    constructor
    · exact List.mem_flatMap.mpr ⟨(x, targets), hm, by simp⟩
    · exact List.mem_flatMap.mpr ⟨(x, targets), hm,
        List.mem_cons_of_mem _ (by simpa [he] using h)⟩

end Silicon.Core.GraphIndex
