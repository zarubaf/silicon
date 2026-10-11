-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.GraphDFSBase
import Silicon.Core.GraphDFSInvariant

/-! Entering and finishing a node preserve the depth-first search state. -/
namespace Silicon.Core.GraphDFS

open GraphReach GraphDFSInvariant

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {g : List (α × List α)} {nodes : List α}

theorem State.Valid.push (state : State α) (active : List α) (x : α)
    (h : State.Valid g nodes active state) (unseen : state.seen.contains x = false)
    (member : x ∈ nodes) :
    State.Valid g nodes (x :: active) { state with seen := state.seen.insert x } := by
  have fresh : x ∉ state.order ∧ x ∉ active := by
    have hs := h.seen_iff x
    simp only [unseen, Bool.false_eq_true, false_iff, not_or] at hs
    exact hs
  constructor
  · intro y
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    rw [h.seen_iff]
    simp only [List.mem_cons]
    grind
  · exact List.nodup_cons.mpr ⟨fresh.2, h.active_nodup⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact fresh.1
    · exact h.active_fresh y hy
  · intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact h.support (List.mem_append_left _ hy)
    · exact member
    · exact h.support (List.mem_append_right _ hy)
  · intro y hy
    rcases h.completed y hy with hc | ⟨a, ha, hp⟩
    · exact Or.inl hc
    · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hp⟩
  · exact h.ordered.push x
  · intro y hy z hz
    simp [h.closed y hy z hz]

omit [LawfulBEq α] [LawfulHashable α] in
theorem State.Valid.finish (state : State α) (active : List α) (x : α)
    (h : State.Valid g nodes (x :: active) state)
    (children : ∀ y ∈ (g.lookup x).getD [], state.seen.contains y = true)
    (ancestors : ∀ a ∈ active, Reachable g a x) :
    State.Valid g nodes active { state with order := x :: state.order } := by
  have closure : ∀ f ∈ x :: state.order, ∀ y ∈ (g.lookup f).getD [],
      y ∈ x :: state.order ∨ y ∈ active := by
    intro f hf y hy
    have seen : state.seen.contains y = true := by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact children y hy
      · exact h.closed f hf y hy
    have hm := (h.seen_iff y).mp seen
    simp only [List.mem_cons] at hm ⊢
    grind
  constructor
  · intro y
    rw [h.seen_iff]
    simp only [List.mem_cons]
    grind
  · exact (List.nodup_cons.mp h.active_nodup).2
  · intro y hy hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (List.nodup_cons.mp h.active_nodup).1 hy
    · exact h.active_fresh y (List.mem_cons_of_mem _ hy) hm
  · intro y hy
    apply h.support
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    grind
  · exact DoneInvariant.finish h.completed closure ancestors
  · exact h.ordered.finish (h.active_fresh x (by simp)) h.completed
  · intro y hy z hz
    rcases List.mem_cons.mp hy with rfl | hy
    · exact children z hz
    · exact h.closed y hy z hz

end Silicon.Core.GraphDFS
