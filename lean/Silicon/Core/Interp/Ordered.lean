-- SPDX-License-Identifier: Apache-2.0
import Std.Data.DHashMap.Lemmas

/-! A finite table stores function values before their consumers request them. -/
namespace Silicon.Core.Interp

variable {α : Type} {Value : α → Type} [BEq α] [Hashable α] [LawfulBEq α]

/-! Store finite function values before the evaluator sorts or visits nodes. -/
def tabulate (f : ∀ a, Value a) (nodes : List α) : Std.DHashMap α Value :=
  nodes.foldr (fun a cache => cache.insert a (f a)) ∅

theorem tabulate_get (f : ∀ a, Value a) (nodes : List α) (a : α) (h : a ∈ nodes) :
    (tabulate f nodes).get? a = some (f a) := by
  induction nodes with
  | nil => simp at h
  | cons b rest ih =>
    simp only [tabulate, List.foldr_cons, Std.DHashMap.get?_insert]
    split
    next eq =>
      have eq := eq_of_beq eq
      subst a
      rfl
    next ne =>
      exact ih (List.mem_cons.mp h |>.resolve_left (fun eq => ne (by simp [eq])))

structure Table (f : ∀ a, Value a) where
  cache : Std.DHashMap α Value
  valid : ∀ a, cache.get? a = some (f a)

def Table.get {f : ∀ a, Value a} (table : Table f) (a : α) : Value a :=
  (table.cache.get? a).get (by rw [table.valid]; trivial)

@[simp] theorem Table.get_eq {f : ∀ a, Value a} (table : Table f) : table.get = f := by
  funext a
  simp [Table.get, table.valid]

def indexed (f : ∀ a, Value a) (nodes : List α) (complete : ∀ a, a ∈ nodes) : Table f :=
  ⟨tabulate f nodes, fun a => tabulate_get f nodes a (complete a)⟩

end Silicon.Core.Interp
