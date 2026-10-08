import Silicon.Core.Semantics.EquationSolution
import Std.Data.DHashMap.Lemmas

/-! A rank-ordered pass stores each equation value for later reads. -/
namespace Silicon.Core.Interp

open Semantics.EquationSolution

variable {α : Type} {Value : α → Type} [BEq α] [Hashable α] [LawfulBEq α]

def evaluate (s : System α Value) (nodes : List α) (cache : Std.DHashMap α Value) :
    Std.DHashMap α Value :=
  nodes.foldl (fun cache node => cache.insert node (s.rhs (fun n => cache.getD n (s.initial n))
    node)) cache

theorem evaluate_correct (s : System α Value) (nodes : List α)
    (sorted : nodes.Pairwise (fun a b => s.rank a ≤ s.rank b))
    (cache : Std.DHashMap α Value)
    (ready : ∀ n, n ∉ nodes → cache.getD n (s.initial n) = solution s n) :
    ∀ n, (evaluate s nodes cache).getD n (s.initial n) = solution s n := by
  induction nodes generalizing cache with
  | nil => exact fun n => ready n (by simp)
  | cons node rest ih =>
    obtain ⟨lower, sorted⟩ := List.pairwise_cons.mp sorted
    have value : s.rhs (fun n => cache.getD n (s.initial n)) node = solution s node := by
      rw [solution_eq s node]
      apply s.respects
      intro dep hd
      apply ready
      intro member
      rcases List.mem_cons.mp member with same | member
      · subst dep; omega
      · have := lower dep member; omega
    apply ih sorted
    intro n absent
    rw [Std.DHashMap.getD_insert]
    split
    next eq =>
      have eq := eq_of_beq eq
      subst n
      exact value
    next ne =>
      apply ready
      simp only [List.mem_cons, not_or]
      exact ⟨fun eq => ne (by simp [eq]), absent⟩

def orderedCache (s : System α Value) (nodes : List α) : Std.DHashMap α Value :=
  evaluate s (nodes.mergeSort (fun a b => s.rank a ≤ s.rank b)) ∅

def ordered (s : System α Value) (nodes : List α) : ∀ n, Value n :=
  let cache := orderedCache s nodes
  fun n => cache.getD n (s.initial n)

theorem ordered_eq_solution (s : System α Value) (nodes : List α)
    (complete : ∀ n, n ∈ nodes) : ordered s nodes = solution s := by
  funext n
  apply evaluate_correct
  · have sorted := List.pairwise_mergeSort
      (le := fun a b => decide (s.rank a ≤ s.rank b))
      (by intros; simp_all; omega) (by intros; simp; omega) nodes
    simpa using sorted
  · intro n absent
    exact False.elim (absent (List.mem_mergeSort.mpr (complete n)))

end Silicon.Core.Interp
