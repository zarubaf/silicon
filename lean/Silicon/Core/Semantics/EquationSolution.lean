import Std

/-!
Each equation can read only nodes with lower rank. Iteration from any initial values
therefore gives a unique solution, even when the value type depends on the node.
-/
namespace Silicon.Core.Semantics.EquationSolution

structure System (α : Type) (Value : α → Type) where
  initial : ∀ node, Value node
  rank : α → Nat
  rhs : (∀ node, Value node) → ∀ node, Value node
  respects : ∀ node a b,
    (∀ dep, rank dep < rank node → a dep = b dep) → rhs a node = rhs b node

variable {α : Type} {Value : α → Type}

def iterate (s : System α Value) : Nat → ∀ node, Value node
  | 0 => s.initial
  | k + 1 => s.rhs (iterate s k)

/-! Each node is stable after more steps than its rank. -/
theorem stable (s : System α Value) (k l : Nat) (node : α)
    (hk : s.rank node < k) (hl : s.rank node < l) :
    iterate s k node = iterate s l node := by
  induction k generalizing l node with
  | zero => omega
  | succ k ih =>
    cases l with
    | zero => omega
    | succ l =>
      apply s.respects
      intro dep hd
      apply ih l dep <;> omega

def solution (s : System α Value) (node : α) : Value node :=
  iterate s (s.rank node + 1) node

/-! Lower ranked nodes are already stable when the node's equation runs. -/
theorem solution_eq (s : System α Value) (node : α) :
    solution s node = s.rhs (solution s) node := by
  change s.rhs (iterate s (s.rank node)) node = s.rhs (solution s) node
  apply s.respects
  intro dep hd
  exact stable s (s.rank node) (s.rank dep + 1) dep hd (by omega)

/-! Any solution agrees with each stable iteration. -/
theorem eq_iterate (s : System α Value) (v : ∀ node, Value node)
    (hv : ∀ node, v node = s.rhs v node) (k : Nat) (node : α)
    (hk : s.rank node < k) : v node = iterate s k node := by
  induction k generalizing node with
  | zero => omega
  | succ k ih =>
    rw [hv node]
    apply s.respects
    intro dep hd
    exact ih dep (by omega)

theorem unique (s : System α Value) (v : ∀ node, Value node)
    (hv : ∀ node, v node = s.rhs v node) : v = solution s := by
  funext node
  exact eq_iterate s v hv (s.rank node + 1) node (by omega)

theorem existsUnique (s : System α Value) :
    ∃ v, (∀ node, v node = s.rhs v node) ∧
      ∀ w, (∀ node, w node = s.rhs w node) → w = v := by
  exact ⟨solution s, solution_eq s, fun v hv => unique s v hv⟩

/-!
Two systems have the same values on a closed set of dependencies when their equations
agree there. The first system's ranks suffice to order the dependency proof.
-/
theorem solution_agree_on (s t : System α Value)
    (selected : α → Prop) (depends : α → α → Prop)
    (ranked : ∀ node dep, depends node dep → s.rank dep < s.rank node)
    (closed : ∀ node dep, selected node → depends node dep → selected dep)
    (rhs_agree : ∀ node, selected node → ∀ a b,
      (∀ dep, depends node dep → a dep = b dep) → s.rhs a node = t.rhs b node)
    (node : α) (hn : selected node) : solution s node = solution t node := by
  have agree : ∀ k node, s.rank node < k → selected node →
      solution s node = solution t node := by
    intro k
    induction k with
    | zero => intro node hk; omega
    | succ k ih =>
      intro node hk hn
      rw [solution_eq s node, solution_eq t node]
      apply rhs_agree node hn
      intro dep hd
      exact ih dep (by have := ranked node dep hd; omega) (closed node dep hn hd)
  exact agree (s.rank node + 1) node (by omega) hn

end Silicon.Core.Semantics.EquationSolution
