-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.GraphReach

/-! Component labels identify cycle nodes without a search from each node. -/
namespace Silicon.Core.GraphSCC

open GraphReach

variable {α : Type} [BEq α]

def ReadyOrder (g : List (α × List α)) (nodes order : List α) : Prop :=
  ∀ done : α → Prop,
    (∀ x y, done x → Reachable g y x → done y) →
    ∀ pre root post, order = pre ++ root :: post →
    (∀ x ∈ pre, done x) → ¬done root →
    ∀ y ∈ nodes, ¬done y → Reachable g y root → Reachable g root y

/-! Edges decrease labels. Equal labels give paths in both directions. -/
structure Certificate (g : List (α × List α)) where
  label : α → Nat
  nodes : List α
  edge_nodes : ∀ x y, y ∈ (g.lookup x).getD [] → x ∈ nodes ∧ y ∈ nodes
  edge_order : ∀ x y, y ∈ (g.lookup x).getD [] → label y ≤ label x
  connected : ∀ x ∈ nodes, ∀ y ∈ nodes, label x = label y → Reachable g x y

theorem Certificate.walk_order (c : Certificate g) {length : Nat} {x y : α}
    (h : Walk g length x y) : c.label y ≤ c.label x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step he _ ih => exact Nat.le_trans ih (c.edge_order _ _ he)

theorem Certificate.reachable_order (c : Certificate g) {x y : α}
    (h : Reachable g x y) : c.label y ≤ c.label x := by
  obtain ⟨length, h⟩ := h
  exact c.walk_order h

theorem Certificate.same_iff (c : Certificate g) (x y : α)
    (hx : x ∈ c.nodes) (hy : y ∈ c.nodes) :
    c.label x = c.label y ↔ Reachable g x y ∧ Reachable g y x := by
  constructor
  · intro h
    exact ⟨c.connected x hx y hy h, c.connected y hy x hx h.symm⟩
  · rintro ⟨hxy, hyx⟩
    exact Nat.le_antisymm (c.reachable_order hyx) (c.reachable_order hxy)

def cyclic (label : α → Nat) (source : α) (children : List α) : Bool :=
  children.any fun child => label child == label source

theorem Certificate.cyclic_iff (c : Certificate g) (x : α) :
    cyclic c.label x ((g.lookup x).getD []) = true ↔
      ∃ y ∈ (g.lookup x).getD [], Reachable g y x := by
  simp only [cyclic, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨y, he, hl⟩
    have hn := c.edge_nodes x y he
    exact ⟨y, he, c.connected y hn.2 x hn.1 hl⟩
  · rintro ⟨y, he, hr⟩
    exact ⟨y, he, Nat.le_antisymm (c.edge_order x y he) (c.reachable_order hr)⟩

theorem Certificate.cyclic_eq_reaches [LawfulBEq α] (c : Certificate g) (x : α) :
    cyclic c.label x ((g.lookup x).getD []) =
      reachesSpec g x (g.length + 1) ((g.lookup x).getD []) [] := by
  apply Bool.eq_iff_iff.mpr
  rw [c.cyclic_iff, reaches_graph_iff]

end Silicon.Core.GraphSCC

