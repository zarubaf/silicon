-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.GraphSCC

/-! Depth-first traversal state records visited nodes and reverse finish order. -/
namespace Silicon.Core.GraphDFS

variable {α : Type} [BEq α]
variable {g : List (α × List α)} {order active nodes : List α}

open GraphReach

def OrderInvariant (g : List (α × List α)) (order active : List α) : Prop :=
  ∀ pre root post, order = pre ++ root :: post →
    ∀ y ∈ post, Reachable g y root →
      Reachable g root y ∨
        ∃ a ∈ pre ++ active, Reachable g y a ∧ Reachable g a y

theorem OrderInvariant.push (h : OrderInvariant g order active) (x : α) :
    OrderInvariant g order (x :: active) := by
  intro pre root post he y hy hr
  rcases h pre root post he y hy hr with h | ⟨a, ha, hr⟩
  · exact Or.inl h
  · refine Or.inr ⟨a, ?_, hr⟩
    simp only [List.mem_append, List.mem_cons] at *
    grind

theorem OrderInvariant.finish {x : α} (h : OrderInvariant g order (x :: active))
    (hx : x ∉ order)
    (hc : ∀ y ∈ order, (∀ z, Reachable g y z → z ∈ order) ∨
      ∃ a ∈ x :: active, Reachable g y a ∧ Reachable g a y) :
    OrderInvariant g (x :: order) active := by
  intro pre root post he y hy hr
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases hc y hy with hclosed | ⟨a, ha, hya, hay⟩
    · exact False.elim (hx (hclosed x hr))
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl hay
      · exact Or.inr ⟨a, by simpa using ha, hya, hay⟩
  | cons a pre =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rcases h pre root post he y hy hr with hr | ⟨a, ha, hya, hay⟩
    · exact Or.inl hr
    · refine Or.inr ⟨a, ?_, hya, hay⟩
      simp only [List.mem_append, List.mem_cons] at *
      grind

theorem OrderInvariant.ready (h : OrderInvariant g order [])
    (hcover : nodes ⊆ order) : GraphSCC.ReadyOrder g nodes order := by
  intro done hclosed pre root post he hp _ y hy hnot hr
  have hmem := hcover hy
  rw [he, List.mem_append, List.mem_cons] at hmem
  rcases hmem with hpre | rfl | hpost
  · exact False.elim (hnot (hp y hpre))
  · exact Reachable.refl g y
  · rcases h pre root post he y hpost hr with hr | ⟨a, ha, hya, _⟩
    · exact hr
    · exact False.elim (hnot (hclosed a y (hp a (by simpa using ha)) hya))

variable [Hashable α]

structure State (α : Type) [BEq α] [Hashable α] where
  seen : Std.HashSet α
  order : List α

structure State.Valid (g : List (α × List α)) (nodes active : List α)
    (state : State α) : Prop where
  seen_iff : ∀ x, state.seen.contains x = true ↔ x ∈ state.order ∨ x ∈ active
  active_nodup : active.Nodup
  active_fresh : ∀ x ∈ active, x ∉ state.order
  support : state.order ++ active ⊆ nodes
  completed : ∀ x ∈ state.order,
    (∀ y, Reachable g x y → y ∈ state.order) ∨
      ∃ a ∈ active, Reachable g x a ∧ Reachable g a x
  ordered : OrderInvariant g state.order active
  closed : ∀ x ∈ state.order, ∀ y ∈ (g.lookup x).getD [], state.seen.contains y = true

def Extended (before after : State α) : Prop :=
  ∀ x, before.seen.contains x = true → after.seen.contains x = true

theorem Extended.refl (state : State α) : Extended state state := fun _ h => h

theorem Extended.trans {first middle last : State α}
    (h₁ : Extended first middle) (h₂ : Extended middle last) : Extended first last :=
  fun x h => h₂ x (h₁ x h)

def visits (visit : α → State α → Option (State α)) :
    List α → State α → Option (State α)
  | [], state => some state
  | x :: xs, state => do
    let state ← visit x state
    visits visit xs state

def visit (edges : α → List α) : Nat → α → State α → Option (State α)
  | fuel, x, state =>
    if state.seen.contains x then some state else
    match fuel with
    | 0 => none
    | fuel + 1 => do
      let start := { state with seen := state.seen.insert x }
      let out ← visits (visit edges fuel) (edges x) start
      some { out with order := x :: out.order }

theorem visits_total (visit : α → State α → Option (State α))
    (P : State α → Prop) (xs : List α)
    (hvisit : ∀ x ∈ xs, ∀ state, P state →
      ∃ out, visit x state = some out ∧ P out ∧
        Extended state out ∧ out.seen.contains x = true)
    (state : State α) (hs : P state) :
    ∃ out, visits visit xs state = some out ∧ P out ∧
      Extended state out ∧ ∀ x ∈ xs, out.seen.contains x = true := by
  induction xs generalizing state with
  | nil => exact ⟨state, rfl, hs, .refl state, by simp⟩
  | cons x xs ih =>
    obtain ⟨middle, hm, hp, he, hx⟩ := hvisit x (by simp) state hs
    obtain ⟨out, ho, hp, hf, hall⟩ := ih
      (fun x hx => hvisit x (by simp [hx])) middle hp
    refine ⟨out, by simp [visits, hm, ho], hp, he.trans hf, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf y hx
    · exact hall y hy

end Silicon.Core.GraphDFS
