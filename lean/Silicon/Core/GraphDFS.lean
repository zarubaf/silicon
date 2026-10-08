import Silicon.Core.GraphDFSState

/-! A depth-first traversal returns nodes in reverse finish order. -/
namespace Silicon.Core.GraphDFS

open GraphReach

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {g : List (α × List α)} {nodes : List α}

omit [LawfulBEq α] [LawfulHashable α] in
theorem valid_empty : State.Valid g nodes [] ({ seen := {}, order := [] } : State α) := by
  constructor
  · intro x
    simp
  · simp
  · simp
  · simp
  · simp
  · intro pre root post he
    have := congrArg List.length he
    simp at this
  · simp

theorem visit_total
    (edges : α → List α) (he : ∀ x, edges x = (g.lookup x).getD [])
    (support : ∀ x ∈ nodes, ∀ y ∈ (g.lookup x).getD [], y ∈ nodes)
    (fuel : Nat) (x : α) (active : List α) (state : State α)
    (hv : State.Valid g nodes active state) (hx : x ∈ nodes)
    (ha : ∀ a ∈ active, Reachable g a x)
    (hb : nodes.length < active.length + fuel) :
    ∃ out, visit edges fuel x state = some out ∧ State.Valid g nodes active out ∧
      Extended state out ∧ out.seen.contains x = true := by
  induction fuel generalizing x active state with
  | zero =>
    have hsub : active ⊆ nodes := fun a h => hv.support (by simp [h])
    have := hv.active_nodup.length_le_of_subset hsub
    simp only [Nat.add_zero] at hb
    omega
  | succ fuel ih =>
    by_cases hs : state.seen.contains x = true
    · exact ⟨state, by simp [visit, hs], hv, .refl state, hs⟩
    · have hs : state.seen.contains x = false := by simpa using hs
      let start : State α := { state with seen := state.seen.insert x }
      have hstart : State.Valid g nodes (x :: active) start :=
        State.Valid.push state active x hv hs hx
      obtain ⟨out, hout, hvout, hext, hall⟩ := visits_total (visit edges fuel)
        (State.Valid g nodes (x :: active)) (edges x) (by
          intro child hc middle hmiddle
          apply ih child (x :: active) middle hmiddle
          · exact support x hx child (by rwa [he] at hc)
          · intro a ham
            rcases List.mem_cons.mp ham with rfl | ham
            · exact Reachable.edge g (by rwa [he] at hc)
            · exact Reachable.trans g (ha a ham) (Reachable.edge g (by rwa [he] at hc))
          · simp only [List.length_cons]
            omega) start hstart
      refine ⟨{ out with order := x :: out.order }, ?_, ?_, ?_, ?_⟩
      · simp [visit, hs, start, hout]
      · exact State.Valid.finish out active x hvout (fun y hy => hall y (by rwa [he])) ha
      · intro y hy
        apply hext y
        simp [start, hy]
      · apply hext x
        simp [start]

def order (edges : α → List α) (nodes : List α) : List α :=
  ((visits (visit edges (nodes.length + 1)) nodes { seen := {}, order := [] }).map
    State.order).getD []

theorem order_spec
    (edges : α → List α) (he : ∀ x, edges x = (g.lookup x).getD [])
    (support : ∀ x ∈ nodes, ∀ y ∈ (g.lookup x).getD [], y ∈ nodes) :
    GraphSCC.ReadyOrder g nodes (order edges nodes) ∧
      ∀ x, x ∈ order edges nodes ↔ x ∈ nodes := by
  obtain ⟨out, ho, hv, _, hall⟩ := visits_total (visit edges (nodes.length + 1))
    (State.Valid g nodes []) nodes (by
      intro x hx state hv
      exact visit_total edges he support _ x [] state hv hx
        (by simp) (by simp)) { seen := {}, order := [] } valid_empty
  have heq : order edges nodes = out.order := by simp [order, ho]
  rw [heq]
  have hcover : nodes ⊆ out.order := by
    intro x hx
    simpa using (hv.seen_iff x).mp (hall x hx)
  refine ⟨hv.ordered.ready hcover, ?_⟩
  intro x
  exact ⟨fun h => hv.support (by simpa using h), fun h => hcover h⟩

end Silicon.Core.GraphDFS
