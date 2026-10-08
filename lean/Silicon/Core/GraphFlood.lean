import Silicon.Core.GraphDFSBase

/-! A visited search returns only the nodes that it adds to an existing closed set. -/
namespace Silicon.Core.GraphFlood

open GraphReach GraphDFS

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {g : List (α × List α)} {nodes active : List α} {root : α}
variable {blocked : Std.HashSet α} {state : State α}

structure Valid (g : List (α × List α)) (nodes : List α) (blocked : Std.HashSet α)
    (root : α) (active : List α) (state : State α) : Prop where
  seen_iff : ∀ x, state.seen.contains x = true ↔
    blocked.contains x = true ∨ x ∈ state.order ∨ x ∈ active
  active_nodup : active.Nodup
  active_fresh : ∀ x ∈ active, x ∉ state.order
  support : state.order ++ active ⊆ nodes
  reached : ∀ x ∈ state.order ++ active, Reachable g root x
  fresh : ∀ x ∈ state.order ++ active, blocked.contains x = false
  closed : ∀ x ∈ state.order, ∀ y ∈ (g.lookup x).getD [], state.seen.contains y = true

theorem Valid.push (h : Valid g nodes blocked root active state) (x : α)
    (hs : state.seen.contains x = false) (hx : x ∈ nodes) (hr : Reachable g root x) :
    Valid g nodes blocked root (x :: active) { state with seen := state.seen.insert x } := by
  have absent : ¬(blocked.contains x = true ∨ x ∈ state.order ∨ x ∈ active) := by
    intro hm
    have := (h.seen_iff x).mpr hm
    simp [hs] at this
  constructor
  · intro y
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
      h.seen_iff, List.mem_cons]
    grind
  · exact List.nodup_cons.mpr ⟨fun hm => absent (Or.inr (Or.inr hm)), h.active_nodup⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact fun hm => absent (Or.inr (Or.inl hm))
    · exact h.active_fresh y hy
  · intro y hy
    rcases List.mem_append.mp hy with ho | ha
    · exact h.support (List.mem_append_left _ ho)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact h.support (List.mem_append_right _ ha)
  · intro y hy
    rcases List.mem_append.mp hy with ho | ha
    · exact h.reached y (List.mem_append_left _ ho)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hr
      · exact h.reached y (List.mem_append_right _ ha)
  · intro y hy
    rcases List.mem_append.mp hy with ho | ha
    · exact h.fresh y (List.mem_append_left _ ho)
    · rcases List.mem_cons.mp ha with rfl | ha
      · cases hb : blocked.contains y
        · rfl
        · exact False.elim (absent (Or.inl hb))
      · exact h.fresh y (List.mem_append_right _ ha)
  · intro y hy z hz
    simp [h.closed y hy z hz]

omit [LawfulBEq α] [LawfulHashable α] in
theorem Valid.finish (h : Valid g nodes blocked root (x :: active) state)
    (all : ∀ y ∈ (g.lookup x).getD [], state.seen.contains y = true) :
    Valid g nodes blocked root active { state with order := x :: state.order } := by
  constructor
  · intro y
    simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using h.seen_iff y
  · exact (List.nodup_cons.mp h.active_nodup).2
  · intro y hy hm
    rcases List.mem_cons.mp hm with he | ho
    · subst y
      exact (List.nodup_cons.mp h.active_nodup).1 hy
    · exact h.active_fresh y (by simp [hy]) ho
  · intro y hy
    apply h.support
    simpa [List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm] using hy
  · intro y hy
    apply h.reached y
    simpa [List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm] using hy
  · intro y hy
    apply h.fresh y
    simpa [List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm] using hy
  · intro y hy z hz
    rcases List.mem_cons.mp hy with rfl | hy
    · exact all z hz
    · exact h.closed y hy z hz

theorem visit_total (edges : α → List α) (he : ∀ x, edges x = (g.lookup x).getD [])
    (support : ∀ x ∈ nodes, ∀ y ∈ (g.lookup x).getD [], y ∈ nodes)
    (fuel : Nat) (x : α) (active : List α) (state : State α)
    (valid : Valid g nodes blocked root active state) (hx : x ∈ nodes)
    (reach : Reachable g root x) (bound : nodes.length < active.length + fuel) :
    ∃ out, visit edges fuel x state = some out ∧ Valid g nodes blocked root active out ∧
      Extended state out ∧ out.seen.contains x = true := by
  induction fuel generalizing x active state with
  | zero =>
    have sub : active ⊆ nodes := fun x hx => valid.support (List.mem_append_right _ hx)
    have := valid.active_nodup.length_le_of_subset sub
    simp only [Nat.add_zero] at bound
    omega
  | succ fuel ih =>
    cases hs : state.seen.contains x
    · let start : State α := { state with seen := state.seen.insert x }
      have started := valid.push x hs hx reach
      obtain ⟨out, hout, hv, hext, hall⟩ := visits_total (visit edges fuel)
        (Valid g nodes blocked root (x :: active)) (edges x) (by
          intro child hc middle hm
          apply ih child (x :: active) middle hm
          · exact support x hx child (by rwa [he] at hc)
          · exact Reachable.trans g reach (Reachable.edge g (by rwa [he] at hc))
          · simp only [List.length_cons]
            omega) start started
      refine ⟨{ out with order := x :: out.order }, ?_, ?_, ?_, ?_⟩
      · simp [visit, hs, start, hout]
      · exact hv.finish (fun y hy => hall y (by rwa [he]))
      · intro y hy
        apply hext y
        simp [start, hy]
      · apply hext x
        simp [start]
    · exact ⟨state, by simp [visit, hs], valid, .refl state, hs⟩

def fill (edges : α → List α) (fuel : Nat) (root : α) (seen : Std.HashSet α) :
    List α × Std.HashSet α :=
  let out := (visit edges fuel root { seen := seen, order := [] }).getD
    { seen := {}, order := [] }
  (out.order, out.seen)

theorem fill_spec (edges : α → List α) (he : ∀ x, edges x = (g.lookup x).getD [])
    (support : ∀ x ∈ nodes, ∀ y ∈ (g.lookup x).getD [], y ∈ nodes)
    (blocked : Std.HashSet α)
    (closed : ∀ x y, blocked.contains x = true → y ∈ (g.lookup x).getD [] →
      blocked.contains y = true)
    (root : α) (hr : root ∈ nodes) :
    let out := fill edges (nodes.length + 1) root blocked
    (∀ n, n ∈ out.1 ↔ blocked.contains n = false ∧ Reachable g root n) ∧
    (∀ n, out.2.contains n = true ↔ blocked.contains n = true ∨ n ∈ out.1) := by
  have initial : Valid g nodes blocked root [] { seen := blocked, order := [] } := by
    constructor <;> simp
  obtain ⟨out, ho, hv, hext, hm⟩ := visit_total edges he support (nodes.length + 1)
    root [] { seen := blocked, order := [] } initial hr (Reachable.refl g root) (by simp)
  have hall : ∀ x y, out.seen.contains x = true → y ∈ (g.lookup x).getD [] →
      out.seen.contains y = true := by
    intro x y hx hy
    have hs := (hv.seen_iff x).mp hx
    simp only [List.not_mem_nil, or_false] at hs
    rcases hs with hb | ho
    · exact hext y (closed x y hb hy)
    · exact hv.closed x ho y hy
  have reachable (x : α) (h : Reachable g root x) : out.seen.contains x = true := by
    obtain ⟨length, hw⟩ := h
    have walk (length : Nat) (x y : α) (hw : Walk g length x y)
        (hx : out.seen.contains x = true) : out.seen.contains y = true := by
      induction hw with
      | refl => exact hx
      | step he _ ih => exact ih (hall _ _ hx he)
    exact walk length root x hw hm
  simp only [fill, ho, Option.getD_some]
  refine ⟨?_, ?_⟩
  · intro n
    constructor
    · intro hn
      exact ⟨hv.fresh n (by simpa using hn), hv.reached n (by simpa using hn)⟩
    · rintro ⟨fresh, reach⟩
      have hs := (hv.seen_iff n).mp (reachable n reach)
      simpa [fresh] using hs
  · intro n
    simpa using hv.seen_iff n

end Silicon.Core.GraphFlood
