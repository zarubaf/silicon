import Std

/-! Bounded graph searches follow the first entry for each source node. -/
namespace Silicon.Core.GraphReach

theorem lookup_row_nodup [BEq α] [LawfulBEq α] (rows : List (α × β)) (n : α) (v : β)
    (hu : (rows.map Prod.fst).Nodup) (hm : (n, v) ∈ rows) : rows.lookup n = some v := by
  induction rows with
  | nil => simp at hm
  | cons row rows ih =>
    rcases row with ⟨a, b⟩
    have hd := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hm with hh | ht
    · cases hh; simp
    · have hne : n ≠ a := by
        intro he
        apply hd.1
        subst n
        exact List.mem_map.mpr ⟨(a, v), ht, rfl⟩
      have hb : (n == a) = false := by simp [hne]
      simpa [List.lookup, hb] using ih hd.2 ht



def freshNodes {α : Type} [BEq α] (seen pending acc : List α) : List α :=
  pending.foldl (fun acc n =>
    if seen.contains n || acc.contains n then acc else n :: acc) acc

/-! A visited search decides whether a target occurs within the edge bound. -/
def reachesSpec [BEq α] (g : List (α × List α)) (target : α) :
    Nat → List α → List α → Bool
  | 0, _, _ => false
  | fuel + 1, pending, seen =>
    if pending.contains target then true else
    let fresh := freshNodes seen pending []
    let seen := fresh ++ seen
    let next := fresh.flatMap fun n => (g.lookup n).getD []
    reachesSpec g target fuel (next.filter fun n => !seen.contains n) seen

section GraphSearch

variable {α : Type} [BEq α] [LawfulBEq α]

theorem mem_fresh (seen pending acc : List α) (x : α) :
    x ∈ freshNodes seen pending acc ↔ x ∈ acc ∨ x ∈ pending ∧ x ∉ seen := by
  induction pending generalizing acc with
  | nil => simp [freshNodes]
  | cons n pending ih =>
    simp only [freshNodes, List.foldl_cons]
    change x ∈ freshNodes seen pending _ ↔ _
    rw [ih]
    by_cases hs : n ∈ seen <;> by_cases ha : n ∈ acc <;>
      simp [hs, ha] <;> grind

inductive Walk (g : List (α × List α)) : Nat → α → α → Prop
  | refl (x : α) : Walk g 0 x x
  | step {x y z : α} {k : Nat} : y ∈ (g.lookup x).getD [] →
      Walk g k y z → Walk g (k + 1) x z

def updated (seen pending : List α) : List α := freshNodes seen pending [] ++ seen

def frontier (g : List (α × List α)) (seen pending : List α) : List α :=
  ((freshNodes seen pending []).flatMap fun n => (g.lookup n).getD []).filter
    fun n => !(updated seen pending).contains n

theorem mem_updated (seen pending : List α) (x : α) :
    x ∈ updated seen pending ↔ x ∈ seen ∨ x ∈ pending := by
  simp only [updated, List.mem_append, mem_fresh, List.not_mem_nil, false_or]
  grind

def Closed (g : List (α × List α)) (seen pending : List α) : Prop :=
  ∀ x ∈ seen, ∀ y ∈ (g.lookup x).getD [], y ∈ seen ∨ y ∈ pending

theorem closed_updated (g : List (α × List α)) (seen pending : List α)
    (hc : Closed g seen pending) :
    Closed g (updated seen pending) (frontier g seen pending) := by
  intro x hx y hy
  by_cases hm : y ∈ updated seen pending
  · exact Or.inl hm
  · apply Or.inr
    unfold frontier
    rw [List.mem_filter]
    refine ⟨?_, by simpa using hm⟩
    apply List.mem_flatMap.mpr
    refine ⟨x, ?_, hy⟩
    have hn : x ∉ seen := by
      intro hs
      exact hm ((mem_updated seen pending y).mpr (hc x hs y hy))
    exact (mem_fresh seen pending [] x).mpr
      (Or.inr ⟨((mem_updated seen pending x).mp hx).resolve_left hn, hn⟩)

theorem reaches_of_walk (g : List (α × List α)) (target : α)
    (fuel length : Nat) (pending seen : List α) (start : α)
    (hw : Walk g length start target) (hb : length < fuel)
    (hs : start ∈ seen ∨ start ∈ pending) (ht : target ∉ seen)
    (hc : Closed g seen pending) : reachesSpec g target fuel pending seen = true := by
  induction fuel generalizing length pending seen start with
  | zero => omega
  | succ fuel ih =>
    by_cases hp : target ∈ pending
    · simp only [reachesSpec, List.contains_iff_mem.mpr hp, ite_true]
    · have hcheck : pending.contains target = false := by simp [hp]
      simp only [reachesSpec, hcheck, Bool.false_eq_true, ite_false]
      change reachesSpec g target fuel (frontier g seen pending) (updated seen pending) = true
      cases hw with
      | refl => exact False.elim (hs.elim ht hp)
      | @step x y z k hedge htail =>
        have newclosed := closed_updated g seen pending hc
        apply ih k (frontier g seen pending) (updated seen pending) y htail (by omega)
        · exact newclosed start ((mem_updated seen pending start).mpr hs) y hedge
        · intro hm
          exact ((mem_updated seen pending target).mp hm).elim ht hp
        · exact newclosed

theorem reaches_initial (g : List (α × List α)) (target start : α)
    (fuel length : Nat) (pending : List α)
    (hw : Walk g length start target) (hb : length < fuel) (hs : start ∈ pending) :
    reachesSpec g target fuel pending [] = true := by
  apply reaches_of_walk g target fuel length pending [] start hw hb (Or.inr hs)
  · simp
  · intro x hx
    simp at hx


end GraphSearch

section Paths

variable {α : Type} [BEq α] [LawfulBEq α]

theorem reaches_sound (g : List (α × List α)) (target : α)
    (fuel : Nat) (pending seen : List α)
    (h : reachesSpec g target fuel pending seen = true) :
    ∃ start ∈ pending, ∃ length, length < fuel ∧ Walk g length start target := by
  induction fuel generalizing pending seen with
  | zero => simp [reachesSpec] at h
  | succ fuel ih =>
    simp only [reachesSpec] at h
    split at h
    · rename_i hm
      exact ⟨target, List.contains_iff_mem.mp hm, 0, by omega, .refl _⟩
    · obtain ⟨child, hc, length, hl, hw⟩ := ih _ _ h
      obtain ⟨hm, _⟩ := List.mem_filter.mp hc
      obtain ⟨start, hs, hedge⟩ := List.mem_flatMap.mp hm
      have hp := (mem_fresh seen pending [] start).mp hs
      simp only [List.not_mem_nil, false_or] at hp
      exact ⟨start, hp.1, length + 1, by omega, .step hedge hw⟩

theorem reaches_initial_iff (g : List (α × List α)) (target : α)
    (fuel : Nat) (pending : List α) :
    reachesSpec g target fuel pending [] = true ↔
      ∃ start ∈ pending, ∃ length, length < fuel ∧ Walk g length start target := by
  constructor
  · exact reaches_sound g target fuel pending []
  · rintro ⟨start, hs, length, hl, hw⟩
    exact reaches_initial g target start fuel length pending hw hl hs

inductive Trail (g : List (α × List α)) : List α → α → α → Prop
  | refl (x) : Trail g [] x x
  | step {x y z xs} : y ∈ (g.lookup x).getD [] → Trail g xs y z →
      Trail g (x :: xs) x z

omit [LawfulBEq α] in
theorem trail_walk (g : List (α × List α)) {xs : List α} {x y : α}
    (h : Trail g xs x y) : Walk g xs.length x y := by
  induction h with
  | refl x => exact .refl x
  | step he ht ih => exact .step he ih

omit [LawfulBEq α] in
theorem trail_suffix (g : List (α × List α)) {xs : List α} {x y n : α}
    (h : Trail g xs x y) (hn : xs.Nodup) (hm : n ∈ xs) :
    ∃ tail, tail.Nodup ∧ tail ⊆ xs ∧ Trail g tail n y := by
  induction h with
  | refl x => simp at hm
  | @step x child y xs he ht ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨n :: xs, hn, fun _ h => h, .step he ht⟩
    · obtain ⟨tail, hd, hs, hw⟩ := ih (List.nodup_cons.mp hn).2 hm
      exact ⟨tail, hd, fun _ h => List.mem_cons_of_mem _ (hs h), hw⟩

theorem walk_simple (g : List (α × List α)) {length : Nat} {x y : α}
    (h : Walk g length x y) : ∃ xs, xs.Nodup ∧ Trail g xs x y := by
  induction h with
  | refl x => exact ⟨[], List.nodup_nil, .refl _⟩
  | @step x child y length he ht ih =>
    obtain ⟨xs, hn, hw⟩ := ih
    by_cases hm : x ∈ xs
    · obtain ⟨tail, hd, _, hw⟩ := trail_suffix g hw hn hm
      exact ⟨tail, hd, hw⟩
    · exact ⟨x :: xs, List.nodup_cons.mpr ⟨hm, hn⟩, .step he hw⟩

theorem edge_source_key (g : List (α × List α)) {x y : α}
    (h : y ∈ (g.lookup x).getD []) : x ∈ g.map Prod.fst := by
  have hs : (g.lookup x).isSome = true := by
    cases he : g.lookup x <;> simp_all
  obtain ⟨row, hr, he⟩ := List.lookup_isSome_iff.mp hs
  exact List.mem_map.mpr ⟨row, hr, (eq_of_beq he).symm⟩

theorem trail_subset (g : List (α × List α)) {xs : List α} {x y : α}
    (h : Trail g xs x y) : xs ⊆ g.map Prod.fst := by
  induction h with
  | refl x => simp
  | step he ht ih =>
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact edge_source_key g he
    · exact ih hn

theorem walk_bounded (g : List (α × List α)) {length : Nat} {x y : α}
    (h : Walk g length x y) : ∃ short, short ≤ g.length ∧ Walk g short x y := by
  obtain ⟨xs, hn, ht⟩ := walk_simple g h
  refine ⟨xs.length, ?_, trail_walk g ht⟩
  have hb := hn.length_le_of_subset (trail_subset g ht)
  simpa using hb

def Reachable (g : List (α × List α)) (x y : α) : Prop := ∃ length, Walk g length x y

omit [LawfulBEq α] in
theorem walk_trans (g : List (α × List α)) {a b c : α} {left right : Nat}
    (hleft : Walk g left a b) (hright : Walk g right b c) :
    Walk g (left + right) a c := by
  induction hleft with
  | refl a => simpa using hright
  | step he ht ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Walk.step (g := g) he (ih hright))

omit [LawfulBEq α] in
theorem Reachable.refl (g : List (α × List α)) (x : α) : Reachable g x x :=
  ⟨0, .refl x⟩

omit [LawfulBEq α] in
theorem Reachable.trans (g : List (α × List α)) {a b c : α}
    (hleft : Reachable g a b) (hright : Reachable g b c) : Reachable g a c := by
  obtain ⟨left, hleft⟩ := hleft
  obtain ⟨right, hright⟩ := hright
  exact ⟨left + right, walk_trans g hleft hright⟩

omit [LawfulBEq α] in
theorem Reachable.edge (g : List (α × List α)) {x y : α}
    (h : y ∈ (g.lookup x).getD []) : Reachable g x y := ⟨1, .step h (.refl y)⟩

theorem reaches_graph_iff (g : List (α × List α)) (target : α) (pending : List α) :
    reachesSpec g target (g.length + 1) pending [] = true ↔
      ∃ start ∈ pending, Reachable g start target := by
  rw [reaches_initial_iff]
  constructor
  · rintro ⟨start, hs, length, _, hw⟩
    exact ⟨start, hs, length, hw⟩
  · rintro ⟨start, hs, length, hw⟩
    obtain ⟨short, hb, hw⟩ := walk_bounded g hw
    exact ⟨start, hs, short, by omega, hw⟩

def Reverses (g reverse : List (α × List α)) : Prop :=
  ∀ x y, y ∈ (g.lookup x).getD [] ↔ x ∈ (reverse.lookup y).getD []

omit [LawfulBEq α] in
theorem Reverses.symm {g reverse : List (α × List α)} (h : Reverses g reverse) :
    Reverses reverse g := fun x y => (h y x).symm

omit [LawfulBEq α] in
theorem walk_reverse {g reverse : List (α × List α)} (hr : Reverses g reverse)
    {length : Nat} {x y : α} (h : Walk g length x y) : Walk reverse length y x := by
  induction h with
  | refl x => exact .refl x
  | step he ht ih => exact walk_trans reverse ih (.step ((hr _ _).mp he) (.refl _))

omit [LawfulBEq α] in
theorem reachable_reverse_iff {g reverse : List (α × List α)} (hr : Reverses g reverse)
    (x y : α) : Reachable g x y ↔ Reachable reverse y x := by
  constructor
  · rintro ⟨length, hw⟩
    exact ⟨length, walk_reverse hr hw⟩
  · rintro ⟨length, hw⟩
    exact ⟨length, walk_reverse hr.symm hw⟩

end Paths

end Silicon.Core.GraphReach
