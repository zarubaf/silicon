-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Lower

/-!
A rank that decreases along each alias bounds every alias chain by the number of aliases.
-/
namespace Silicon.Core.LowerProof

variable (aliases : Std.HashMap String String) (rank : String → Nat)

def chainBound (x : String) : Nat :=
  if x ∈ aliases then aliases.keys.countP (fun k => rank k ≤ rank x) else 0

private theorem countP_lt (xs : List String) (p q : String → Bool)
    (sub : ∀ x, p x = true → q x = true) (k : String) (hk : k ∈ xs)
    (hq : q k = true) (hp : p k = false) : xs.countP p < xs.countP q := by
  induction xs with
  | nil => cases hk
  | cons x xs ih =>
    simp only [List.countP_cons]
    have le := List.countP_mono_left (l := xs) (fun a _ h => sub a h)
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [hp, hq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have lt := ih hk
      have step : (if p x = true then 1 else 0) ≤ (if q x = true then 1 else 0) := by
        by_cases hx : p x = true
        · simp [hx, sub x hx]
        · simp [hx]
      omega

variable {aliases} {rank}

theorem chainBound_le (x : String) : chainBound aliases rank x ≤ aliases.size := by
  unfold chainBound
  split
  · exact Nat.le_trans List.countP_le_length (Nat.le_of_eq Std.HashMap.length_keys)
  · exact Nat.zero_le _

theorem chainBound_pos (x : String) (hx : x ∈ aliases) : 0 < chainBound aliases rank x := by
  unfold chainBound
  simp only [hx, ↓reduceIte]
  exact List.countP_pos_iff.mpr ⟨x, Std.HashMap.mem_keys.mpr hx, by simp⟩

theorem resolve_none (x : String) (absent : aliases[x]? = none) (fuel : Nat) :
    Lower.resolve aliases fuel x = x := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [Lower.resolve, absent]

variable (decreasing : ∀ k v, aliases[k]? = some v → v ∈ aliases → rank v < rank k)
include decreasing

theorem chainBound_step (k v : String) (found : aliases[k]? = some v) :
    chainBound aliases rank v < chainBound aliases rank k := by
  have hk : k ∈ aliases := Std.HashMap.isSome_getElem?_iff_mem.mp (by rw [found]; rfl)
  by_cases hv : v ∈ aliases
  · have lt := decreasing k v found hv
    unfold chainBound
    simp only [hv, hk, ↓reduceIte]
    apply countP_lt _ _ _ (fun x h => by simp at h ⊢; omega) k (Std.HashMap.mem_keys.mpr hk)
    · simp
    · simp
      omega
  · have pos := chainBound_pos (rank := rank) k hk
    unfold chainBound at pos ⊢
    simp only [hv, ↓reduceIte]
    exact pos

private theorem resolve_stable_aux (n : Nat) : ∀ x, chainBound aliases rank x ≤ n →
    ∀ f g, chainBound aliases rank x ≤ f → chainBound aliases rank x ≤ g →
      Lower.resolve aliases f x = Lower.resolve aliases g x := by
  induction n with
  | zero =>
    intro x hx f g _ _
    cases found : aliases[x]? with
    | none => rw [resolve_none x found, resolve_none x found]
    | some v =>
      have := chainBound_pos (rank := rank) x
        (Std.HashMap.isSome_getElem?_iff_mem.mp (by rw [found]; rfl))
      omega
  | succ n ih =>
    intro x hx f g hf hg
    cases found : aliases[x]? with
    | none => rw [resolve_none x found, resolve_none x found]
    | some v =>
      have step := chainBound_step decreasing x v found
      cases f with
      | zero => omega
      | succ f =>
        cases g with
        | zero => omega
        | succ g =>
          simp only [Lower.resolve, found]
          exact ih v (by omega) f g (by omega) (by omega)

theorem resolve_alias (k v : String) (found : aliases[k]? = some v) :
    Lower.resolve aliases aliases.size k = Lower.resolve aliases aliases.size v := by
  have step := chainBound_step decreasing k v found
  have bound := chainBound_le (aliases := aliases) (rank := rank) k
  cases size : aliases.size with
  | zero => omega
  | succ n =>
    simp only [Lower.resolve, found]
    exact resolve_stable_aux decreasing _ v (Nat.le_refl _) n (n + 1) (by omega) (by omega)

end Silicon.Core.LowerProof
