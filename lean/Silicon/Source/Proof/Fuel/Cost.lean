-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli
import Silicon.Source.Proof.Fuel.Elab
import Silicon.Source.Proof.Fuel.Flatten

/-!
The theorem `eval_cost` of section 10.3 of the front-end spec. `Cli.elabRun` elaborates the
top selection and lowers the design. The result has the fuel `used` of both steps.

`eval_cost` is the budget boundary of `elabRun`: each fuel from `used` gives the same result,
and each fuel below `used` gives `S015`. Thus `used` is the least fuel that works, and spare
fuel does not change the result. The proof joins `Elab.Fuel.elaborate_budget` and
`Flatten.Fuel.flatten_budget`. The lowering gets the fuel that elaboration leaves.

`eval_cost_total` shows that the output of the command `cost` starts with `total {used}`.
-/
namespace Silicon.Source.Cli.Fuel

/-- The budget boundary of `elabRun` for one fuel `F`. -/
theorem elabRun_budget {o : Opts} {src t : String} {dg : String → String} {d : Elab.Design}
    {l : Flatten.Lowered} {used : Nat} (h : elabRun o src t dg = .ok (d, l, used)) (F : Nat) :
    (used ≤ F → elabRun { o with budget.fuel := F } src t dg = .ok (d, l, used)) ∧
    (F < used → ∃ p m,
      elabRun { o with budget.fuel := F } src t dg = .error (.error ⟨.S015, p, m⟩)) := by
  unfold elabRun observeRun at h ⊢
  simp only [← Elab.elaborate.eq_1] at h ⊢
  split at h
  · cases h
  rename_i items checked hl
  split at h
  · cases h
  rename_i p i ps xs ht
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i d' ue he
  split at h
  rotate_left
  · cases h
  · cases h
  rename_i l' ul hf
  cases h
  simp only [hlen, Bool.false_eq_true, ↓reduceIte]
  have eb := Elab.Fuel.elaborate_budget he F
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · rw [eb.1 (by omega)]
    dsimp only
    rw [(Flatten.Fuel.flatten_budget hf (F - ue)).1 (by omega)]
  · by_cases h1 : F < ue
    · obtain ⟨p', m, he'⟩ := eb.2 h1
      exact ⟨p', m, by rw [he']⟩
    · rw [eb.1 (by omega)]
      dsimp only
      obtain ⟨p', m, hf'⟩ := (Flatten.Fuel.flatten_budget hf (F - ue)).2 (by omega)
      exact ⟨p', m, by rw [hf']⟩

/--
The budget boundary of `elabRun` (spec 10.3, `eval_cost`). Let `elabRun` succeed and use
`used` units. Then each fuel from `used` gives the same result, and each fuel below gives
`S015`.
-/
theorem eval_cost (o : Opts) (src t : String) (dg : String → String) {d l used}
    (h : elabRun o src t dg = .ok (d, l, used)) :
    (∀ F, used ≤ F → elabRun { o with budget.fuel := F } src t dg = .ok (d, l, used)) ∧
    (∀ F, F < used → ∃ p m,
      elabRun { o with budget.fuel := F } src t dg = .error (.error ⟨.S015, p, m⟩)) :=
  ⟨fun F => (elabRun_budget h F).1, fun F => (elabRun_budget h F).2⟩

theorem foldl_prefix (g : β → String) :
    ∀ (xs : List β) (init : String), ∃ rest, xs.foldl (fun s x => s ++ g x) init = init ++ rest
  | [], init => ⟨"", by simp⟩
  | x :: xs, init => by
    obtain ⟨rest, h⟩ := foldl_prefix g xs (init ++ g x)
    exact ⟨g x ++ rest, by rw [List.foldl_cons, h, String.append_assoc]⟩

/-- The output of `cost` starts with the line `total {used}` of the fuel that `elabRun` used. -/
theorem eval_cost_total (o : Opts) (src t : String) (dg : String → String) {d l used}
    (h : elabRun o src t dg = .ok (d, l, used)) :
    ∃ rest, costText o src t dg = .ok (s!"total {used}\n" ++ rest) := by
  unfold costText Elab.costLines
  rw [h]
  dsimp only
  rw [← Array.foldl_toList]
  obtain ⟨rest, e⟩ := foldl_prefix (fun (x : String × Nat) => s!"{x.1} {x.2}\n") _ _
  exact ⟨rest, by rw [e]⟩

end Silicon.Source.Cli.Fuel
