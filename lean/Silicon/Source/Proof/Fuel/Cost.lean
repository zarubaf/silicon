-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli
import Silicon.Source.Proof.Fuel.Elab
import Silicon.Source.Proof.Fuel.Flatten

/-!
The theorems `observe_cost` and `eval_cost` of section 10.3 of the front-end spec.
`Cli.observeRun` elaborates the top selection and lowers the design. It gives the records of
the elaboration and a result with the fuel `used` of both steps.

`observe_cost` is the budget boundary of `observeRun`: each fuel from `used` gives the same
records and result, and each fuel below `used` gives `S015`. Thus `used` is the least fuel that
works, and spare fuel does not change the records or the result. The proof joins
`Elab.Fuel.observe_budget` and `Flatten.Fuel.flatten_budget`. The lowering gets the fuel that
elaboration leaves, and it makes no records. `observeText_cost` gives the same output of the
command `observe`. `eval_cost` is the projection of `observe_cost` to the result of `elabRun`.

`eval_cost_total` shows that the output of the command `cost` starts with `total {used}`.
-/
namespace Silicon.Source.Cli.Fuel

/-- The budget boundary of `observeRun` for one fuel `F`, with the records. -/
theorem observeRun_budget {o : Opts} {src t : String} {dg : String → String}
    {rs : Array Eval.Record} {d : Elab.Design} {l : Flatten.Lowered} {used : Nat}
    (h : observeRun o src t dg = (rs, .ok (d, l, used))) (F : Nat) :
    (used ≤ F → observeRun { o with budget.fuel := F } src t dg = (rs, .ok (d, l, used))) ∧
    (F < used → ∃ p m,
      (observeRun { o with budget.fuel := F } src t dg).2 = .error (.error ⟨.S015, p, m⟩)) := by
  unfold observeRun at h ⊢
  split at h
  · cases h
  rename_i items checked hl
  split at h
  · cases h
  rename_i p i ps xs ht
  split at h
  · cases h
  rename_i hlen
  simp only [hl, ht, hlen, Bool.false_eq_true, ↓reduceIte]
  generalize hr : Elab.observe o.budget checked dg p i xs = r at h
  obtain ⟨rs', res⟩ := r
  simp only [Prod.mk.injEq] at h
  obtain ⟨hrs, h⟩ := h
  subst hrs
  split at h
  · cases h
  rename_i _ _ ue
  split at h
  rotate_left
  · cases h
  · cases h
  rename_i l' ul hf
  cases h
  have eb := Elab.Fuel.observe_budget hr F
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
The budget boundary of `observeRun` (spec 10.3, `observe_cost`). Let `observeRun` give the
records `rs` and a result that uses `used` units. Then each fuel from `used` gives the same
records and result, and each fuel below gives `S015`. The lowering makes no records, so the
records come from the elaboration only.
-/
theorem observe_cost (o : Opts) (src t : String) (dg : String → String) {rs d l used}
    (h : observeRun o src t dg = (rs, .ok (d, l, used))) :
    (∀ F, used ≤ F → observeRun { o with budget.fuel := F } src t dg = (rs, .ok (d, l, used))) ∧
    (∀ F, F < used → ∃ p m,
      (observeRun { o with budget.fuel := F } src t dg).2 = .error (.error ⟨.S015, p, m⟩)) :=
  ⟨fun F => (observeRun_budget h F).1, fun F => (observeRun_budget h F).2⟩

/-- The output of the command `observe` is the same for each fuel from `used`. -/
theorem observeText_cost (o : Opts) (src t : String) (dg : String → String) {rs d l used}
    (h : observeRun o src t dg = (rs, .ok (d, l, used))) (F : Nat) (hu : used ≤ F) :
    observeText { o with budget.fuel := F } src t dg = observeText o src t dg := by
  unfold observeText
  rw [(observeRun_budget h F).1 hu, h]

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
  have r := observe_cost o src t dg (Prod.ext rfl h : observeRun o src t dg = (_, .ok _))
  ⟨fun F hu => congrArg Prod.snd (r.1 F hu), r.2⟩

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
