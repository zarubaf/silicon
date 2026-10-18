-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Elab
import Silicon.Source.Proof.Fuel

/-!
The fuel of the elaborator: a part of the theorem `eval_cost` of section 10.3 of the front-end
spec. The result of `Elab.elaborate` does not depend on spare fuel, and less fuel than an
elaboration uses gives `S015`.

The walk runs in `Eval.M`, and its tables are in the state of `Eval`. Thus `Eval.Fuel.Follows`
and the tactic `follows` cover it. The only read of the absolute fuel besides `charge` is
`Eval.measure`, and `Follows.measure` keeps it.

`follows_all` gives `Follows n' (f n a) (f n' a)` for `stmt` and `block` at any two bounds,
and `observe_budget` is the budget boundary of `Elab.observe` by `Eval.Fuel.observe_budget`.
`elaborate_budget` is its projection to the result.
-/
namespace Silicon.Source.Elab.Fuel

open Eval Eval.Fuel

section helpers
variable {cap : Nat}

theorem bindings_f : Follows cap bindings bindings := by
  unfold bindings; follows [Follows.forInArray]

theorem modifyBody_f (f : Body → Body) : Follows cap (modifyBody f) (modifyBody f) := by
  unfold modifyBody; follows

theorem dataType_f (p : Pos) (t : Ty) : Follows cap (dataType p t) (dataType p t) := by
  unfold dataType; follows [notHandle_f]

theorem resource_f (k : Kind) (path : Names.Path) (t : Ty) (p : Pos) (x : String) :
    Follows cap (resource k path t p x) (resource k path t p x) := by
  unfold resource; follows

theorem port_f (p : Pos) (input : Bool) (b : Resolve.Binder) (t : Ty) :
    Follows cap (port p input b t) (port p input b t) := by
  unfold port
  refine Follows.bind Follows.readThe fun c => Follows.bind (Follows.of_frame ?_) fun _ => ?_
  · intro c s a s' h
    simp only [bind_apply, get_apply, set_apply, pure_apply] at h ⊢
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  · follows [resource_f, modifyBody_f, normalize_f]

theorem bindTarget_f (p : Pos) (t : Target) (h : Agg) :
    Follows cap (bindTarget p t h) (bindTarget p t h) := by
  unfold bindTarget; follows [modifyBody_f]

theorem sinkValue_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (sinkValue p t v) (sinkValue p t v) := by
  unfold sinkValue; follows [lit_f]

theorem serialize_f (p : Pos) (m : String) (vs : List Value) :
    Follows cap (serialize p m vs) (serialize p m vs) := by
  unfold serialize; follows

end helpers

/-! `instantiate` gets the bound of its caller after the charge, as a helper of `Eval`. -/

section walk
variable {k m : Nat}

theorem targetKeys_f (he : ∀ e, Follows m (eval k e) (eval m e)) (sels : List Sel) :
    Follows m (targetKeys k sels) (targetKeys m sels) := by
  unfold targetKeys; follows [he, need_f, static_f]

theorem targetStep_f (s : Pos) (v : Val) (step : Sel × Option Value) :
    Follows m (targetStep s v step) (targetStep s v step) := by
  unfold targetStep; follows [pickKey_f, selectKey_f, fieldKey_f]

theorem targetRoot_f (he : ∀ e, Follows m (eval k e) (eval m e)) (root : Resolve.Expr) :
    Follows m (targetRoot k root) (targetRoot m root) := by
  unfold targetRoot; follows [he, need_f]

theorem targetPart_f (he : ∀ e, Follows m (eval k e) (eval m e)) (e : Resolve.Expr) :
    Follows m (targetPart k e) (targetPart m e) := by
  unfold targetPart; follows [targetRoot_f he, targetKeys_f he, targetStep_f]

theorem target_f (he : ∀ e, Follows m (eval k e) (eval m e)) (e : Resolve.Expr) :
    Follows m (target k e) (target m e) := by
  unfold target; follows [targetPart_f he]

theorem instantiate_f (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (pos : Pos)
    (i : Nat) (tvs : List (Ty × Value)) :
    Follows m (instantiate k pos i tvs) (instantiate m pos i tvs) := by
  rw [instantiate.eq_def k, instantiate.eq_def m]
  follows [hb, serialize_f, bindings_f, nested_f, inFrame_f, Follows.measure, bindLocal_f]

end walk

/--
The walk functions at the bound `n'` follow the walk functions at any bound `n`, with each
fuel up to `n'`.
-/
theorem follows_all : ∀ n,
    (∀ n' s, Follows n' (stmt n s) (stmt n' s)) ∧
    (∀ n' p ss, Follows n' (block n p ss) (block n' p ss))
  | 0 => by
    refine ⟨fun n' s => ?_, fun _ p ss => ?_⟩
    · rw [stmt.eq_def 0, stmt.eq_def n']
      split
      all_goals first
        | exact Follows.exhausted_left _ _
        | follows [(Eval.Fuel.follows_all 0).2.2.1 n']
    · rw [block.eq_def]; exact Follows.exhausted_left _ _
  | k + 1 => by
    obtain ⟨hs, hb⟩ := follows_all k
    have he := Eval.Fuel.follows_all k
    refine ⟨fun n' s => ?_, fun n' p ss => ?_⟩
    · rw [stmt.eq_def (k + 1), stmt.eq_def n']
      split
      all_goals first
        | follows [(Eval.Fuel.follows_all (k + 1)).2.2.1 n']; done
        | skip
      all_goals rcases n' with _ | m
      · refine Follows.exhaust (cap := k) _ _ fun _ => ?_
        follows [hs k, hb k, instantiate_f (hb k),
          arguments_f (he.1 k) (he.2.1 k), he.1 k, he.2.1 k, need_f, copy_f,
          conform_f, static_f, conformVal_f, lit_f, fresh_f, bindLocal_f, test_f, int_f, range_f,
          iteration_f, dataType_f, memWord_f, memDepth_f, port_f, resource_f, modifyBody_f,
          target_f (he.1 k), bindTarget_f, sinkValue_f, typedUse_f, settle_f, hold_f, release_f,
          structural_f]
      · refine Follows.charge_one _ fun _ => ?_
        follows [hs m, hb m, instantiate_f (hb m),
          arguments_f (he.1 m) (he.2.1 m), he.1 m, he.2.1 m, need_f, copy_f,
          conform_f, static_f, conformVal_f, lit_f, fresh_f, bindLocal_f, test_f, int_f, range_f,
          iteration_f, dataType_f, memWord_f, memDepth_f, port_f, resource_f, modifyBody_f,
          target_f (he.1 m), bindTarget_f, sinkValue_f, typedUse_f, settle_f, hold_f, release_f,
          structural_f]
    · rcases n' with _ | m
      · rw [block.eq_def (k + 1), block.eq_def 0]
        exact Follows.exhaust (cap := k) _ _ fun _ => by follows [hs k]
      · rw [block.eq_def (k + 1), block.eq_def (m + 1)]
        exact Follows.charge_one _ fun _ => by follows [hs m]

/--
The budget boundary of `observe`. If the elaboration uses `u` units, each fuel from `u` gives
the same records, design, and units, and each fuel below `u` gives `S015`.
-/
theorem observe_budget {budget : Budget} {items : Array Resolve.Item}
    {digest : String → String} {pos : Pos} {top : Nat} {xs : List Resolve.Expr}
    {rs : Array Record} {d : Design} {u : Nat}
    (h : observe budget items digest pos top xs = (rs, .ok (d, u))) (F : Nat) :
    (u ≤ F → observe { budget with fuel := F } items digest pos top xs = (rs, .ok (d, u))) ∧
    (F < u → ∃ p m,
      (observe { budget with fuel := F } items digest pos top xs).2 = .error ⟨.S015, p, m⟩) := by
  refine Eval.Fuel.observe_budget (fun n n' => ?_) h F
  follows [(Eval.Fuel.follows_all n).1 n', static_f, need_f,
    instantiate_f ((follows_all n).2 n'),
    arguments_f ((Eval.Fuel.follows_all n).1 n') ((Eval.Fuel.follows_all n).2.1 n')]

/--
The budget boundary of `elaborate`. If the elaboration uses `u` units, each fuel from `u` gives
the same design and units, and each fuel below `u` gives `S015`.
-/
theorem elaborate_budget {budget : Budget} {items : Array Resolve.Item}
    {digest : String → String} {pos : Pos} {top : Nat} {xs : List Resolve.Expr} {d : Design}
    {u : Nat} (h : elaborate budget items digest pos top xs = .ok (d, u)) (F : Nat) :
    (u ≤ F → elaborate { budget with fuel := F } items digest pos top xs = .ok (d, u)) ∧
    (F < u → ∃ p m,
      elaborate { budget with fuel := F } items digest pos top xs = .error ⟨.S015, p, m⟩) :=
  have r := observe_budget
    (Prod.ext rfl h : observe budget items digest pos top xs = (_, .ok (d, u))) F
  ⟨fun hu => congrArg Prod.snd (r.1 hu), r.2⟩

end Silicon.Source.Elab.Fuel
