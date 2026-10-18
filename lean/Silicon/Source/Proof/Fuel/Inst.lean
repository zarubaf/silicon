-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.Fuel

/-!
The fuel of the module statements and the instantiations: a part of the theorem `eval_cost` of
section 10.3 of the front-end spec. `hwStmt` and `instantiate` are in the mutual
block of `Eval`, so this module closes `follows_all` over the whole block.

The parts of `Source.Eval.Inst` follow themselves. The target of a `:=` evaluates its indices and
its root by a closure, as `arguments` does. `hwStmt_f` and `instantiate_f` get the facts of the
entry functions at the bounds `k` and `m`, as the helpers of `Proof.Fuel` do. The only read of
the absolute fuel besides `charge` is `measure` in `instantiate`, and `Follows.measure` keeps it.
`evalExpr_budget` is the budget boundary of a static expression.
-/
namespace Silicon.Source.Eval.Fuel

open Resolve

section helpers
variable {cap : Nat}

theorem bindings_f : Follows cap Elab.bindings Elab.bindings := by
  unfold Elab.bindings; follows [Follows.forInArray]

theorem modifyBody_f (f : Elab.Body → Elab.Body) :
    Follows cap (Elab.modifyBody f) (Elab.modifyBody f) := by
  unfold Elab.modifyBody; follows

theorem dataType_f (p : Pos) (t : Ty) : Follows cap (Elab.dataType p t) (Elab.dataType p t) := by
  unfold Elab.dataType; follows [notHandle_f]

theorem resource_f (k : Kind) (path : Names.Path) (t : Ty) (p : Pos) (x : String) :
    Follows cap (Elab.resource k path t p x) (Elab.resource k path t p x) := by
  unfold Elab.resource; follows

theorem port_f (p : Pos) (input : Bool) (b : Binder) (t : Ty) :
    Follows cap (Elab.port p input b t) (Elab.port p input b t) := by
  unfold Elab.port
  refine Follows.bind Follows.readThe fun c => Follows.bind (Follows.of_frame ?_) fun _ => ?_
  · intro c s a s' h
    simp only [bind_apply, get_apply, set_apply, pure_apply] at h ⊢
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  · follows [resource_f, modifyBody_f, normalize_f]

theorem bindTarget_f (p : Pos) (t : Elab.Target) (h : Agg) :
    Follows cap (Elab.bindTarget p t h) (Elab.bindTarget p t h) := by
  unfold Elab.bindTarget; follows [modifyBody_f]

theorem serialize_f (p : Pos) (m : String) (vs : List Value) :
    Follows cap (Elab.serialize p m vs) (Elab.serialize p m vs) := by
  unfold Elab.serialize; follows

theorem targetStep_f (s : Pos) (v : Val) (step : Sel × Option Value) :
    Follows cap (Elab.targetStep s v step) (Elab.targetStep s v step) := by
  unfold Elab.targetStep; follows [pickKey_f, selectKey_f, fieldKey_f]

theorem sinkValue_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (sinkValue p t v) (sinkValue p t v) := by
  unfold sinkValue; follows [lit_f]

theorem targetKeys_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (sels : List Sel) :
    Follows cap (targetKeys ev sels) (targetKeys ev' sels) := by
  unfold targetKeys; follows [he, need_f, static_f]

theorem targetRoot_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (root : Resolve.Expr) :
    Follows cap (targetRoot ev root) (targetRoot ev' root) := by
  unfold targetRoot; follows [he, need_f]

theorem targetPart_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (e : Resolve.Expr) :
    Follows cap (targetPart ev e) (targetPart ev' e) := by
  unfold targetPart; follows [targetRoot_f he, targetKeys_f he, targetStep_f]

theorem target_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (e : Resolve.Expr) :
    Follows cap (target ev e) (target ev' e) := by
  unfold target; follows [targetPart_f he]

end helpers

/-! `hwStmt` and `instantiate` get the bound of their caller after the charge. -/

section walk
variable {k m : Nat}

theorem instantiate_f (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (pos : Pos)
    (i : Nat) (tvs : List (Ty × Value)) :
    Follows m (instantiate k pos i tvs) (instantiate m pos i tvs) := by
  rw [instantiate.eq_def k, instantiate.eq_def m]
  follows [hb, serialize_f, bindings_f, nested_f, inFrame_f, Follows.measure, bindLocal_f]

theorem hwStmt_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t))
    (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (s : Resolve.Stmt) :
    Follows m (hwStmt k s) (hwStmt m s) := by
  rw [hwStmt.eq_def k, hwStmt.eq_def m]
  follows [he, ht, instantiate_f hb, arguments_f he ht, need_f, copy_f, conform_f, static_f,
    lit_f, fresh_f, bindLocal_f, dataType_f, memWord_f, memDepth_f, port_f, resource_f,
    modifyBody_f, target_f he, bindTarget_f, sinkValue_f, typedUse_f, settle_f, structural_f]

end walk

set_option maxHeartbeats 400000 in
/--
Each function of the evaluator at any bound `n` is followed by the same function at the
bound `n'`, with each fuel up to `n'`. The proof splits each branch of the evaluator, so it
needs more than the default heartbeats.
-/
theorem follows_all : ∀ n,
    (∀ n' e, Follows n' (eval n e) (eval n' e)) ∧
    (∀ n' t, Follows n' (typeExpr n t) (typeExpr n' t)) ∧
    (∀ n' s, Follows n' (stmt n s) (stmt n' s)) ∧
    (∀ n' p ss, Follows n' (block n p ss) (block n' p ss))
  | 0 => by
    refine ⟨fun _ e => ?_, fun _ t => ?_, fun _ s => ?_, fun _ p ss => ?_⟩
    · rw [eval.eq_def]; exact Follows.exhausted_left _ _
    · rw [typeExpr.eq_def]; exact Follows.exhausted_left _ _
    · rw [stmt.eq_def]; exact Follows.exhausted_left _ _
    · rw [block.eq_def]; exact Follows.exhausted_left _ _
  | k + 1 => by
    obtain ⟨he, ht, hs, hb⟩ := follows_all k
    refine ⟨fun n' e => ?_, fun n' t => ?_, fun n' s => ?_, fun n' p ss => ?_⟩
    · rcases n' with _ | m
      · rw [eval.eq_def (k + 1), eval.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, index_f (he k) (ht k), name_f (he k) (ht k),
          call_f (he k) (ht k) (hb k), spec_f (he k) (ht k), need_f, data_f, baseData_f, apply_f,
          hwUnary_f, test_f, hwBinary_f, unify_f, mux_f, static_f, pick_f, element_f, tupleOf_f,
          arrayOf_f, select_f, containerOp_f, arrayTy_f, field_f, strAt_f, hold_f, release_f,
          changesOf_f, normalize_f, readRef_f, aggEq_f, enumUse_f (he k) (ht k), variantOf_f,
          operands_f (he k), comparable_f, params_f (ht k), fnTy_f, structural_f, scrutTy_f,
          matchArms_f, binderTys_f, bindArm_f, scrutParts_f, shared_f, matchHw_f]
      · rw [eval.eq_def (k + 1), eval.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m) (ht m), name_f (he m) (ht m),
          call_f (he m) (ht m) (hb m), spec_f (he m) (ht m), need_f, data_f, baseData_f, apply_f,
          hwUnary_f, test_f, hwBinary_f, unify_f, mux_f, static_f, pick_f, element_f, tupleOf_f,
          arrayOf_f, select_f, containerOp_f, arrayTy_f, field_f, strAt_f, hold_f, release_f,
          changesOf_f, normalize_f, readRef_f, aggEq_f, enumUse_f (he m) (ht m), variantOf_f,
          operands_f (he m), comparable_f, params_f (ht m), fnTy_f, structural_f, scrutTy_f,
          matchArms_f, binderTys_f, bindArm_f, scrutParts_f, shared_f, matchHw_f]
    · rcases n' with _ | m
      · rw [typeExpr.eq_def (k + 1), typeExpr.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, index_f (he k) (ht k), name_f (he k) (ht k), spec_f (he k) (ht k),
          typeOf_f, tupleTy_f, arrayTy_f, static_f, need_f, params_f (ht k), fnTy_f,
          structural_f]
      · rw [typeExpr.eq_def (k + 1), typeExpr.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m) (ht m), name_f (he m) (ht m), spec_f (he m) (ht m),
          typeOf_f, tupleTy_f, arrayTy_f, static_f, need_f, params_f (ht m), fnTy_f,
          structural_f]
    · rcases n' with _ | m
      · rw [stmt.eq_def (k + 1), stmt.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, hs k, hb k, placeAt_f (he k), need_f, copy_f, typedUse_f,
          heldUse_f, known_f, named_f, bindLocal_f, test_f, int_f, range_f, iteration_f,
          static_f, store_f, hold_f, release_f, shut_f, hwStmt_f (he k) (ht k) (hb k)]
      · rw [stmt.eq_def (k + 1), stmt.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, hs m, hb m, placeAt_f (he m), need_f, copy_f, typedUse_f,
          heldUse_f, known_f, named_f, bindLocal_f, test_f, int_f, range_f, iteration_f,
          static_f, store_f, hold_f, release_f, shut_f, hwStmt_f (he m) (ht m) (hb m)]
    · rcases n' with _ | m
      · rw [block.eq_def (k + 1), block.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [hs k]
      · rw [block.eq_def (k + 1), block.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [hs m]

/-- The budget boundary of a static expression in the file scope. -/
theorem evalExpr_budget {budget : Budget} {items : Array Resolve.Item} {e : Resolve.Expr}
    {v : Value} {u : Nat} (h : evalExpr budget items e = .ok (v, u)) (F : Nat) :
    (u ≤ F → evalExpr { budget with fuel := F } items e = .ok (v, u)) ∧
    (F < u → ∃ p m, evalExpr { budget with fuel := F } items e = .error ⟨.S015, p, m⟩) :=
  run_budget (fun n n' => by follows [(follows_all n).1 n', static_f, need_f]) h F

end Silicon.Source.Eval.Fuel
