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

theorem resource_f (k : Kind) (path : Names.Path) (t : Ty) (p : Pos) (x : String)
    (key : Option Nat) (binder : Option String) :
    Follows cap (Elab.resource k path t p x key binder) (Elab.resource k path t p x key binder) :=
  by unfold Elab.resource; follows

theorem publish_f (y : Nat) (f : Elab.Public) (p : Pos) :
    Follows cap (Elab.publish y f p) (Elab.publish y f p) := by
  unfold Elab.publish; follows

theorem reserve_f (y : Nat) : Follows cap (Elab.reserve y) (Elab.reserve y) := by
  refine Follows.of_frame ?_
  intro c s a s' h
  simp only [Elab.reserve, bind_apply, get_apply, set_apply, pure_apply] at h ⊢
  cases h
  exact ⟨rfl, fun _ => rfl⟩

theorem publicOf_f (y : Nat) : Follows cap (Elab.publicOf y) (Elab.publicOf y) := by
  unfold Elab.publicOf; follows

theorem port_f (p : Pos) (input : Bool) (x : String) (y : Nat) (t : Ty) (b : Option String) :
    Follows cap (Elab.port p input x y t b) (Elab.port p input x y t b) := by
  unfold Elab.port
  follows [publicOf_f, again_f, publish_f, reserve_f, resource_f, modifyBody_f, normalize_f]

theorem entry_f (p : Pos) (input : Bool) (x : String) (y k : Nat) (t : Ty) (b : Option String) :
    Follows cap (Elab.entry p input x y k t b) (Elab.entry p input x y k t b) := by
  unfold Elab.entry; follows [publicOf_f, publish_f, resource_f, modifyBody_f, normalize_f]

theorem symbolOf_f (x : String) : Follows cap (symbolOf x) (symbolOf x) := by
  unfold symbolOf; follows [symbolFind_f]

theorem keyed_f (p : Pos) (input : Bool) (b : Binder) (t : Ty) (kp : Pos) (v : Value) :
    Follows cap (Elab.keyed p input b t kp v) (Elab.keyed p input b t kp v) := by
  unfold Elab.keyed; follows [symbolOf_f, port_f, entry_f, bindLocal_f]

theorem hwCheck_f (p : Pos) (s : Resolve.Stmt) : Follows cap (hwCheck p s) (hwCheck p s) := by
  unfold hwCheck; follows

theorem familyKey_f (p : Pos) (v : Value) :
    Follows cap (Elab.familyKey p v) (Elab.familyKey p v) := by
  unfold Elab.familyKey; follows

theorem selectionKey_f (np p : Pos) (x : String) (v : Val) :
    Follows cap (selectionKey np p x v) (selectionKey np p x v) := by
  unfold selectionKey; follows [static_f, familyKey_f]

theorem entryVal_f (p : Pos) (x : String) (id k : Nat) :
    Follows cap (entryVal p x id k) (entryVal p x id k) := by
  unfold entryVal; follows

theorem entryAt_f (p kp : Pos) (x : String) (id k : Nat) :
    Follows cap (entryAt p kp x id k) (entryAt p kp x id k) := by
  unfold entryAt; follows [entryVal_f, readRef_f]

theorem bindTarget_f (p : Pos) (t : Elab.Target) (h : Agg) :
    Follows cap (Elab.bindTarget p t h) (Elab.bindTarget p t h) := by
  unfold Elab.bindTarget; follows [modifyBody_f, breach_f, second_f]

theorem serialize_f (p : Pos) (m : String) (vs : List Value) :
    Follows cap (Elab.serialize p m vs) (Elab.serialize p m vs) := by
  unfold Elab.serialize; follows

theorem targetPort_f (s : Pos) (id : Nat) (path : Names.Path) (q : Port) :
    Follows cap (targetPort s id path q) (targetPort s id path q) := by
  unfold targetPort; follows

theorem targetStep_f (s : Pos) (v : Val) (step : Sel × Option Value) :
    Follows cap (targetStep s v step) (targetStep s v step) := by
  unfold targetStep; follows [pickKey_f, selectKey_f, fieldKey_f, targetPort_f]

theorem childFamily_f (v : Val) (f : Ident) :
    Follows cap (Elab.childFamily v f) (Elab.childFamily v f) := by
  unfold Elab.childFamily; follows

theorem childTarget_f (s : Pos) (v : Val) (f : Ident) (kp : Pos) (k : Value) :
    Follows cap (childTarget s v f kp k) (childTarget s v f kp k) := by
  unfold childTarget; follows [familyKey_f, childPort_f, targetPort_f]

theorem walkStep_f (s : Pos) (v : Val) (fam : Option Ident) (step : Sel × Option Value) :
    Follows cap (walkStep s v fam step) (walkStep s v fam step) := by
  unfold walkStep; follows [targetStep_f, childFamily_f, childTarget_f]

theorem targetWalk_f (s : Pos) :
    ∀ (v : Val) (fam : Option Ident) (steps : List (Sel × Option Value)),
      Follows cap (targetWalk s v fam steps) (targetWalk s v fam steps)
  | v, none, [] => by rw [targetWalk]; follows
  | v, some f, [] => by rw [targetWalk]; follows
  | v, fam, step :: rest => by
    rw [targetWalk]
    exact Follows.bind (walkStep_f s v fam step) fun (w, g) => targetWalk_f s w g rest

theorem sinkValue_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (sinkValue p t v) (sinkValue p t v) := by
  unfold sinkValue; follows [lit_f]

theorem targetKeys_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (sels : List Sel) :
    Follows cap (targetKeys ev sels) (targetKeys ev' sels) := by
  unfold targetKeys; follows [he, need_f, static_f, guardedBy_f]

theorem targetRoot_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (root : Resolve.Expr) :
    Follows cap (targetRoot ev root) (targetRoot ev' root) := by
  unfold targetRoot; follows [he, need_f]

theorem familyTarget_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (s rp : Pos) (x : String) (id : Nat)
    (sels : List Sel) :
    Follows cap (familyTarget ev s rp x id sels) (familyTarget ev' s rp x id sels) := by
  unfold familyTarget
  follows [he, need_f, guardedBy_f, selectionKey_f, targetKeys_f he, targetWalk_f, entryVal_f]

theorem targetPart_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (e : Resolve.Expr) :
    Follows cap (targetPart ev e) (targetPart ev' e) := by
  unfold targetPart
  follows [targetRoot_f he, targetKeys_f he, targetWalk_f, familyTarget_f he]

theorem target_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (e : Resolve.Expr) :
    Follows cap (target ev e) (target ev' e) := by
  unfold target; follows [targetPart_f he]

theorem queryKey_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) (i : Resolve.Expr) :
    Follows cap (queryKey ev i) (queryKey ev' i) := by
  unfold queryKey; follows [he, need_f, guardedBy_f, staticValue_f, static_f]

theorem queryWalk_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows cap (ev e) (ev' e)) :
    ∀ (q : Query) (sels : List Sel), Follows cap (queryWalk ev q sels) (queryWalk ev' q sels)
  | q, [] => by rw [queryWalk.eq_def, queryWalk.eq_def]; follows
  | q, sel :: rest => by
    rw [queryWalk.eq_def, queryWalk.eq_def]
    dsimp only
    follows [he, need_f, guardedBy_f, selectionKey_f, childPort_f, portFind_f, childFamily_f,
      queryKey_f he, queryStep_f, queryField_f, queryWalk_f he]
termination_by _ sels => sels.length
decreasing_by all_goals simp_all <;> omega

end helpers

/-! `hwStmt` and `instantiate` get the bound of their caller after the charge. -/

section walk
variable {k m : Nat}

theorem instantiate_f (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (pos : Pos)
    (i : Nat) (tvs : List (Ty × Value)) :
    Follows m (instantiate k pos i tvs) (instantiate m pos i tvs) := by
  rw [instantiate.eq_def k, instantiate.eq_def m]
  follows [hb, serialize_f, bindings_f, nested_f, inFrame_f, Follows.measure, bindLocal_f]

theorem childSel_f {ev ev' : Resolve.Expr → M (Option Out)}
    (he : ∀ e, Follows m (ev e) (ev' e)) (p q : Pos) (o : Out) (f : Ident) (x : Resolve.Expr) :
    Follows m (childSel ev p q o f x) (childSel ev' p q o f x) := by
  unfold childSel; follows [he, childFamily_f, need_f, guardedBy_f, selectionKey_f, childEntry_f]

theorem indexBase_f (he : ∀ e, Follows m (eval k e) (eval m e)) (p : Pos)
    (b x : Resolve.Expr) : Follows m (indexBase k p b x) (indexBase m p b x) := by
  rw [indexBase.eq_def k, indexBase.eq_def m]
  follows [he, need_f, fieldPart_f, childSel_f he]

theorem familySel_f (he : ∀ e, Follows m (eval k e) (eval m e)) (p np : Pos) (x : String)
    (id : Nat) (e : Resolve.Expr) :
    Follows m (familySel k p np x id e) (familySel m p np x id e) := by
  rw [familySel.eq_def k, familySel.eq_def m]
  follows [he, need_f, guardedBy_f, selectionKey_f, entryAt_f]

theorem typeOfPart_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t)) (p : Pos) (x : Resolve.Expr) :
    Follows m (typeOfPart k p x) (typeOfPart m p x) := by
  rw [typeOfPart.eq_def k, typeOfPart.eq_def m]
  follows [he, name_f he ht, queryWalk_f he, queryTy_f, need_f, guardedBy_f, selectionKey_f,
    entryVal_f]

theorem entryDecl_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t)) (p : Pos) (input : Bool) (x : Binder)
    (e : Resolve.Expr) (ty : Resolve.TypeExpr) :
    Follows m (entryDecl k p input x e ty) (entryDecl m p input x e ty) := by
  rw [entryDecl.eq_def k, entryDecl.eq_def m]
  follows [he, ht, need_f, guardedBy_f, static_f, familyKey_f, dataType_f, entry_f]

theorem hwStmt_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t))
    (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (s : Resolve.Stmt) :
    Follows m (hwStmt k s) (hwStmt m s) := by
  rw [hwStmt.eq_def k, hwStmt.eq_def m]
  follows [he, ht, instantiate_f hb, arguments_f he ht, need_f, copy_f, conform_f, static_f,
    lit_f, fresh_f, bindLocal_f, dataType_f, memWord_f, memDepth_f, port_f, resource_f,
    modifyBody_f, target_f he, bindTarget_f, sinkValue_f, typedUse_f, settle_f, structural_f,
    entryDecl_f he ht, guardedBy_f, keyed_f]

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
          changesOf_f, normalize_f, readRef_f, aggEq_f, fieldPart_f, indexBase_f (he k),
          enumUse_f (he k) (ht k), variantOf_f,
          operands_f (he k), comparable_f, params_f (ht k), fnTy_f, structural_f, scrutTy_f,
          matchArms_f, binderTys_f, bindArm_f, scrutParts_f, shared_f, matchHw_f,
          familySel_f (he k), typeOfPart_f (he k) (ht k), staticValue_f, fieldOut_f]
      · rw [eval.eq_def (k + 1), eval.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m) (ht m), name_f (he m) (ht m),
          call_f (he m) (ht m) (hb m), spec_f (he m) (ht m), need_f, data_f, baseData_f, apply_f,
          hwUnary_f, test_f, hwBinary_f, unify_f, mux_f, static_f, pick_f, element_f, tupleOf_f,
          arrayOf_f, select_f, containerOp_f, arrayTy_f, field_f, strAt_f, hold_f, release_f,
          changesOf_f, normalize_f, readRef_f, aggEq_f, fieldPart_f, indexBase_f (he m),
          enumUse_f (he m) (ht m), variantOf_f,
          operands_f (he m), comparable_f, params_f (ht m), fnTy_f, structural_f, scrutTy_f,
          matchArms_f, binderTys_f, bindArm_f, scrutParts_f, shared_f, matchHw_f,
          familySel_f (he m), typeOfPart_f (he m) (ht m), staticValue_f, fieldOut_f]
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
          static_f, store_f, hold_f, release_f, shut_f, hwCheck_f, hwStmt_f (he k) (ht k) (hb k)]
      · rw [stmt.eq_def (k + 1), stmt.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, hs m, hb m, placeAt_f (he m), need_f, copy_f, typedUse_f,
          heldUse_f, known_f, named_f, bindLocal_f, test_f, int_f, range_f, iteration_f,
          static_f, store_f, hold_f, release_f, shut_f, hwCheck_f, hwStmt_f (he m) (ht m) (hb m)]
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
