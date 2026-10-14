-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Elab
import Silicon.Source.Proof.Fuel

/-!
The fuel of the elaborator: a part of the theorem `eval_cost` of section 10.3 of the front-end
spec. The result of `Elab.elaborate` does not depend on spare fuel, and less fuel than an
elaboration uses gives `S015`.

The walk runs in `EM`, a state monad over `Eval.M`. `EFollows cap x y` holds when `y` follows
`x` (`Eval.Fuel.Follows`) from each state of `EM`. The state of `EM` holds no fuel, so its
`get`, `set`, and `modify` follow themselves. The only read of the absolute fuel is in
`Elab.measure`, and it gives only the difference of the fuel around its action. That
difference is the same in each run that succeeds, so `measure` keeps `EFollows`.

`follows_all` gives `EFollows n' (f n a) (f n' a)` for `stmt` and `block` at any two bounds,
and `elaborate_budget` is the budget boundary of `Elab.elaborate` by `Eval.Fuel.run_budget`.
The tactic `efollows` is the tactic `follows` with the lemmas of `EM`.
-/
namespace Silicon.Source.Elab.Fuel

open Eval Eval.Fuel

/-- `y` follows `x` from each state of `EM`. -/
def EFollows (cap : Nat) (x y : EM α) : Prop := ∀ σ, Follows cap (x.run σ) (y.run σ)

theorem lift_run (x : Eval.M α) (σ : St) :
    (MonadLiftT.monadLift x : EM α).run σ = x >>= fun a => Pure.pure (a, σ) := rfl

theorem lift_bind_run (x : Eval.M α) (f : α → EM β) (σ : St) :
    (MonadLiftT.monadLift x >>= f : EM β).run σ = x >>= fun a => (f a).run σ := by
  rw [StateT.run_bind, lift_run, bind_assoc]
  simp only [pure_bind]

/-- The run of `measure`: the value gets the difference of the fuel around the action. -/
theorem measure_apply (x : EM α) (σ : St) (c : Ctx) (s : Eval.St) :
    (measure x).run σ c s = match x.run σ c s with
      | .ok ((a, σ'), s') => .ok (((a, s.fuel - s'.fuel), σ'), s')
      | .error e => .error e := by
  unfold measure
  rw [lift_bind_run]
  simp only [StateT.run_bind, bind_apply, get_apply, pure_apply]
  rcases x.run σ c s with _ | ⟨⟨a, σ'⟩, s'⟩ <;> rfl

namespace EFollows

theorem bind {x y : EM α} {f g : α → EM β} (hx : EFollows cap x y)
    (hf : ∀ a, EFollows cap (f a) (g a)) : EFollows cap (x >>= f) (y >>= g) :=
  fun σ => Follows.bind (hx σ) fun p => hf p.1 p.2

theorem pure (a : α) : EFollows cap (Pure.pure a : EM α) (Pure.pure a) :=
  fun _ => Follows.pure _

theorem get : EFollows cap (MonadState.get : EM St) MonadState.get :=
  fun _ => Follows.pure _

theorem set (t : St) : EFollows cap (MonadState.set t : EM PUnit) (MonadState.set t) :=
  fun _ => Follows.pure _

theorem setOf (t : St) : EFollows cap (MonadStateOf.set t : EM PUnit) (MonadStateOf.set t) :=
  fun _ => Follows.pure _

theorem modify (f : St → St) : EFollows cap (_root_.modify f : EM PUnit) (_root_.modify f) :=
  fun _ => Follows.pure _

theorem monadLift {x y : Eval.M α} (h : Follows cap x y) :
    EFollows cap (MonadLiftT.monadLift x : EM α) (MonadLiftT.monadLift y) :=
  fun σ => by
    show Follows cap (x >>= fun a => Pure.pure (a, σ)) (y >>= fun a => Pure.pure (a, σ))
    exact Follows.bind h fun _ => Follows.pure _

theorem read : EFollows cap (MonadReader.read : EM Ctx) MonadReader.read :=
  monadLift Follows.read

theorem readThe : EFollows cap (_root_.readThe Ctx : EM Ctx) (_root_.readThe Ctx) :=
  monadLift Follows.read

theorem withTheReader {x y : EM α} (f : Ctx → Ctx) (h : EFollows cap x y) :
    EFollows cap (_root_.withTheReader Ctx f x) (_root_.withTheReader Ctx f y) :=
  fun σ => Follows.withTheReader f (h σ)

theorem mapM {f g : β → EM γ} (h : ∀ b, EFollows cap (f b) (g b)) :
    ∀ xs : List β, EFollows cap (xs.mapM f) (xs.mapM g)
  | [] => pure _
  | x :: xs => by
    rw [List.mapM_cons, List.mapM_cons]
    exact bind (h x) fun _ => bind (mapM h xs) fun _ => pure _

theorem forIn {f g : β → γ → EM (ForInStep γ)} (h : ∀ b a, EFollows cap (f b a) (g b a)) :
    ∀ (xs : List β) (init : γ), EFollows cap (ForIn.forIn xs init f) (ForIn.forIn xs init g)
  | [], _ => pure _
  | x :: xs, init => by
    rw [List.forIn_cons, List.forIn_cons]
    refine bind (h x init) fun r => ?_
    cases r with
    | done a => exact pure a
    | yield a => exact forIn h xs a

theorem forInArray {f g : β → γ → EM (ForInStep γ)} (h : ∀ b a, EFollows cap (f b a) (g b a))
    (xs : Array β) (init : γ) :
    EFollows cap (ForIn.forIn xs init f) (ForIn.forIn xs init g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn h _ init

theorem forInRange {f g : Nat → γ → EM (ForInStep γ)} (h : ∀ b a, EFollows cap (f b a) (g b a))
    (r : Std.Legacy.Range) (init : γ) :
    EFollows cap (ForIn.forIn r init f) (ForIn.forIn r init g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn h _ init

/-- The difference of the fuel is the same in each run that succeeds. -/
theorem measure {x y : EM α} (h : EFollows cap x y) :
    EFollows cap (Elab.measure x) (Elab.measure y) := by
  intro σ
  have e := h σ
  unfold Follows at e ⊢
  intro c s r s'' hx
  rw [measure_apply] at hx
  split at hx
  next a σ' s' hxs =>
    cases hx
    obtain ⟨m, k⟩ := e c s _ _ hxs
    refine ⟨m, fun F hF => ⟨fun hu => ?_, fun hu => ?_⟩⟩
    · rw [measure_apply, (k F hF).1 hu]
      simp only [used] at hu ⊢
      congr 4; omega
    · obtain ⟨p, m, rs, he⟩ := (k F hF).2 hu
      exact ⟨p, m, rs, by rw [measure_apply, he]⟩
  next => cases hx

/-- An entry function charges one unit, then runs its body one bound lower. -/
theorem charge_one (p : Pos) {f g : PUnit → EM α} (h : ∀ u, EFollows cap (f u) (g u)) :
    EFollows (cap + 1) (MonadLiftT.monadLift (charge p 1) >>= f)
      (MonadLiftT.monadLift (charge p 1) >>= g) := fun σ => by
  rw [lift_bind_run, lift_bind_run]
  exact Follows.charge_one p fun u => h u σ

/-- With no fuel, an entry function at the bound 0 fails as its charge does. -/
theorem exhaust (p q : Pos) {f : PUnit → EM α} (h : ∀ u, EFollows cap (f u) (f u)) :
    EFollows 0 (MonadLiftT.monadLift (charge p 1) >>= f)
      (MonadLiftT.monadLift (exhausted q : Eval.M α)) := fun σ => by
  have e := Follows.exhaust (cap := cap) p q (f := fun u => (f u).run σ) fun u => h u σ
  rw [lift_bind_run, lift_run]
  unfold Follows at e ⊢
  intro c s a s' hx
  obtain ⟨m, k⟩ := e c s a s' hx
  refine ⟨m, fun F hF => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · have r := (k F hF).1 hu
    unfold exhausted at r
    rw [bind_apply, charge_apply] at r
    split at r <;> cases r
  · obtain rfl : F = 0 := by omega
    rw [bind_apply]
    unfold exhausted
    rw [bind_apply, charge_apply]
    simp only [show ¬(1 ≤ 0) by omega, ↓reduceIte]
    exact ⟨_, _, _, rfl⟩

theorem run {x y : EM α} (h : EFollows cap x y) (σ : St) :
    Follows cap (x.run σ) (y.run σ) := h σ

/-- The bound 0 never succeeds. -/
theorem exhausted_left (p : Pos) (y : EM α) :
    EFollows cap (MonadLiftT.monadLift (exhausted p : Eval.M α)) y := fun σ => by
  rw [lift_run]
  unfold Follows
  intro c s a s' hx
  rw [bind_apply] at hx
  split at hx
  next hx' =>
    unfold exhausted at hx'
    rw [bind_apply, charge_apply] at hx'
    split at hx' <;> cases hx'
  next => cases hx

end EFollows

attribute [irreducible] EFollows

/-- The tactic `follows` with the lemmas of `EM` after the given facts. -/
syntax "efollows" (" [" term,* "]")? : tactic

macro_rules | `(tactic| efollows) => `(tactic| efollows [EFollows.pure])

macro_rules | `(tactic| efollows [$ts,*]) => `(tactic| follows [$ts,*, EFollows.pure,
  EFollows.get, EFollows.set, EFollows.setOf, EFollows.modify, EFollows.read,
  EFollows.readThe, EFollows.monadLift, EFollows.withTheReader,
  EFollows.mapM, EFollows.forIn, EFollows.forInArray, EFollows.forInRange, EFollows.bind])

section helpers
variable {cap : Nat}

theorem nested_e (p : Pos) {x y : EM α} (h : EFollows cap x y) :
    EFollows cap (nested p x) (nested p y) := by
  unfold nested; efollows [h]

theorem structural_e {x y : EM α} (h : EFollows cap x y) :
    EFollows cap (structural x) (structural y) := by
  unfold structural; efollows [h]

theorem inFrame_e (r : Option Ty) {x y : EM α} (h : EFollows cap x y) :
    EFollows cap (inFrame r x) (inFrame r y) := by
  unfold inFrame; efollows [h]

theorem inFrameOf_e (fr : Frame) {x y : EM α} (h : EFollows cap x y) :
    EFollows cap (inFrameOf fr x) (inFrameOf fr y) := by
  unfold inFrameOf; efollows [h]

theorem iteration_e (p : Pos) (i : Resolve.Binder) (v : Int) {x y : EM α} (h : EFollows cap x y) :
    EFollows cap (iteration p i v x) (iteration p i v y) := by
  unfold iteration; efollows [h, inFrameOf_e, frameOf_f, bindLocal_f]

theorem bindings_e : EFollows cap bindings bindings := by
  unfold bindings; efollows

theorem modifyBody_e (f : Body → Body) : EFollows cap (modifyBody f) (modifyBody f) := by
  unfold modifyBody; efollows

theorem slot_e (id : Nat) : EFollows cap (slot id) (slot id) := by
  unfold slot; efollows

theorem dataType_e (p : Pos) (t : Ty) : EFollows cap (dataType p t) (dataType p t) := by
  unfold dataType; efollows

theorem memWord_e (p : Pos) (t : Ty) : EFollows cap (memWord p t) (memWord p t) := by
  unfold memWord; efollows

theorem memDepth_e (p : Pos) (v : Val) : EFollows cap (memDepth p v) (memDepth p v) := by
  unfold memDepth; efollows

theorem resource_e (k : Kind) (path : Names.Path) (t : Ty) (p : Pos) (x : String) :
    EFollows cap (resource k path t p x) (resource k path t p x) := by
  unfold resource; efollows

theorem port_e (p : Pos) (input : Bool) (b : Resolve.Binder) (t : Ty) :
    EFollows cap (port p input b t) (port p input b t) := by
  unfold port
  refine EFollows.bind EFollows.readThe fun c =>
    EFollows.bind (EFollows.monadLift (Follows.of_frame ?_)) fun _ => ?_
  · intro c s a s' h
    simp only [bind_apply, get_apply, set_apply, pure_apply] at h ⊢
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  · efollows [resource_e, modifyBody_e, normalize_f]

theorem target_e (p : Pos) (e : Resolve.Expr) : EFollows cap (target p e) (target p e) := by
  unfold target; efollows [slot_e]

theorem bindTarget_e (p : Pos) (t : Target) (h : Agg) :
    EFollows cap (bindTarget p t h) (bindTarget p t h) := by
  unfold bindTarget; efollows [modifyBody_e]

theorem sinkValue_e (p : Pos) (t : Ty) (v : Val) :
    EFollows cap (sinkValue p t v) (sinkValue p t v) := by
  unfold sinkValue; efollows [lit_f]

theorem serialize_e (p : Pos) (m : String) (vs : List Value) :
    EFollows cap (serialize p m vs) (serialize p m vs) := by
  unfold serialize; efollows

end helpers

/-! `instantiate` gets the bound of its caller after the charge, as a helper of `Eval`. -/

section walk
variable {k m : Nat}

theorem instantiate_e (ht : ∀ t, Follows m (Eval.typeExpr k t) (Eval.typeExpr m t))
    (hb : ∀ p ss, EFollows m (block k p ss) (block m p ss)) (pos : Pos) (i : Nat)
    (vs : List Value) : EFollows m (instantiate k pos i vs) (instantiate m pos i vs) := by
  rw [instantiate.eq_def k, instantiate.eq_def m]
  efollows [ht, hb, serialize_e, bindings_e, nested_e, inFrame_e, EFollows.measure, conform_f,
    bindLocal_f]

theorem arguments_e (he : ∀ e, Follows m (Eval.eval k e) (Eval.eval m e))
    (ht : ∀ t, Follows m (Eval.typeExpr k t) (Eval.typeExpr m t)) (pos : Pos) (i : Nat)
    (xs : List Resolve.Expr) : EFollows m (arguments k pos i xs) (arguments m pos i xs) := by
  unfold arguments
  efollows [he, ht, need_f, static_f, settle_f, inFrame_e, bindLocal_f, hold_f, release_f]

end walk

/--
The walk functions at the bound `n'` follow the walk functions at any bound `n`, with each
fuel up to `n'`.
-/
theorem follows_all : ∀ n,
    (∀ n' s, EFollows n' (stmt n s) (stmt n' s)) ∧
    (∀ n' p ss, EFollows n' (block n p ss) (block n' p ss))
  | 0 => by
    refine ⟨fun n' s => ?_, fun _ p ss => ?_⟩
    · rw [stmt.eq_def 0, stmt.eq_def n']
      split
      all_goals first
        | exact EFollows.exhausted_left _ _
        | efollows [(Eval.Fuel.follows_all 0).2.2.1 n']
    · rw [block.eq_def]; exact EFollows.exhausted_left _ _
  | k + 1 => by
    obtain ⟨hs, hb⟩ := follows_all k
    have he := Eval.Fuel.follows_all k
    refine ⟨fun n' s => ?_, fun n' p ss => ?_⟩
    · rw [stmt.eq_def (k + 1), stmt.eq_def n']
      split
      all_goals first
        | efollows [(Eval.Fuel.follows_all (k + 1)).2.2.1 n']; done
        | skip
      all_goals rcases n' with _ | m
      · refine EFollows.exhaust (cap := k) _ _ fun _ => ?_
        efollows [hs k, hb k, instantiate_e (he.2.1 k) (hb k),
          arguments_e (he.1 k) (he.2.1 k), he.1 k, he.2.1 k, need_f, copy_f,
          conform_f, static_f, conformVal_f, lit_f, fresh_f, bindLocal_f, test_f, int_f, range_f,
          iteration_e, dataType_e, memWord_e, memDepth_e, port_e, resource_e, modifyBody_e,
          target_e, bindTarget_e, sinkValue_e, copyUse_f, settle_f, hold_f, release_f,
          structural_e]
      · refine EFollows.charge_one _ fun _ => ?_
        efollows [hs m, hb m, instantiate_e (he.2.1 m) (hb m),
          arguments_e (he.1 m) (he.2.1 m), he.1 m, he.2.1 m, need_f, copy_f,
          conform_f, static_f, conformVal_f, lit_f, fresh_f, bindLocal_f, test_f, int_f, range_f,
          iteration_e, dataType_e, memWord_e, memDepth_e, port_e, resource_e, modifyBody_e,
          target_e, bindTarget_e, sinkValue_e, copyUse_f, settle_f, hold_f, release_f,
          structural_e]
    · rcases n' with _ | m
      · rw [block.eq_def (k + 1), block.eq_def 0]
        exact EFollows.exhaust (cap := k) _ _ fun _ => by efollows [hs k]
      · rw [block.eq_def (k + 1), block.eq_def (m + 1)]
        exact EFollows.charge_one _ fun _ => by efollows [hs m]

/--
The budget boundary of `elaborate`. If the elaboration uses `u` units, each fuel from `u` gives
the same design and units, and each fuel below `u` gives `S015`.
-/
theorem elaborate_budget {budget : Budget} {items : Array Resolve.Item}
    {digest : String → String} {pos : Pos} {top : Nat} {xs : List Resolve.Expr} {d : Design}
    {u : Nat} (h : elaborate budget items digest pos top xs = .ok (d, u)) (F : Nat) :
    (u ≤ F → elaborate { budget with fuel := F } items digest pos top xs = .ok (d, u)) ∧
    (F < u → ∃ p m,
      elaborate { budget with fuel := F } items digest pos top xs = .error ⟨.S015, p, m⟩) := by
  refine run_budget (fun n n' => ?_) h F
  follows [EFollows.run]
  efollows [(Eval.Fuel.follows_all n).1 n', static_f, need_f,
    instantiate_e ((Eval.Fuel.follows_all n).2.1 n') ((follows_all n).2 n'),
    arguments_e ((Eval.Fuel.follows_all n).1 n') ((Eval.Fuel.follows_all n).2.1 n')]

end Silicon.Source.Elab.Fuel
