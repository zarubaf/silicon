-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval

/-!
The fuel of the evaluator: a part of the theorem `eval_cost` of section 10.3 of the front-end
spec. The result of `Eval` does not depend on spare fuel, and less fuel than a run uses gives
`S015`.

`Follows cap x y` relates two runs of `M`. Each time that `x` succeeds from the state `s` to
`s'`, it used `u = s.fuel - s'.fuel` units and did not add fuel. Then `y` from `s` with any
fuel `F ≤ cap` gives the value of `x` and the state `s'` with the fuel `F - u` if `u ≤ F`. If
`F < u`, it stops with `S015` and the records before it. The other fields of the state are
equal. Only `charge` reads the fuel in the evaluator, and nothing catches an error, so each
function of the evaluator follows itself. The cap holds the invariant "fuel ≤ bound" of the run
`y`. A run `y` within the cap never reaches the bound 0 when it has fuel for the work.

`follows_all` gives `Follows n' (f n a) (f n' a)` for `eval`, `typeExpr`, `stmt`, and `block`
at any two bounds `n` and `n'`. `Follows.shift` and `Follows.short` read off the two
directions for one run. `observe_budget` is the budget boundary of `Eval.observeRun`, with the
records: it needs only `∀ n n', Follows n' (act n) (act n')` of the action. `run_budget` is its
projection to the result. The elaborator and the lowering prove this premise for their actions
with the lemmas here (`Follows.bind` and the other lemmas of the monad, and the tactic
`follows`).
-/
namespace Silicon.Source.Eval.Fuel

open Resolve

/-- The fuel that a run from `s` to `s'` uses. -/
abbrev used (s s' : St) : Nat := s.fuel - s'.fuel

/-- The run of `y` with the fuel `F` agrees with the run of `x` that used `u` units. -/
@[reducible] def Follows.Res (a : α) (s' : St) (u F : Nat) (r : Except Stop (α × St)) :
    Prop :=
  (u ≤ F → r = .ok (a, { s' with fuel := F - u })) ∧
    (F < u → ∃ p m rs, r = .error ⟨⟨.S015, p, m⟩, rs⟩)

/--
`y` follows `x` with each fuel up to `cap`: a success of `x` that uses `u` units decides the
run of `y` with each such fuel (see the module doc).
-/
def Follows (cap : Nat) (x y : M α) : Prop :=
  ∀ c s a s', x c s = .ok (a, s') → s'.fuel ≤ s.fuel ∧ ∀ F, F ≤ cap →
    Follows.Res a s' (used s s') F (y c { s with fuel := F })

/-! The runs of the primitives of `M`. -/

theorem bind_apply (x : M α) (f : α → M β) (c : Ctx) (s : St) :
    (x >>= f) c s = match x c s with
      | .ok (a, s') => f a c s'
      | .error e => .error e := by
  show (x c s >>= fun p => f p.1 c p.2) = _
  cases x c s <;> rfl

theorem chargeWith_apply (p : Pos) (k : Nat) (cannot : Nat → String) (c : Ctx) (s : St) :
    chargeWith p k cannot c s = if k ≤ s.fuel then .ok ((), { s with fuel := s.fuel - k })
      else .error ⟨⟨.S015, p, cannot s.fuel⟩, s.records⟩ := by
  unfold chargeWith
  rw [bind_apply]
  show (if k ≤ s.fuel then _ else _ : M Unit) c s = _
  by_cases h : k ≤ s.fuel <;> simp only [h, ↓reduceIte] <;> rfl

theorem charge_apply (p : Pos) (k : Nat) (c : Ctx) (s : St) :
    charge p k c s = if k ≤ s.fuel then .ok ((), { s with fuel := s.fuel - k })
      else .error ⟨⟨.S015, p, payText k s.fuel⟩, s.records⟩ :=
  chargeWith_apply p k _ c s

theorem get_apply (c : Ctx) (s : St) : (get : M St) c s = .ok (s, s) := rfl

theorem set_apply (t : St) (c : Ctx) (s : St) : (set t : M PUnit) c s = .ok ((), t) := rfl

theorem read_apply (c : Ctx) (s : St) : (read : M Ctx) c s = .ok (c, s) := rfl

theorem pure_apply (a : α) (c : Ctx) (s : St) : (pure a : M α) c s = .ok (a, s) := rfl

namespace Follows

/-! The combinators of the monad. -/

theorem bind {x y : M α} {f g : α → M β} (hx : Follows cap x y)
    (hf : ∀ a, Follows cap (f a) (g a)) : Follows cap (x >>= f) (y >>= g) := by
  intro c s b s'' h
  rw [bind_apply] at h
  split at h
  next a s' hxs =>
    obtain ⟨m1, k1⟩ := hx c s a s' hxs
    obtain ⟨m2, k2⟩ := hf a c s' b s'' h
    refine ⟨Nat.le_trans m2 m1, fun F hF => ?_⟩
    have u : used s s'' = used s s' + used s' s'' := by simp only [used]; omega
    rw [bind_apply, u]
    by_cases h1 : used s s' ≤ F
    · rw [(k1 F hF).1 h1]
      have hF' : F - used s s' ≤ cap := by omega
      have e2 := k2 (F - used s s') hF'
      constructor
      · intro h2
        simp only []
        rw [e2.1 (by omega)]
        congr 3; omega
      · intro h2
        simp only []
        exact e2.2 (by omega)
    · obtain ⟨p, m, rs, he⟩ := (k1 F hF).2 (by omega)
      rw [he]
      exact ⟨fun _ => by omega, fun _ => ⟨p, m, rs, rfl⟩⟩
  next => cases h

/-- A computation that neither reads nor changes the fuel follows itself. -/
theorem of_frame {x : M α}
    (h : ∀ c s a s', x c s = .ok (a, s') →
      s'.fuel = s.fuel ∧ ∀ F, x c { s with fuel := F } = .ok (a, { s' with fuel := F })) :
    Follows cap x x := by
  intro c s a s' hx
  obtain ⟨e, k⟩ := h c s a s' hx
  refine ⟨Nat.le_of_eq e, fun F _ => ⟨fun _ => ?_, fun hF => by simp [used] at hF; omega⟩⟩
  rw [k F]; simp [used, e]

theorem pure (a : α) : Follows cap (Pure.pure a : M α) (Pure.pure a) :=
  of_frame fun _ _ _ _ h => by cases h; exact ⟨rfl, fun _ => rfl⟩

theorem fail (code : ErrorCode) (p : Pos) (m : String) :
    Follows cap (Eval.fail code p m : M α) (Eval.fail code p m) :=
  fun _ _ _ _ h => by cases h

theorem read : Follows cap (MonadReader.read : M Ctx) MonadReader.read :=
  of_frame fun _ _ _ _ h => by cases h; exact ⟨rfl, fun _ => rfl⟩

theorem chargeWith (p : Pos) (k : Nat) (cannot : Nat → String) :
    Follows cap (Eval.chargeWith p k cannot) (Eval.chargeWith p k cannot) := by
  intro c s a s' h
  rw [chargeWith_apply] at h
  split at h
  next hk =>
    cases h
    refine ⟨Nat.sub_le _ _, fun F _ => ⟨fun hF => ?_, fun hF => ?_⟩⟩
    · simp only [used] at hF ⊢
      rw [chargeWith_apply]
      simp only [show k ≤ F by omega, ↓reduceIte]
      congr 3; omega
    · simp only [used] at hF
      rw [chargeWith_apply]
      simp only [show ¬k ≤ F by omega, ↓reduceIte]
      exact ⟨_, _, _, rfl⟩
  · cases h

theorem charge (p : Pos) (k : Nat) : Follows cap (Eval.charge p k) (Eval.charge p k) :=
  chargeWith p k _

theorem get_bind {k k' : St → M α} (h : ∀ s, Follows cap (k s) (k' s))
    (hk : ∀ s F, k' { s with fuel := F } = k' s) : Follows cap (get >>= k) (get >>= k') := by
  intro c s a s' hx
  rw [bind_apply] at hx
  obtain ⟨m, k1⟩ := h s c s a s' hx
  refine ⟨m, fun F hF => ?_⟩
  rw [bind_apply]
  show Follows.Res _ _ _ _ ((k' { s with fuel := F }) c { s with fuel := F })
  rw [hk]
  exact k1 F hF

theorem modify (f : St → St) (hf : ∀ s F, f { s with fuel := F } = { f s with fuel := F })
    (hf' : ∀ s, (f s).fuel = s.fuel) : Follows cap (_root_.modify f : M PUnit) (_root_.modify f) :=
  of_frame fun c s a s' h => by
    cases h; exact ⟨hf' s, fun F => by show Except.ok ((), f { s with fuel := F }) = _; rw [hf]⟩

theorem withReader {x y : M α} (f : Ctx → Ctx) (h : Follows cap x y) :
    Follows cap (MonadWithReader.withReader f x) (MonadWithReader.withReader f y) :=
  fun c => h (f c)

theorem readThe : Follows cap (_root_.readThe Ctx : M Ctx) (_root_.readThe Ctx) :=
  of_frame fun _ _ _ _ h => by cases h; exact ⟨rfl, fun _ => rfl⟩

theorem monadLift {x y : M α} (h : Follows cap x y) :
    Follows cap (MonadLiftT.monadLift x : M α) (MonadLiftT.monadLift y) := h

theorem withTheReader {x y : M α} (f : Ctx → Ctx) (h : Follows cap x y) :
    Follows cap (_root_.withTheReader Ctx f x) (_root_.withTheReader Ctx f y) :=
  fun c => h (f c)

theorem lift (p : Pos) (e : Except Fault α) : Follows cap (Eval.lift p e) (Eval.lift p e) := by
  cases e with
  | ok a => exact pure a
  | error f => exact fail _ _ _

theorem mapM {f g : β → M γ} (h : ∀ b, Follows cap (f b) (g b)) :
    ∀ xs : List β, Follows cap (xs.mapM f) (xs.mapM g)
  | [] => pure _
  | x :: xs => by
    rw [List.mapM_cons, List.mapM_cons]
    exact bind (h x) fun _ => bind (mapM h xs) fun _ => pure _

theorem optionMapM {f g : β → M γ} (h : ∀ b, Follows cap (f b) (g b)) :
    ∀ o : Option β, Follows cap (o.mapM f) (o.mapM g)
  | none => pure _
  | some b => bind (h b) fun _ => pure _

theorem forIn {f g : β → γ → M (ForInStep γ)} (h : ∀ b a, Follows cap (f b a) (g b a)) :
    ∀ (xs : List β) (init : γ), Follows cap (ForIn.forIn xs init f) (ForIn.forIn xs init g)
  | [], _ => pure _
  | x :: xs, init => by
    rw [List.forIn_cons, List.forIn_cons]
    refine bind (h x init) fun r => ?_
    cases r with
    | done a => exact pure a
    | yield a => exact forIn h xs a

theorem forInRange {f g : Nat → γ → M (ForInStep γ)} (h : ∀ b a, Follows cap (f b a) (g b a))
    (r : Std.Legacy.Range) (init : γ) :
    Follows cap (ForIn.forIn r init f) (ForIn.forIn r init g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn h _ init

/-- An entry function charges one unit, then runs its body one bound lower. -/
theorem charge_one (p : Pos) {f g : PUnit → M α} (h : ∀ u, Follows cap (f u) (g u)) :
    Follows (cap + 1) (Eval.charge p 1 >>= f) (Eval.charge p 1 >>= g) := by
  intro c s a s' hx
  rw [bind_apply, charge_apply] at hx
  by_cases h1 : 1 ≤ s.fuel
  · simp only [h1, ↓reduceIte] at hx
    obtain ⟨m, k⟩ := h () c _ a s' hx
    try simp only [] at m
    refine ⟨by omega, fun F hF => ?_⟩
    rw [bind_apply, charge_apply]
    by_cases hF0 : 1 ≤ F
    · simp only [hF0, ↓reduceIte]
      have r := k (F - 1) (by omega)
      simp only [used] at r ⊢
      refine ⟨fun hu => ?_, fun hu => ?_⟩
      · rw [r.1 (by omega)]; congr 3; omega
      · exact r.2 (by omega)
    · simp only [hF0, ↓reduceIte]
      exact ⟨fun hu => by simp only [used] at hu; omega, fun _ => ⟨_, _, _, rfl⟩⟩
  · simp [h1] at hx

/-- With no fuel, an entry function at the bound 0 fails as its charge does. -/
theorem exhaust (p q : Pos) {f : PUnit → M α} (h : ∀ u, Follows cap (f u) (f u)) :
    Follows 0 (Eval.charge p 1 >>= f) (exhausted q) := by
  intro c s a s' hx
  rw [bind_apply, charge_apply] at hx
  by_cases h1 : 1 ≤ s.fuel
  · simp only [h1, ↓reduceIte] at hx
    obtain ⟨m, _⟩ := h () c _ a s' hx
    try simp only [] at m
    refine ⟨by omega, fun F hF => ?_⟩
    have : F = 0 := by omega
    subst this
    unfold exhausted
    rw [bind_apply, charge_apply]
    simp only [show ¬(1 ≤ 0) by omega, ↓reduceIte]
    exact ⟨fun hu => by simp only [used] at hu; omega, fun _ => ⟨_, _, _, rfl⟩⟩
  · simp [h1] at hx

/-- The bound 0 never succeeds. -/
theorem exhausted_left (p : Pos) (y : M α) : Follows cap (exhausted p) y := by
  intro c s a s' hx
  unfold exhausted at hx
  rw [bind_apply, charge_apply] at hx
  split at hx <;> cases hx

end Follows

attribute [irreducible] Follows

/--
Splits a goal `Follows cap x y` along the common structure of `x` and `y`. The local
hypotheses give the facts of the recursive calls.
-/
syntax "follows" (" [" term,* "]")? : tactic

/-- Applies the first of the given facts that fits the goal. -/
syntax "follows_by" " [" term,* "]" : tactic

macro_rules
  | `(tactic| follows_by []) => `(tactic| fail "no fact fits")
  | `(tactic| follows_by [$t:term]) => `(tactic| with_reducible apply $t)
  | `(tactic| follows_by [$t:term, $ts:term,*]) =>
    `(tactic| first | with_reducible apply $t | follows_by [$ts,*])

macro_rules | `(tactic| follows) => `(tactic| follows [])

macro_rules | `(tactic| follows [$ts,*]) => `(tactic| repeat' (first
  | intro _
  | with_reducible exact Follows.pure _
  | with_reducible exact Follows.charge _ _
  | with_reducible exact Follows.chargeWith _ _ _
  | with_reducible exact Follows.fail _ _ _
  | with_reducible exact Follows.read
  | with_reducible exact Follows.readThe
  | with_reducible apply Follows.monadLift
  | with_reducible apply Follows.withTheReader
  | with_reducible exact Follows.lift _ _
  | (with_reducible apply Follows.modify <;> intros <;> rfl)
  | (with_reducible apply Follows.get_bind; case hk => intros; rfl)
  | with_reducible apply Follows.withReader
  | with_reducible apply Follows.mapM
  | with_reducible apply Follows.optionMapM
  | with_reducible apply Follows.forIn
  | with_reducible apply Follows.forInRange
  | follows_by [$ts,*]
  | split
  | with_reducible apply Follows.bind
  | dsimp only))

/-! The helpers of the evaluator follow themselves. -/

section helpers
variable {cap : Nat}

theorem need_f (e : Resolve.Expr) (o : Option Out) : Follows cap (need e o) (need e o) := by
  unfold need; follows

theorem apply_f (p : Pos) (st : Except Fault Step) : Follows cap (apply p st) (apply p st) := by
  unfold apply; follows

theorem normalize_f (p : Pos) (a : Agg) : Follows cap (normalize p a) (normalize p a) := by
  unfold normalize; follows

theorem data_f (p : Pos) (v : Val) : Follows cap (data p v) (data p v) := by
  unfold data; follows [normalize_f]

theorem conform_f (p : Pos) (t : Ty) (v : Value) :
    Follows cap (conform p t v) (conform p t v) := by
  unfold conform; follows [apply_f]

theorem copy_f (p : Pos) (o : Out) :
    Follows cap (copy p o) (copy p o) := by
  unfold copy; follows

theorem hold_f (o : Out) : Follows cap (hold o) (hold o) := by
  unfold hold waits; follows

theorem release_f (o : Out) : Follows cap (release o) (release o) := by
  unfold release waits; follows

theorem pend_f (p : Pos) (x : String) (i : Nat) : Follows cap (pend p x i) (pend p x i) := by
  unfold pend; follows

theorem shut_f (i : Nat) : Follows cap (shut i) (shut i) := by
  unfold shut; follows

theorem held_f (p : Pos) (i : Nat) : Follows cap (held p i) (held p i) := by
  unfold held; follows

theorem changesOf_f (o : Out) : Follows cap (changesOf o) (changesOf o) := by
  unfold changesOf; follows

theorem static_f (p : Pos) (v : Val) :
    Follows cap (static p v) (static p v) := by
  unfold static; follows

theorem test_f (p : Pos) (v : Val) :
    Follows cap (test p v) (test p v) := by
  unfold test; follows

theorem place_f (e : Resolve.Expr) :
    Follows cap (place e) (place e) := by
  unfold place; follows

theorem int_f (p : Pos) (v : Val) :
    Follows cap (int p v) (int p v) := by
  unfold int; follows

theorem unify_f (p : Pos) (op : BinOp) (a b : Value) :
    Follows cap (unify p op a b) (unify p op a b) := by
  unfold unify; follows [conform_f]

theorem range_f (p : Pos) (a z : Int) :
    Follows cap (range p a z) (range p a z) := by
  unfold range; follows

theorem hwNode_f (p : Pos) (t : Ty) (op : Op) (xs : List Hw) :
    Follows cap (hwNode p t op xs) (hwNode p t op xs) := by
  unfold hwNode; follows

theorem node_f (p : Pos) (t : Ty) (op : Op) (xs : List Hw) :
    Follows cap (node p t op xs) (node p t op xs) := by
  unfold node; follows [hwNode_f]

theorem lit_f (p : Pos) (v : Value) :
    Follows cap (lit p v) (lit p v) := by
  unfold lit; follows

theorem litAt_f (p : Pos) (t : Ty) (v : Value) :
    Follows cap (litAt p t v) (litAt p t v) := by
  unfold litAt; follows [lit_f, conform_f]

theorem hwPair_f (p : Pos) (a b : Val) :
    Follows cap (hwPair p a b) (hwPair p a b) := by
  unfold hwPair; follows [litAt_f]

theorem hwUnary_f (p : Pos) (op : UnOp) (a : Hw) :
    Follows cap (hwUnary p op a) (hwUnary p op a) := by
  unfold hwUnary; follows [node_f]

theorem hwShift_f (p : Pos) (op : BinOp) (a b : Val) :
    Follows cap (hwShift p op a b) (hwShift p op a b) := by
  unfold hwShift; follows [litAt_f, node_f]

theorem hwBinary_f (p : Pos) (op : BinOp) (a b : Val) :
    Follows cap (hwBinary p op a b) (hwBinary p op a b) := by
  unfold hwBinary; follows [hwShift_f, hwPair_f, node_f]

theorem comparable_f (p : Pos) (op : BinOp) (a b : Val) :
    Follows cap (comparable p op a b) (comparable p op a b) := by
  unfold comparable; follows

theorem hwConvert_f (p : Pos) (f : PrimFn) (t : Ty) (x : Hw) :
    Follows cap (hwConvert p f t x) (hwConvert p f t x) := by
  unfold hwConvert; follows [node_f]

theorem known_f (v : Val) : Follows cap (known v) (known v) := by
  unfold known; follows

theorem bounded_f (p : Pos) (d : Nat) : Follows cap (bounded p d) (bounded p d) := by
  unfold bounded; follows

theorem sums_f (p : Pos) (ps : List Meta) (m : Meta) : Follows cap (sums p ps m) (sums p ps m) := by
  unfold sums; follows

theorem walked_f (p : Pos) (w : Walk α) : Follows cap (walked p w) (walked p w) := by
  unfold walked; follows

theorem containerOp_f (p : Pos) (op : BinOp) (a b : Value) :
    Follows cap (containerOp p op a b) (containerOp p op a b) := by
  unfold containerOp; follows [walked_f, apply_f]

theorem staticPair_f (p : Pos) (x y : Value) (acc : Pairs) :
    Follows cap (staticPair p x y acc) (staticPair p x y acc) := by
  unfold staticPair; follows

theorem leafPair_f (p : Pos) (a b : Agg) (acc : Pairs) :
    Follows cap (leafPair p a b acc) (leafPair p a b acc) := by
  unfold leafPair; follows [staticPair_f, hwPair_f, hwNode_f]

theorem eqWalk_f (fs : Ty → Option (Array (String × Ty))) (p : Pos) :
    ∀ (d : Nat) (t : Ty) (a b : Agg) (acc : Pairs),
      Follows cap (eqWalk fs p d t a b acc) (eqWalk fs p d t a b acc)
  | 0, t, a, b, acc => by rw [eqWalk.eq_def]; follows
  | d + 1, t, a, b, acc => by
    rw [eqWalk.eq_def]; dsimp only
    follows [eqWalk_f fs p d, staticPair_f, leafPair_f]

theorem aggEq_f (p : Pos) (op : BinOp) (a b : Val) :
    Follows cap (aggEq p op a b) (aggEq p op a b) := by
  unfold aggEq; follows [walked_f, eqWalk_f, lit_f, hwNode_f, node_f]

theorem ifStatic_f (p : Pos) (t : Ty) (x y : Value) :
    Follows cap (ifStatic p t x y) (ifStatic p t x y) := by
  unfold ifStatic; follows

theorem ifLeaf_f (p : Pos) (c : Hw) (t : Ty) (a b : Agg) :
    Follows cap (ifLeaf p c t a b) (ifLeaf p c t a b) := by
  unfold ifLeaf; follows [litAt_f, hwPair_f, hwNode_f]

theorem ifPart_f (p : Pos) (c : Hw) (t : Ty) (a b : Agg) :
    Follows cap (ifPart p c t a b) (ifPart p c t a b) := by
  unfold ifPart; follows [ifStatic_f, ifLeaf_f]

theorem ifWalk_f (fs : Ty → Option (Array (String × Ty))) (p : Pos) (c : Hw) :
    ∀ (d : Nat) (t : Ty) (a b : Agg),
      Follows cap (ifWalk fs p c d t a b) (ifWalk fs p c d t a b)
  | 0, t, a, b => by rw [ifWalk.eq_def]; follows
  | d + 1, t, a, b => by
    rw [ifWalk.eq_def]; dsimp only
    follows [ifWalk_f fs p c d, ifPart_f]

theorem shared_f (c : Hw) (n : Nat) : Follows cap (shared c n) (shared c n) := by
  unfold shared; follows

theorem mux_f (p : Pos) (c : Hw) (a b : Val) :
    Follows cap (mux p c a b) (mux p c a b) := by
  unfold mux; follows [walked_f, ifPart_f, shared_f, ifWalk_f]

theorem typeOf_f (p : Pos) (x : String) (v : Val) :
    Follows cap (typeOf p x v) (typeOf p x v) := by
  unfold typeOf; follows

theorem tupleTy_f (p : Pos) (ts : List Ty) : Follows cap (tupleTy p ts) (tupleTy p ts) := by
  unfold tupleTy; follows [bounded_f, sums_f]

theorem fnTy_f (p : Pos) (ps : List TyParam) (r : Ty) :
    Follows cap (fnTy p ps r) (fnTy p ps r) := by
  unfold fnTy; follows [bounded_f]

theorem arrayTy_f (p q : Pos) (e : Ty) (v : Value) :
    Follows cap (arrayTy p q e v) (arrayTy p q e v) := by
  unfold arrayTy; follows [bounded_f]

theorem selectAt_f (p q : Pos) (i : Nat) (v : Val) :
    Follows cap (selectAt p q i v) (selectAt p q i v) := by
  unfold selectAt; follows

theorem selectKey_f (p q : Pos) (i : Nat) (v : Val) :
    Follows cap (selectKey p q i v) (selectKey p q i v) := by
  unfold selectKey; follows [selectAt_f, normalize_f]

theorem select_f (p q : Pos) (i : Nat) (v : Val) :
    Follows cap (select p q i v) (select p q i v) := by
  unfold select; follows [selectKey_f]

theorem indexOf_f (q : Pos) (i : Value) : Follows cap (indexOf q i) (indexOf q i) := by
  unfold indexOf; follows

theorem pickAt_f (p q : Pos) (v : Val) (i : Value) :
    Follows cap (pickAt p q v i) (pickAt p q v i) := by
  unfold pickAt; follows [indexOf_f]

theorem chargeScan_f (p : Pos) (v : Value) :
    Follows cap (chargeScan p v) (chargeScan p v) := by
  unfold chargeScan; follows

theorem strAt_f (p q : Pos) (s : String) (i : Value) :
    Follows cap (strAt p q s i) (strAt p q s i) := by
  unfold strAt; follows [indexOf_f, chargeScan_f]

theorem within_f (q : Pos) (n : Nat) (i : Value) :
    Follows cap (within q n i) (within q n i) := by
  unfold within; follows [indexOf_f]

theorem pickKey_f (p q : Pos) (v : Val) (i : Value) :
    Follows cap (pickKey p q v i) (pickKey p q v i) := by
  unfold pickKey; follows [pickAt_f, within_f, normalize_f]

theorem pick_f (p q : Pos) (v : Val) (i : Value) :
    Follows cap (pick p q v i) (pick p q v i) := by
  unfold pick; follows [pickKey_f]

theorem lenOf_f (p : Pos) (vs : List Val) : Follows cap (lenOf p vs) (lenOf p vs) := by
  unfold lenOf; follows [data_f, chargeScan_f]

theorem fieldOf_f (p : Pos) (f : Ident) (t : Ty) (x : String) :
    Follows cap (fieldOf p f t x) (fieldOf p f t x) := by
  unfold fieldOf; follows

theorem fieldAt_f (p : Pos) (f : Ident) (v : Val) :
    Follows cap (fieldAt p f v) (fieldAt p f v) := by
  unfold fieldAt; follows [fieldOf_f]

theorem fieldKey_f (p : Pos) (f : Ident) (v : Val) :
    Follows cap (fieldKey p f v) (fieldKey p f v) := by
  unfold fieldKey; follows [fieldOf_f, fieldAt_f, normalize_f]

theorem field_f (p : Pos) (f : Ident) (v : Val) :
    Follows cap (field p f v) (field p f v) := by
  unfold field; follows [fieldKey_f]

theorem zero_f (p : Pos) (t : Ty) : Follows cap (zero p t) (zero p t) := by
  unfold zero; follows [bounded_f]

theorem typedAgg_f (p : Pos) (t : Ty) (a : Agg) :
    Follows cap (typedAgg p t a) (typedAgg p t a) := by
  unfold typedAgg; follows [bounded_f]

theorem conformAgg_f (p : Pos) (t : Ty) (a : Agg) :
    Follows cap (conformAgg p t a) (conformAgg p t a) := by
  unfold conformAgg; follows [conform_f, typedAgg_f]

theorem element_f (p : Pos) (v : Val) : Follows cap (element p v) (element p v) := by
  unfold element; follows

theorem item_f (p : Pos) (v : Val) : Follows cap (item p v) (item p v) := by
  unfold item; follows [element_f]

theorem made_f (p : Pos) (a : Agg) : Follows cap (made p a) (made p a) := by
  unfold made; follows [bounded_f]

theorem tupleOf_f (p : Pos) (xs : List Agg) :
    Follows cap (tupleOf p xs) (tupleOf p xs) := by
  unfold tupleOf; follows [made_f]

theorem arrayOf_f (p : Pos) (xs : List Agg) :
    Follows cap (arrayOf p xs) (arrayOf p xs) := by
  unfold arrayOf; follows [walked_f, conformAgg_f, made_f]

mutual
  theorem build_f (p : Pos) : ∀ (t : Ty) (x : Part), Follows cap (build p t x) (build p t x)
    | t, .value v => by rw [build.eq_def]; dsimp only; follows
    | t, .empty q => by rw [build.eq_def]; dsimp only; follows [bounded_f]
    | t, .array q ps => by rw [build.eq_def]; dsimp only; follows [buildAll_f p, arrayOf_f]
    | t, .tuple q ps => by rw [build.eq_def]; dsimp only; follows [buildZip_f p, tupleOf_f]

  theorem buildAll_f (p : Pos) (t : Ty) :
      ∀ xs : List Part, Follows cap (buildAll p t xs) (buildAll p t xs)
    | [] => by rw [buildAll]; follows
    | x :: xs => by rw [buildAll]; follows [build_f p t x, buildAll_f p t xs]

  theorem buildZip_f (p : Pos) :
      ∀ (ts : List Ty) (xs : List Part), Follows cap (buildZip p ts xs) (buildZip p ts xs)
    | t :: ts, x :: xs => by
      rw [buildZip.eq_def]; dsimp only; follows [build_f p t x, buildZip_f p ts xs]
    | [], _ => by rw [buildZip.eq_def]; dsimp only; follows
    | _ :: _, [] => by rw [buildZip.eq_def]; dsimp only; follows
end

theorem settle_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (settle p t v) (settle p t v) := by
  unfold settle; follows [build_f]

theorem recordOf_f (p : Pos) (t : Ty) (fs : List Ty) (ps : List Pos) (vs : List Val) :
    Follows cap (recordOf p t fs ps vs) (recordOf p t fs ps vs) := by
  unfold recordOf; follows [conformAgg_f, item_f, data_f, settle_f, made_f]

theorem conformVal_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (conformVal p t v) (conformVal p t v) := by
  unfold conformVal; follows [settle_f, data_f, conform_f, typedAgg_f]

theorem readUse_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (readUse p t v) (readUse p t v) := by
  unfold readUse; follows [settle_f, data_f, conformVal_f]

theorem copyUse_f (p : Pos) (t : Ty) (c : Bool) (v : Val) :
    Follows cap (copyUse p t c v) (copyUse p t c v) := by
  unfold copyUse; follows [readUse_f, conformVal_f]

theorem version_f (k : Tag) (b : Names.Path) :
    Follows cap (version k b) (version k b) := by
  unfold version; follows

theorem fresh_f (i : Nat) (u : String) :
    Follows cap (fresh i u) (fresh i u) := by
  unfold fresh; follows [version_f]

theorem bindHw_f (p : Pos) (q : Names.Path) (h : Hw) :
    Follows cap (bindHw p q h) (bindHw p q h) := by
  unfold bindHw; follows

theorem bindAgg_f (p : Pos) (q : Names.Path) (a : Agg) :
    Follows cap (bindAgg p q a) (bindAgg p q a) := by
  unfold bindAgg; follows

theorem named_f (p : Pos) (i : Nat) (u : String) (v : Val) :
    Follows cap (named p i u v) (named p i u v) := by
  unfold named; follows [fresh_f, bindHw_f, bindAgg_f]

theorem bindLocal_f (i : Nat) (sl : Slot) :
    Follows cap (bindLocal i sl) (bindLocal i sl) := by
  unfold bindLocal; follows

theorem setConst_f (i : Nat) (e : Entry) :
    Follows cap (setConst i e) (setConst i e) := by
  unfold setConst; follows

theorem mutation_f (p : Pos) (x : String) : Follows cap (mutation p x) (mutation p x) := by
  unfold mutation; follows

theorem setAt_f (p : Pos) (a y : Agg) (ks : List Nat) :
    Follows cap (setAt p a y ks) (setAt p a y ks) := by
  unfold setAt; follows

theorem changeAt_f (p : Pos) (pl : Place) (f : Value → Value) (sz : Nat → Nat)
    (d : Option Nat) : Follows cap (changeAt p pl f sz d) (changeAt p pl f sz d) := by
  unfold changeAt; follows [held_f, bindLocal_f, setAt_f]

theorem rebind_f (p : Pos) (pl : Place) (sl : Slot) (a o x : Agg) :
    Follows cap (rebind p pl sl a o x) (rebind p pl sl a o x) := by
  unfold rebind; follows [held_f, setAt_f, bindAgg_f, fresh_f, bindLocal_f]

theorem store_f (p q : Pos) (pl : Place) (y : Val) :
    Follows cap (store p q pl y) (store p q pl y) := by
  unfold store; follows [named_f, held_f, bindLocal_f, item_f, bounded_f, changeAt_f, rebind_f]

theorem finals_f (ps : List Resolve.Param) (acts : List Actual) :
    Follows cap (finals ps acts) (finals ps acts) := by
  unfold finals; follows

theorem writeBack_f (p : Pos) (outs : List (Place × Val)) :
    Follows cap (writeBack p outs) (writeBack p outs) := by
  unfold writeBack; follows [mutation_f, bounded_f, store_f]

theorem prim_f (p : Pos) (x : String) (k : PrimType) :
    Follows cap (prim p x k) (prim p x k) := by
  unfold prim; follows

theorem frameOf_f (u : String) (y : Nat) (f : Names.Field) :
    Follows cap (frameOf u y f) (frameOf u y f) := by
  apply Follows.of_frame
  intro c s a s' h
  simp only [frameOf, bind_apply, read_apply, get_apply] at h ⊢
  cases hk : s.naming.frames[(c.frame.id, y, f)]? <;>
    simp only [hk, bind_apply, set_apply, pure_apply] at h ⊢ <;>
    cases h <;> exact ⟨rfl, fun _ => rfl⟩

theorem nested_f (p : Pos) {x y : M α} (h : Follows cap x y) :
    Follows cap (nested p x) (nested p y) := by
  unfold nested; follows [h]

theorem structural_f {x y : M α} (h : Follows cap x y) :
    Follows cap (structural x) (structural y) := by
  unfold structural; follows [h]

theorem inFrame_f (r : Option Ty) {x y : M α} (h : Follows cap x y) :
    Follows cap (inFrame r x) (inFrame r y) := by
  unfold inFrame; follows [h]

theorem inFrameOf_f (fr : Frame) {x y : M α} (h : Follows cap x y) :
    Follows cap (inFrameOf fr x) (inFrameOf fr y) := by
  unfold inFrameOf; follows [h]

theorem constant_f (p : Pos) (x : String) (i : Nat) {b b' : M Value} (h : Follows cap b b') :
    Follows cap (constant p x i b) (constant p x i b') := by
  unfold constant; follows [h, setConst_f, nested_f, inFrame_f, structural_f]

theorem specialize_f (p : Pos) (x : String) (i : Nat) (pre : Bool) (args : List Value)
    {f g : M (List (String × Ty))} (h : Follows cap f g) :
    Follows cap (specialize p x i pre args f) (specialize p x i pre args g) := by
  unfold specialize; follows [h, bounded_f, sums_f]

/-! A moved error keeps its code, so a run without the fuel still gives `S015`. -/
theorem atUse_f (p : Pos) {x y : M α} (h : Follows cap x y) :
    Follows cap (atUse p x) (atUse p y) := by
  unfold Follows at h ⊢
  intro c s a s' hx
  simp only [atUse] at hx
  split at hx
  · next r hr =>
    cases hx
    obtain ⟨h1, h2⟩ := h c s a s' hr
    refine ⟨h1, fun F hF => ⟨fun hu => ?_, fun hu => ?_⟩⟩
    · simp only [atUse, (h2 F hF).1 hu]
    · obtain ⟨q, m, rs, e⟩ := (h2 F hF).2 hu
      exact ⟨p, m, rs, by simp only [atUse, e]⟩
  · cases hx

theorem iteration_f (p : Pos) (i : Binder) (v : Int) {x y : M α} (h : Follows cap x y) :
    Follows cap (iteration p i v x) (iteration p i v y) := by
  unfold iteration; follows [h, frameOf_f, inFrameOf_f, bindLocal_f]

theorem copyIn_f (p : Pos) (c : Bool) (q : Resolve.Param) (t : Ty) (a : Actual) :
    Follows cap (copyIn p c q t a) (copyIn p c q t a) := by
  unfold copyIn
  follows [static_f, settle_f, conform_f, copyUse_f, named_f, bindLocal_f]

theorem result_f (p : Pos) (path : Names.Path) (u : String) (o : Option Val) :
    Follows cap (result p path u o) (result p path u o) := by
  unfold result; follows [bindHw_f, bindAgg_f]

theorem pushOnto_f (p x : Pos) (g : String) (pl : Place) (v : Val) :
    Follows cap (pushOnto p x g pl v) (pushOnto p x g pl v) := by
  unfold pushOnto; follows [mutation_f, data_f, settle_f, conform_f, bounded_f, changeAt_f]

theorem popFrom_f (p : Pos) (g : String) (pl : Place) :
    Follows cap (popFrom p g pl) (popFrom p g pl) := by
  unfold popFrom; follows [mutation_f, changeAt_f]

theorem dataBitsOf_f (p : Pos) (g : String) (vs : List Val) :
    Follows cap (dataBitsOf p g vs) (dataBitsOf p g vs) := by
  unfold dataBitsOf; follows

theorem message_f (p : Pos) (g : String) (v : Val) :
    Follows cap (message p g v) (message p g v) := by
  unfold message; follows [data_f]

theorem diagnose_f (p : Pos) (g : String) (m v : Val) :
    Follows cap (diagnose p g m v) (diagnose p g m v) := by
  unfold diagnose; follows [message_f]

theorem primCall_f (p : Pos) (g : String) (h : PrimFn) (vs : List Val) :
    Follows cap (primCall p g h vs) (primCall p g h vs) := by
  unfold primCall
  follows [lenOf_f, dataBitsOf_f, static_f, data_f, apply_f, hwConvert_f, bounded_f,
    diagnose_f]

theorem bindParams_f {ty ty' : Resolve.TypeExpr → M Ty} (h : ∀ t, Follows cap (ty t) (ty' t))
    (p : Pos) (ps : List Resolve.Param) (args : List Val) :
    Follows cap (bindParams ty p ps args) (bindParams ty' p ps args) := by
  unfold bindParams
  follows [h, conform_f, static_f, settle_f, bindLocal_f]

theorem specOf_f {ty ty' : Resolve.TypeExpr → M Ty} (h : ∀ t, Follows cap (ty t) (ty' t))
    (p : Pos) (i : Nat) (x : Ident) (ps : List Resolve.Param) (fs : List Resolve.StructField)
    (pre : Bool) (args : List Val) :
    Follows cap (specOf ty p i x ps fs pre args) (specOf ty' p i x ps fs pre args) := by
  unfold specOf
  follows [h, bindParams_f h, specialize_f, nested_f, inFrame_f, atUse_f]

theorem responseTy_f {ty ty' : Resolve.TypeExpr → M Ty} (h : ∀ t, Follows cap (ty t) (ty' t))
    (p : Pos) (t : Ty) : Follows cap (responseTy ty p t) (responseTy ty' p t) := by
  unfold responseTy; follows [specOf_f h]

theorem requestPart_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (requestPart p t v) (requestPart p t v) := by
  unfold requestPart; follows [readUse_f]

theorem portCall_f {u u' : Ty → M Ty} (h : ∀ t, Follows cap (u t) (u' t)) (p : Pos) (g : String)
    (f : PrimFn) (vs : List Val) : Follows cap (portCall p g f vs u) (portCall p g f vs u') := by
  unfold portCall; follows [h, requestPart_f, bounded_f]

end helpers

/-!
The functions of the mutual block. A helper gets the bound of its caller after the charge, so
its lemma takes the facts of the entry functions at the bounds `k` and `m`.
-/

section evaluator
variable {k m : Nat}

theorem operands_f (he : ∀ e, Follows m (eval k e) (eval m e)) (xs : List Resolve.Expr)
    {f : Resolve.Expr → Out → M α} (hf : ∀ x o, Follows m (f x o) (f x o)) :
    Follows m (operands k xs f) (operands m xs f) := by
  rw [operands.eq_def k, operands.eq_def m]
  follows [he, hf, need_f, hold_f, release_f]

theorem index_f (he : ∀ e, Follows m (eval k e) (eval m e)) (p : Pos) (kd : PrimType)
    (xs : List Resolve.Expr) : Follows m (index k p kd xs) (index m p kd xs) := by
  rw [index.eq_def k, index.eq_def m]
  follows [he, operands_f he, static_f, need_f, bounded_f]

theorem spec_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t)) (p : Pos) (i : Nat)
    (xs : List Resolve.Expr) : Follows m (spec k p i xs) (spec m p i xs) := by
  rw [spec.eq_def k, spec.eq_def m]
  follows [operands_f he, need_f, static_f, specOf_f ht, structural_f]

theorem params_f (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t))
    (ps : List Resolve.FnParam) : Follows m (params k ps) (params m ps) := by
  rw [params.eq_def k, params.eq_def m]
  follows [ht]

theorem name_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t)) (p : Pos) (x : String) (r : Ref) :
    Follows m (name k p x r) (name m p x r) := by
  rw [name.eq_def k, name.eq_def m]
  follows [he, ht, prim_f, need_f, copy_f, conform_f, static_f, settle_f, constant_f,
    spec_f he ht, nested_f, inFrame_f, params_f ht, fnTy_f, normalize_f]

theorem placeAt_f (he : ∀ e, Follows m (eval k e) (eval m e)) (p : Pos) (c : ErrorCode)
    (t : Resolve.Expr) : Follows m (placeAt k p c t) (placeAt m p c t) := by
  rw [placeAt.eq_def k, placeAt.eq_def m]
  follows [he, place_f, pend_f, need_f, static_f, pickKey_f, selectKey_f, fieldKey_f]

theorem args_f (he : ∀ e, Follows m (eval k e) (eval m e)) (b : Nat)
    (xs : List Resolve.Expr) : Follows m (args k b xs) (args m b xs) := by
  rw [args.eq_def k, args.eq_def m]
  follows [operands_f he, need_f]

theorem ctor_f (he : ∀ e, Follows m (eval k e) (eval m e)) (p : Pos) (o : Out)
    (b : Nat) (xs : List Resolve.Expr) : Follows m (ctor k p o b xs) (ctor m p o b xs) := by
  rw [ctor.eq_def k, ctor.eq_def m]
  follows [he, args_f he, need_f, static_f, conform_f, zero_f, recordOf_f, hold_f, release_f]

theorem actuals_f (he : ∀ e, Follows m (eval k e) (eval m e)) (xs : List Resolve.Expr)
    (muts : List Bool) : Follows m (actuals k xs muts) (actuals m xs muts) := by
  rw [actuals.eq_def k, actuals.eq_def m]
  follows [he, placeAt_f he, need_f, hold_f, release_f, shut_f]

theorem invoke_f (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t))
    (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (p : Pos) (i j : Nat) (c : Bool)
    (u : Ident) (ps : List Resolve.Param) (ret : Resolve.TypeExpr) (ip : Pos)
    (body : List Resolve.Stmt) (acts : List Actual) :
    Follows m (invoke k p i j c u ps ret ip body acts)
      (invoke m p i j c u ps ret ip body acts) := by
  rw [invoke.eq_def k, invoke.eq_def m]
  follows [ht, hb, copyIn_f, result_f, frameOf_f, nested_f, inFrame_f, finals_f, writeBack_f]

theorem call_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t))
    (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (p : Pos) (f : Resolve.Expr)
    (xs : List Resolve.Expr) (b j : Nat) :
    Follows m (call k p f xs b j) (call m p f xs b j) := by
  rw [call.eq_def k, call.eq_def m]
  follows [he, placeAt_f he, args_f he, ctor_f he, actuals_f he, invoke_f ht hb, need_f,
    hold_f, release_f, shut_f, pushOnto_f, popFrom_f, primCall_f,
    portCall_f (responseTy_f ht _)]

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
        follows [he k, ht k, index_f (he k), name_f (he k) (ht k),
          call_f (he k) (ht k) (hb k), spec_f (he k) (ht k), need_f, data_f, apply_f,
          hwUnary_f, test_f, hwBinary_f, unify_f, mux_f, static_f, pick_f, element_f, tupleOf_f,
          arrayOf_f, select_f, containerOp_f, arrayTy_f, field_f, strAt_f, hold_f, release_f,
          changesOf_f, normalize_f, aggEq_f,
          operands_f (he k), comparable_f, params_f (ht k), fnTy_f, structural_f]
      · rw [eval.eq_def (k + 1), eval.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m), name_f (he m) (ht m),
          call_f (he m) (ht m) (hb m), spec_f (he m) (ht m), need_f, data_f, apply_f,
          hwUnary_f, test_f, hwBinary_f, unify_f, mux_f, static_f, pick_f, element_f, tupleOf_f,
          arrayOf_f, select_f, containerOp_f, arrayTy_f, field_f, strAt_f, hold_f, release_f,
          changesOf_f, normalize_f, aggEq_f,
          operands_f (he m), comparable_f, params_f (ht m), fnTy_f, structural_f]
    · rcases n' with _ | m
      · rw [typeExpr.eq_def (k + 1), typeExpr.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, index_f (he k), name_f (he k) (ht k), spec_f (he k) (ht k),
          typeOf_f, tupleTy_f, arrayTy_f, static_f, need_f, params_f (ht k), fnTy_f,
          structural_f]
      · rw [typeExpr.eq_def (k + 1), typeExpr.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m), name_f (he m) (ht m), spec_f (he m) (ht m),
          typeOf_f, tupleTy_f, arrayTy_f, static_f, need_f, params_f (ht m), fnTy_f,
          structural_f]
    · rcases n' with _ | m
      · rw [stmt.eq_def (k + 1), stmt.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, hs k, hb k, placeAt_f (he k), need_f, copy_f, copyUse_f,
          known_f, named_f, bindLocal_f, test_f, int_f, range_f, iteration_f, static_f,
          store_f, hold_f, release_f, shut_f]
      · rw [stmt.eq_def (k + 1), stmt.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, hs m, hb m, placeAt_f (he m), need_f, copy_f, copyUse_f,
          known_f, named_f, bindLocal_f, test_f, int_f, range_f, iteration_f, static_f,
          store_f, hold_f, release_f, shut_f]
    · rcases n' with _ | m
      · rw [block.eq_def (k + 1), block.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [hs k]
      · rw [block.eq_def (k + 1), block.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [hs m]

end evaluator

/-! The two directions of `Follows` for one run. -/

/-- With `δ` more fuel and room for it in the cap, the run gives the same value. -/
theorem Follows.shift {x y : M α} (h : Follows cap x y) {c : Ctx} {s s' : St} {a : α}
    (hx : x c s = .ok (a, s')) (δ : Nat) (hcap : s.fuel + δ ≤ cap) :
    y c { s with fuel := s.fuel + δ } = .ok (a, { s' with fuel := s'.fuel + δ }) := by
  delta Follows at h
  obtain ⟨m, k⟩ := h c s a s' hx
  rw [(k _ hcap).1 (by simp only [used]; omega)]
  congr 3; simp only [used]; omega

/-- With less fuel than the run of `x` used, the run gives `S015`. -/
theorem Follows.short {x y : M α} (h : Follows cap x y) {c : Ctx} {s s' : St} {a : α}
    (hx : x c s = .ok (a, s')) {F : Nat} (hF : F < s.fuel - s'.fuel) (hcap : F ≤ cap) :
    ∃ p m rs, y c { s with fuel := F } = .error ⟨⟨.S015, p, m⟩, rs⟩ := by
  delta Follows at h
  exact ((h c s a s' hx).2 F hcap).2 hF

theorem observeRun_apply (budget : Budget) (items : Array Resolve.Item) (act : Nat → M α)
    (top : Scan) :
    observeRun budget items act top =
      match act budget.fuel (start budget items top).1 (start budget items top).2 with
      | .ok (a, s) => (s.records, .ok (a, budget.fuel - s.fuel))
      | .error e => (e.records, .error e.err) := by
  unfold observeRun
  rcases hs : start budget items top with ⟨ctx, st⟩
  rfl

/--
The budget boundary of `Eval.observeRun`. Let the runs of an action follow each other at each
pair of bounds. Then the action uses the same fuel `u` with each budget. Each fuel from `u`
gives the same records and result, and each fuel below `u` gives `S015`.
-/
theorem observe_budget {act : Nat → M α} (hact : ∀ n n', Follows n' (act n) (act n'))
    {budget : Budget} {items : Array Resolve.Item} {top : Scan} {rs : Array Record} {a : α}
    {u : Nat} (h : observeRun budget items act top = (rs, .ok (a, u))) (F : Nat) :
    (u ≤ F → observeRun { budget with fuel := F } items act top = (rs, .ok (a, u))) ∧
    (F < u → ∃ p m,
      (observeRun { budget with fuel := F } items act top).2 = .error ⟨.S015, p, m⟩) := by
  rw [observeRun_apply] at h
  split at h
  next a' s' hx =>
    simp only [Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hf := hact budget.fuel F
    unfold Follows at hf
    obtain ⟨_, k⟩ := hf _ _ a' s' hx
    have r := k F (Nat.le_refl F)
    have e : start { budget with fuel := F } items top =
        ((start budget items top).1, { (start budget items top).2 with fuel := F }) := rfl
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · rw [observeRun_apply, e]
      have hs : (start budget items top).2.fuel = budget.fuel := rfl
      simp only [r.1 hu, Prod.mk.injEq, Except.ok.injEq, true_and]
      simp only [used, hs] at hu ⊢
      omega
    · obtain ⟨p, m, rs, he⟩ := r.2 hu
      exact ⟨p, m, by rw [observeRun_apply, e]; simp only [he]⟩
  next => simp at h

/--
The budget boundary of `Eval.run`. Let the runs of an action follow each other at each pair
of bounds. Then the action uses the same fuel `u` with each budget. Each fuel from `u` gives
the same result, and each fuel below `u` gives `S015`.
-/
theorem run_budget {act : Nat → M α} (hact : ∀ n n', Follows n' (act n) (act n'))
    {budget : Budget} {items : Array Resolve.Item} {top : Scan} {a : α} {u : Nat}
    (h : run budget items act top = .ok (a, u)) (F : Nat) :
    (u ≤ F → run { budget with fuel := F } items act top = .ok (a, u)) ∧
    (F < u → ∃ p m, run { budget with fuel := F } items act top = .error ⟨.S015, p, m⟩) :=
  have r := observe_budget hact
    (Prod.ext rfl h : observeRun budget items act top = (_, .ok (a, u))) F
  ⟨fun hu => congrArg Prod.snd (r.1 hu), r.2⟩

/-- The budget boundary of a static expression in the file scope. -/
theorem evalExpr_budget {budget : Budget} {items : Array Resolve.Item} {e : Resolve.Expr}
    {v : Value} {u : Nat} (h : evalExpr budget items e = .ok (v, u)) (F : Nat) :
    (u ≤ F → evalExpr { budget with fuel := F } items e = .ok (v, u)) ∧
    (F < u → ∃ p m, evalExpr { budget with fuel := F } items e = .error ⟨.S015, p, m⟩) :=
  run_budget (fun n n' => by follows [(follows_all n).1 n', static_f, need_f]) h F

end Silicon.Source.Eval.Fuel
