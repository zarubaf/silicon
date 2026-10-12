-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval

/-!
The fuel of the evaluator: a part of the theorem `eval_cost` of section 10.3 of the front-end
spec. The result of `Eval` does not depend on spare fuel, and less fuel than a run uses gives
`S015`.

`Follows cap x y` relates two runs of `M`. Each time that `x` succeeds from the state `s` to
`s'`, it used `u = s.fuel - s'.fuel` units and did not add fuel. Then `y` from `s` with any
fuel `F ≤ cap` gives the value of `x` and the state `s'` with the fuel `F - u` if `u ≤ F`, and
`S015` if `F < u`. The other fields of the state are equal. Only `charge` reads the fuel in
the evaluator, and nothing catches an error, so each function of the evaluator follows
itself. The cap holds the invariant "fuel ≤ bound" of the run `y`. A run `y` within the cap
never reaches the bound 0 when it has fuel for the work.

`follows_all` gives `Follows n' (f n a) (f n' a)` for `eval`, `typeExpr`, `stmt`, and `block`
at any two bounds `n` and `n'`. `Follows.shift` and `Follows.short` read off the two
directions for one run. `run_budget` is the budget boundary of `Eval.run`: it needs only
`∀ n n', Follows n' (act n) (act n')` of the action. The elaborator and the lowering prove
this premise for their actions with the lemmas here (`Follows.bind` and the other lemmas
of the monad, and the tactic `follows`).
-/
namespace Silicon.Source.Eval.Fuel

open Resolve

/-- The fuel that a run from `s` to `s'` uses. -/
abbrev used (s s' : St) : Nat := s.fuel - s'.fuel

/-- The run of `y` with the fuel `F` agrees with the run of `x` that used `u` units. -/
@[reducible] def Follows.Res (a : α) (s' : St) (u F : Nat) (r : Except Error (α × St)) :
    Prop :=
  (u ≤ F → r = .ok (a, { s' with fuel := F - u })) ∧
    (F < u → ∃ p m, r = .error ⟨.S015, p, m⟩)

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

theorem charge_apply (p : Pos) (k : Nat) (c : Ctx) (s : St) :
    charge p k c s = if k ≤ s.fuel then .ok ((), { s with fuel := s.fuel - k })
      else .error ⟨.S015, p,
        s!"the fuel cannot pay {intText k} unit(s); {intText s.fuel} remain"⟩ := by
  unfold charge
  rw [bind_apply]
  show (if k ≤ s.fuel then _ else _ : M Unit) c s = _
  by_cases h : k ≤ s.fuel <;> simp only [h, ↓reduceIte] <;> rfl

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
    · obtain ⟨p, m, he⟩ := (k1 F hF).2 (by omega)
      rw [he]
      exact ⟨fun _ => by omega, fun _ => ⟨p, m, rfl⟩⟩
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

theorem throw (e : Error) : Follows cap (MonadExcept.throw e : M α) (MonadExcept.throw e) :=
  fun _ _ _ _ h => by cases h

theorem read : Follows cap (MonadReader.read : M Ctx) MonadReader.read :=
  of_frame fun _ _ _ _ h => by cases h; exact ⟨rfl, fun _ => rfl⟩

theorem charge (p : Pos) (k : Nat) : Follows cap (Eval.charge p k) (Eval.charge p k) := by
  intro c s a s' h
  rw [charge_apply] at h
  split at h
  next hk =>
    cases h
    refine ⟨Nat.sub_le _ _, fun F _ => ⟨fun hF => ?_, fun hF => ?_⟩⟩
    · simp only [used] at hF ⊢
      rw [charge_apply]
      simp only [show k ≤ F by omega, ↓reduceIte]
      congr 3; omega
    · simp only [used] at hF
      rw [charge_apply]
      simp only [show ¬k ≤ F by omega, ↓reduceIte]
      exact ⟨_, _, rfl⟩
  · cases h

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
      exact ⟨fun hu => by simp only [used] at hu; omega, fun _ => ⟨_, _, rfl⟩⟩
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
    exact ⟨fun hu => by simp only [used] at hu; omega, fun _ => ⟨_, _, rfl⟩⟩
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
  | with_reducible exact Follows.fail _ _ _
  | with_reducible exact Follows.throw _
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

theorem data_f (p : Pos) (v : Val) : Follows cap (data p v) (data p v) := by
  unfold data; follows

theorem conform_f (p : Pos) (t : Ty) (v : Value) :
    Follows cap (conform p t v) (conform p t v) := by
  unfold conform; follows [apply_f]

theorem copy_f (p : Pos) (o : Out) :
    Follows cap (copy p o) (copy p o) := by
  unfold copy; follows

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

theorem node_f (p : Pos) (t : Ty) (op : Op) (xs : List Hw) :
    Follows cap (node p t op xs) (node p t op xs) := by
  unfold node; follows

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

theorem mux_f (p : Pos) (c : Hw) (a b : Val) :
    Follows cap (mux p c a b) (mux p c a b) := by
  unfold mux; follows [lit_f, litAt_f, hwPair_f, node_f]

theorem hwConvert_f (p : Pos) (f : PrimFn) (t : Ty) (x : Hw) :
    Follows cap (hwConvert p f t x) (hwConvert p f t x) := by
  unfold hwConvert; follows [node_f]

theorem known_f (v : Val) : Follows cap (known v) (known v) := by
  unfold known; follows

theorem bounded_f (p : Pos) (d : Nat) : Follows cap (bounded p d) (bounded p d) := by
  unfold bounded; follows

theorem walked_f (p : Pos) (w : Walk α) : Follows cap (walked p w) (walked p w) := by
  unfold walked; follows

theorem containerOp_f (p : Pos) (op : BinOp) (a b : Value) :
    Follows cap (containerOp p op a b) (containerOp p op a b) := by
  unfold containerOp; follows [walked_f, apply_f]

theorem typeOf_f (p : Pos) (x : String) (v : Val) :
    Follows cap (typeOf p x v) (typeOf p x v) := by
  unfold typeOf; follows

theorem tupleTy_f (p : Pos) (ts : List Ty) : Follows cap (tupleTy p ts) (tupleTy p ts) := by
  unfold tupleTy; follows [bounded_f]

theorem element_f (p : Pos) (v : Val) : Follows cap (element p v) (element p v) := by
  unfold element; follows

theorem item_f (p : Pos) (v : Val) : Follows cap (item p v) (item p v) := by
  unfold item; follows [element_f]

theorem tupleOf_f (p : Pos) (vs : List Value) :
    Follows cap (tupleOf p vs) (tupleOf p vs) := by
  unfold tupleOf; follows [bounded_f]

theorem arrayOf_f (p : Pos) (vs : List Value) :
    Follows cap (arrayOf p vs) (arrayOf p vs) := by
  unfold arrayOf; follows [walked_f, conform_f, bounded_f]

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

theorem arrayTy_f (p q : Pos) (e : Ty) (v : Value) :
    Follows cap (arrayTy p q e v) (arrayTy p q e v) := by
  unfold arrayTy; follows [bounded_f]

theorem selectAt_f (p q : Pos) (i : Nat) (v : Val) :
    Follows cap (selectAt p q i v) (selectAt p q i v) := by
  unfold selectAt; follows

theorem select_f (p q : Pos) (i : Nat) (v : Val) :
    Follows cap (select p q i v) (select p q i v) := by
  unfold select; follows [selectAt_f]

theorem pickAt_f (p q : Pos) (v : Val) (i : Value) :
    Follows cap (pickAt p q v i) (pickAt p q v i) := by
  unfold pickAt; follows

theorem pick_f (p q : Pos) (v : Val) (i : Value) :
    Follows cap (pick p q v i) (pick p q v i) := by
  unfold pick; follows [pickAt_f]

theorem lenOf_f (p : Pos) (vs : List Val) : Follows cap (lenOf p vs) (lenOf p vs) := by
  unfold lenOf; follows [data_f]

theorem fieldAt_f (p : Pos) (f : Ident) (v : Val) :
    Follows cap (fieldAt p f v) (fieldAt p f v) := by
  unfold fieldAt; follows

theorem recordOf_f (p : Pos) (t : Ty) (fs : List Ty) (ps : List Pos) (vs : List Val) :
    Follows cap (recordOf p t fs ps vs) (recordOf p t fs ps vs) := by
  unfold recordOf; follows [conform_f, item_f, settle_f, bounded_f]

theorem zero_f (p : Pos) (t : Ty) : Follows cap (zero p t) (zero p t) := by
  unfold zero; follows [bounded_f]

theorem conformVal_f (p : Pos) (t : Ty) (v : Val) :
    Follows cap (conformVal p t v) (conformVal p t v) := by
  unfold conformVal; follows [settle_f, data_f, conform_f]

theorem version_f (k : Tag) (b : Names.Path) :
    Follows cap (version k b) (version k b) := by
  unfold version; follows

theorem fresh_f (i : Nat) (u : String) :
    Follows cap (fresh i u) (fresh i u) := by
  unfold fresh; follows [version_f]

theorem bindHw_f (p : Pos) (q : Names.Path) (h : Hw) :
    Follows cap (bindHw p q h) (bindHw p q h) := by
  unfold bindHw; follows

theorem named_f (p : Pos) (i : Nat) (u : String) (v : Val) :
    Follows cap (named p i u v) (named p i u v) := by
  unfold named; follows [fresh_f, bindHw_f]

theorem bindLocal_f (i : Nat) (sl : Slot) :
    Follows cap (bindLocal i sl) (bindLocal i sl) := by
  unfold bindLocal; follows

theorem setConst_f (i : Nat) (e : Entry) :
    Follows cap (setConst i e) (setConst i e) := by
  unfold setConst; follows

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

theorem inFrame_f (r : Option Ty) {x y : M α} (h : Follows cap x y) :
    Follows cap (inFrame r x) (inFrame r y) := by
  unfold inFrame; follows [h]

theorem inFrameOf_f (fr : Frame) {x y : M α} (h : Follows cap x y) :
    Follows cap (inFrameOf fr x) (inFrameOf fr y) := by
  unfold inFrameOf; follows [h]

theorem constant_f (p : Pos) (x : String) (i : Nat) {b b' : M Value} (h : Follows cap b b') :
    Follows cap (constant p x i b) (constant p x i b') := by
  unfold constant; follows [h, setConst_f, nested_f, inFrame_f]

theorem specialize_f (p : Pos) (x : String) (i : Nat) (args : List Value) {f g : M (List Ty)}
    (h : Follows cap f g) : Follows cap (specialize p x i args f) (specialize p x i args g) := by
  unfold specialize; follows [h, bounded_f]

theorem iteration_f (p : Pos) (i : Binder) (v : Int) {x y : M α} (h : Follows cap x y) :
    Follows cap (iteration p i v x) (iteration p i v y) := by
  unfold iteration; follows [h, frameOf_f, inFrameOf_f, bindLocal_f]

end helpers

/-!
The functions of the mutual block. A helper gets the bound of its caller after the charge, so
its lemma takes the facts of the entry functions at the bounds `k` and `m`.
-/

section evaluator
variable {k m : Nat}

theorem index_f (he : ∀ e, Follows m (eval k e) (eval m e)) (p : Pos) (kd : PrimType)
    (xs : List Resolve.Expr) : Follows m (index k p kd xs) (index m p kd xs) := by
  rw [index.eq_def k, index.eq_def m]
  follows [he, static_f, need_f]

theorem spec_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t)) (p : Pos) (i : Nat)
    (xs : List Resolve.Expr) : Follows m (spec k p i xs) (spec m p i xs) := by
  rw [spec.eq_def k, spec.eq_def m]
  follows [he, ht, need_f, static_f, specialize_f, nested_f, inFrame_f, conform_f, bindLocal_f]

theorem name_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t)) (p : Pos) (x : String) (r : Ref) :
    Follows m (name k p x r) (name m p x r) := by
  rw [name.eq_def k, name.eq_def m]
  follows [he, ht, prim_f, need_f, copy_f, conform_f, static_f, settle_f, constant_f,
    spec_f he ht]

theorem call_f (he : ∀ e, Follows m (eval k e) (eval m e))
    (ht : ∀ t, Follows m (typeExpr k t) (typeExpr m t))
    (hb : ∀ p ss, Follows m (block k p ss) (block m p ss)) (p : Pos) (f : Resolve.Expr)
    (xs : List Resolve.Expr) : Follows m (call k p f xs) (call m p f xs) := by
  rw [call.eq_def k, call.eq_def m]
  follows [he, ht, hb, need_f, static_f, settle_f, data_f, conform_f, conformVal_f, apply_f,
    hwConvert_f, lenOf_f, named_f, bindLocal_f, bindHw_f, version_f, frameOf_f, nested_f,
    inFrame_f, zero_f, recordOf_f]

/--
Each function of the evaluator at any bound `n` is followed by the same function at the
bound `n'`, with each fuel up to `n'`.
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
          arrayOf_f, select_f, containerOp_f, arrayTy_f, fieldAt_f]
      · rw [eval.eq_def (k + 1), eval.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m), name_f (he m) (ht m),
          call_f (he m) (ht m) (hb m), spec_f (he m) (ht m), need_f, data_f, apply_f,
          hwUnary_f, test_f, hwBinary_f, unify_f, mux_f, static_f, pick_f, element_f, tupleOf_f,
          arrayOf_f, select_f, containerOp_f, arrayTy_f, fieldAt_f]
    · rcases n' with _ | m
      · rw [typeExpr.eq_def (k + 1), typeExpr.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, index_f (he k), name_f (he k) (ht k), spec_f (he k) (ht k),
          typeOf_f, tupleTy_f, arrayTy_f, static_f, need_f]
      · rw [typeExpr.eq_def (k + 1), typeExpr.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, index_f (he m), name_f (he m) (ht m), spec_f (he m) (ht m),
          typeOf_f, tupleTy_f, arrayTy_f, static_f, need_f]
    · rcases n' with _ | m
      · rw [stmt.eq_def (k + 1), stmt.eq_def 0]
        apply Follows.exhaust (cap := k)
        intro _
        follows [he k, ht k, hs k, hb k, need_f, copy_f, conformVal_f, known_f, named_f,
          bindLocal_f, place_f, test_f, int_f, range_f, iteration_f, static_f, pickAt_f,
          selectAt_f, item_f, fieldAt_f]
      · rw [stmt.eq_def (k + 1), stmt.eq_def (m + 1)]
        apply Follows.charge_one
        intro _
        follows [he m, ht m, hs m, hb m, need_f, copy_f, conformVal_f, known_f, named_f,
          bindLocal_f, place_f, test_f, int_f, range_f, iteration_f, static_f, pickAt_f,
          selectAt_f, item_f, fieldAt_f]
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
    ∃ p m, y c { s with fuel := F } = .error ⟨.S015, p, m⟩ := by
  delta Follows at h
  exact ((h c s a s' hx).2 F hcap).2 hF

theorem run_apply (budget : Budget) (items : Array Resolve.Item) (act : Nat → M α) :
    run budget items act =
      match act budget.fuel (start budget items).1 (start budget items).2 with
      | .ok (a, s) => .ok (a, budget.fuel - s.fuel)
      | .error e => .error e := by
  unfold run
  rcases hs : start budget items with ⟨ctx, st⟩
  simp only []
  show (act budget.fuel ctx st >>= fun x => pure (x.1, budget.fuel - x.2.fuel)) = _
  cases act budget.fuel ctx st <;> rfl

/--
The budget boundary of `Eval.run`. Let the runs of an action follow each other at each pair
of bounds. Then the action uses the same fuel `u` with each budget. Each fuel from `u` gives
the same result, and each fuel below `u` gives `S015`.
-/
theorem run_budget {act : Nat → M α} (hact : ∀ n n', Follows n' (act n) (act n'))
    {budget : Budget} {items : Array Resolve.Item} {a : α} {u : Nat}
    (h : run budget items act = .ok (a, u)) (F : Nat) :
    (u ≤ F → run { budget with fuel := F } items act = .ok (a, u)) ∧
    (F < u → ∃ p m, run { budget with fuel := F } items act = .error ⟨.S015, p, m⟩) := by
  rw [run_apply] at h
  split at h
  next a' s' hx =>
    cases h
    have hf : Follows F (act budget.fuel) (act F) := hact budget.fuel F
    unfold Follows at hf
    obtain ⟨_, k⟩ := hf _ _ a s' hx
    have r := k F (Nat.le_refl F)
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · rw [run_apply]
      show (match act F (start budget items).1 { (start budget items).2 with fuel := F } with
        | .ok (a, s) => Except.ok (a, F - s.fuel) | .error e => Except.error e) = _
      rw [r.1 hu]
      simp only [used] at hu ⊢
      congr 2
      show F - (F - (budget.fuel - s'.fuel)) = budget.fuel - s'.fuel
      omega
    · obtain ⟨p, m, he⟩ := r.2 hu
      refine ⟨p, m, ?_⟩
      rw [run_apply]
      show (match act F (start budget items).1 { (start budget items).2 with fuel := F } with
        | .ok (a, s) => Except.ok (a, F - s.fuel) | .error e => Except.error e) = _
      rw [he]
  next => cases h

/-- The budget boundary of a static expression in the file scope. -/
theorem evalExpr_budget {budget : Budget} {items : Array Resolve.Item} {e : Resolve.Expr}
    {v : Value} {u : Nat} (h : evalExpr budget items e = .ok (v, u)) (F : Nat) :
    (u ≤ F → evalExpr { budget with fuel := F } items e = .ok (v, u)) ∧
    (F < u → ∃ p m, evalExpr { budget with fuel := F } items e = .error ⟨.S015, p, m⟩) :=
  run_budget (fun n n' => by follows [(follows_all n).1 n', static_f, need_f]) h F

end Silicon.Source.Eval.Fuel
