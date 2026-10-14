-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Flatten

/-!
The fuel of the lowering: a part of the theorem `eval_cost` of section 10.3 of the front-end
spec. The result of `Flatten.flatten` does not depend on spare fuel, and less fuel than a
lowering uses gives `S015`.

The lowering runs in `FM`, a state monad without a reader and without a bound. Thus the
relation is simpler than `Eval.Fuel.Follows`: `FFollows x` holds when `x` follows itself. A
success of `x` from `s` to `s'` uses `u = s.fuel - s'.fuel` units and adds no fuel. Then `x`
from `s` with the fuel `F` gives the value of the first run and `s'` with the fuel `F - u` if
`u ≤ F`. It gives `S015` if `F < u`. Only `charge` and `measure` read the fuel, and `measure`
keeps only a difference. Nothing catches an error.

`flatten_budget` is the budget boundary of `flatten`. The tactic `ffollows` splits a goal as the
tactic `follows` of `Eval.Fuel` does.
-/
namespace Silicon.Source.Flatten.Fuel

open Eval

/-- The run with the fuel `F` agrees with the first run that used `u` units. -/
@[reducible] def Res (a : α) (s' : St) (u F : Nat) (r : Except Failure (α × St)) : Prop :=
  (u ≤ F → r = .ok (a, { s' with fuel := F - u })) ∧
    (F < u → ∃ p m, r = .error (.source ⟨.S015, p, m⟩))

/-- `x` follows itself with each fuel (see the module doc). -/
def FFollows (x : FM α) : Prop :=
  ∀ s a s', x s = .ok (a, s') → s'.fuel ≤ s.fuel ∧ ∀ F,
    Res a s' (s.fuel - s'.fuel) F (x { s with fuel := F })

theorem bind_apply (x : FM α) (f : α → FM β) (s : St) :
    (x >>= f) s = match x s with
      | .ok (a, s') => f a s'
      | .error e => .error e := by
  show (x s >>= fun p => f p.1 p.2) = _
  cases x s <;> rfl

theorem charge_apply (p : Pos) (k : Nat) (s : St) :
    charge p k s = if k ≤ s.fuel then .ok ((), { s with fuel := s.fuel - k })
      else .error (.source ⟨.S015, p, s!"the fuel cannot pay {intText k} unit(s) of the " ++
        s!"lowering; {intText s.fuel} remain"⟩) := by
  unfold charge
  rw [bind_apply]
  show (if k ≤ s.fuel then _ else _ : FM Unit) s = _
  by_cases h : k ≤ s.fuel <;> simp only [h, ↓reduceIte] <;> rfl

theorem measure_apply (x : FM α) (s : St) :
    measure x s = match x s with
      | .ok (a, s') => .ok ((a, s.fuel - s'.fuel), s')
      | .error e => .error e := by
  unfold measure
  rw [bind_apply]
  show (x >>= fun a => _) s = _
  rw [bind_apply]
  rcases x s with _ | ⟨a, s'⟩ <;> rfl

namespace FFollows

theorem bind {x : FM α} {f : α → FM β} (hx : FFollows x) (hf : ∀ a, FFollows (f a)) :
    FFollows (x >>= f) := by
  intro s b s'' h
  rw [bind_apply] at h
  split at h
  next a s' hxs =>
    obtain ⟨m1, k1⟩ := hx s a s' hxs
    obtain ⟨m2, k2⟩ := hf a s' b s'' h
    refine ⟨Nat.le_trans m2 m1, fun F => ?_⟩
    rw [bind_apply]
    by_cases h1 : s.fuel - s'.fuel ≤ F
    · rw [(k1 F).1 h1]
      have e2 := k2 (F - (s.fuel - s'.fuel))
      constructor
      · intro h2
        simp only []
        rw [e2.1 (by omega)]
        congr 3; omega
      · intro h2
        simp only []
        exact e2.2 (by omega)
    · obtain ⟨p, m, he⟩ := (k1 F).2 (by omega)
      rw [he]
      exact ⟨fun _ => by omega, fun _ => ⟨p, m, rfl⟩⟩
  next => cases h

/-- A computation that neither reads nor changes the fuel follows itself. -/
theorem of_frame {x : FM α}
    (h : ∀ s a s', x s = .ok (a, s') →
      s'.fuel = s.fuel ∧ ∀ F, x { s with fuel := F } = .ok (a, { s' with fuel := F })) :
    FFollows x := by
  intro s a s' hx
  obtain ⟨e, k⟩ := h s a s' hx
  refine ⟨Nat.le_of_eq e, fun F => ⟨fun _ => ?_, fun hF => by omega⟩⟩
  rw [k F]; simp [e]

theorem pure (a : α) : FFollows (Pure.pure a : FM α) :=
  of_frame fun _ _ _ h => by cases h; exact ⟨rfl, fun _ => rfl⟩

theorem throw (e : Failure) : FFollows (MonadExcept.throw e : FM α) :=
  fun _ _ _ h => by cases h

theorem defect (msg : String) : FFollows (Flatten.defect msg : FM α) :=
  fun _ _ _ h => by cases h

theorem charge (p : Pos) (k : Nat) : FFollows (Flatten.charge p k) := by
  intro s a s' h
  rw [charge_apply] at h
  split at h
  next hk =>
    cases h
    refine ⟨Nat.sub_le _ _, fun F => ⟨fun hF => ?_, fun hF => ?_⟩⟩ <;> dsimp only at hF ⊢
    · rw [charge_apply]
      simp only [show k ≤ F by omega, ↓reduceIte]
      congr 3; omega
    · rw [charge_apply]
      simp only [show ¬k ≤ F by omega, ↓reduceIte]
      exact ⟨_, _, rfl⟩
  · cases h

theorem get_bind {k : St → FM α} (h : ∀ s, FFollows (k s))
    (hk : ∀ s F, k { s with fuel := F } = k s) : FFollows (get >>= k) := by
  intro s a s' hx
  rw [bind_apply] at hx
  obtain ⟨m, k1⟩ := h s s a s' hx
  refine ⟨m, fun F => ?_⟩
  rw [bind_apply]
  show Res _ _ _ _ ((k { s with fuel := F }) { s with fuel := F })
  rw [hk]
  exact k1 F

theorem modify (f : St → St) (hf : ∀ s F, f { s with fuel := F } = { f s with fuel := F })
    (hf' : ∀ s, (f s).fuel = s.fuel) : FFollows (_root_.modify f : FM PUnit) :=
  of_frame fun s a s' h => by
    cases h; exact ⟨hf' s, fun F => by show Except.ok ((), f { s with fuel := F }) = _; rw [hf]⟩

/-- The difference of the fuel is the same in each run that succeeds. -/
theorem measure {x : FM α} (h : FFollows x) : FFollows (Flatten.measure x) := by
  intro s r s'' hx
  rw [measure_apply] at hx
  split at hx
  next a s' hxs =>
    cases hx
    obtain ⟨m, k⟩ := h s _ _ hxs
    refine ⟨m, fun F => ⟨fun hu => ?_, fun hu => ?_⟩⟩
    · rw [measure_apply, (k F).1 hu]
      dsimp only
      congr 3; omega
    · obtain ⟨p, m, he⟩ := (k F).2 hu
      exact ⟨p, m, by rw [measure_apply, he]⟩
  next => cases hx

theorem forIn {f : β → γ → FM (ForInStep γ)} (h : ∀ b a, FFollows (f b a)) :
    ∀ (xs : List β) (init : γ), FFollows (ForIn.forIn xs init f)
  | [], _ => pure _
  | x :: xs, init => by
    rw [List.forIn_cons]
    refine bind (h x init) fun r => ?_
    cases r with
    | done a => exact pure a
    | yield a => exact forIn h xs a

theorem forInArray {f : β → γ → FM (ForInStep γ)} (h : ∀ b a, FFollows (f b a))
    (xs : Array β) (init : γ) : FFollows (ForIn.forIn xs init f) := by
  rw [← Array.forIn_toList]
  exact forIn h _ init

theorem forInRange {f : Nat → γ → FM (ForInStep γ)} (h : ∀ b a, FFollows (f b a))
    (r : Std.Legacy.Range) (init : γ) : FFollows (ForIn.forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn h _ init

end FFollows

attribute [irreducible] FFollows

/--
Splits a goal `FFollows x` along the structure of `x`. The given facts and the local
hypotheses give the facts of the calls.
-/
syntax "ffollows" (" [" term,* "]")? : tactic

/-- Applies the first of the given facts that fits the goal. -/
syntax "ffollows_by" " [" term,* "]" : tactic

macro_rules
  | `(tactic| ffollows_by []) => `(tactic| fail "no fact fits")
  | `(tactic| ffollows_by [$t:term]) => `(tactic| with_reducible apply $t)
  | `(tactic| ffollows_by [$t:term, $ts:term,*]) =>
    `(tactic| first | with_reducible apply $t | ffollows_by [$ts,*])

macro_rules | `(tactic| ffollows) => `(tactic| ffollows [])

macro_rules | `(tactic| ffollows [$ts,*]) => `(tactic| repeat' (first
  | intro _
  | with_reducible exact FFollows.pure _
  | with_reducible exact FFollows.charge _ _
  | with_reducible exact FFollows.defect _
  | with_reducible exact FFollows.throw _
  | (with_reducible apply FFollows.modify <;> intros <;> rfl)
  | (with_reducible apply FFollows.get_bind; case hk => intros; rfl)
  | with_reducible apply FFollows.measure
  | with_reducible apply FFollows.forInArray
  | with_reducible apply FFollows.forInRange
  | with_reducible apply FFollows.forIn
  | ffollows_by [$ts,*]
  | split
  | with_reducible apply FFollows.bind
  | dsimp only))

/-! Each function of the lowering follows itself. -/

theorem pathText_f (pos : Pos) (p : Names.Path) : FFollows (pathText pos p) := by
  unfold pathText; ffollows

theorem nameText_f (pos : Pos) (p : Names.Name) : FFollows (nameText pos p) := by
  unfold nameText; ffollows

theorem constOf_f (p : Core.Pos) (v : Value) : FFollows (constOf p v) := by
  unfold constOf; split <;> ffollows

theorem bindTemp_f (pos : Pos) (target : Names.Path) (w : Nat) (opPos : Pos) (e : Core.Expr) :
    FFollows (bindTemp pos target w opPos e) := by
  unfold bindTemp; ffollows [pathText_f]

theorem tempRef_f (pos : Pos) (path : Names.Path) : FFollows (tempRef pos path) := by
  unfold tempRef; ffollows [pathText_f]

theorem twice_f (pos : Pos) (target : Names.Path) (w : Nat) (opPos : Pos) (lo : Low) :
    FFollows (twice pos target w opPos lo) := by
  unfold twice; ffollows [bindTemp_f, tempRef_f]

theorem deep_f (pos : Pos) (target : Names.Path) (w : Nat) (root : Bool) (lo : Low) :
    FFollows (deep pos target w root lo) := by
  unfold deep; ffollows [bindTemp_f, tempRef_f]

theorem lower_f (target : Names.Path) :
    ∀ n (h : Hw), sizeOf h ≤ n → ∀ root, FFollows (lower target root h)
  | 0, .node .., hs => by simp at hs
  | n + 1, .node p t sz op args, hs => by
    have ih := lower_f target n
    -- A link of a spine and the bottom of a spine are below a node within the bound.
    have ihB : ∀ (B : Nat) (x : { x : Hw // sizeOf x < B }), B ≤ n + 1 → ∀ r,
        FFollows (lower target r x.1) := fun B x hB r => ih x.1 (by have := x.2; omega) r
    intro root
    rw [lower.eq_def]
    ffollows [ihB, ih, twice_f, deep_f, bindTemp_f, tempRef_f, pathText_f, nameText_f,
      constOf_f]
    all_goals simp_all only [Hw.node.injEq, Hw.node.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega

theorem value_f (target : Names.Path) (h : Hw) : FFollows (value target h) := by
  unfold value; ffollows [lower_f target _ h (Nat.le_refl _)]

theorem leafHw_f (pos : Pos) (t : Ty) (a : Option Agg) : FFollows (leafHw pos t a) := by
  unfold leafHw; split <;> ffollows

theorem leafConst_f (p : Core.Pos) (a : Option Agg) : FFollows (leafConst p a) := by
  unfold leafConst; split <;> ffollows [constOf_f]

theorem noFields_f (b : β) (t : Ty) : FFollows (noFields b t) := by
  unfold noFields; ffollows

theorem domainRef_f (pos : Pos) (n : Names.Name) : FFollows (domainRef pos n) := by
  unfold domainRef; ffollows [nameText_f]

theorem domainConns_f (pos : Pos) (c d : Option String) : FFollows (domainConns pos c d) := by
  unfold domainConns; ffollows [nameText_f, domainRef_f]

/-- The walk over the leaves follows itself, by induction on its bound. -/
theorem foldLeaves_f (fs : Layout.Fields) (sub : α → Names.Field → Nat → Ty → α)
    {f : β → Layout.Leaf → α → FM β} {bad : β → Ty → FM β} (h : ∀ b l x, FFollows (f b l x))
    (hb : ∀ b t, FFollows (bad b t)) :
    ∀ d p t x b, FFollows (Layout.foldLeaves fs sub f bad d p t x b)
  | 0, _, _, _, _ => by unfold Layout.foldLeaves; ffollows
  | d + 1, p, t, x, b => by
    have ih := foldLeaves_f fs sub h hb d
    unfold Layout.foldLeaves
    ffollows [ih, h, hb]

theorem foldPort_f (fs : Layout.Fields) (q : Elab.PortDecl) (b : β) {f : β → Layout.Leaf → FM β}
    {bad : β → Ty → FM β} (h : ∀ b l, FFollows (f b l)) (hb : ∀ b t, FFollows (bad b t)) :
    FFollows (Layout.foldPort fs q b f bad) := by
  unfold Layout.foldPort; exact foldLeaves_f fs _ (fun b l _ => h b l) hb _ _ _ _ _

theorem nameRef_f (pos : Pos) (path : Names.Path) : FFollows (nameRef pos path) := by
  unfold nameRef; ffollows [pathText_f]

theorem memReg_f (pos : Pos) (d : String) (path : Names.Path) (w : Nat) :
    FFollows (memReg pos d path w) := by
  unfold memReg; ffollows [pathText_f, nameText_f, domainRef_f]

theorem memLet_f (pos : Pos) (path : Names.Path) (t : Ty) (a : Agg) :
    FFollows (memLet pos path t a) := by
  unfold memLet; ffollows [pathText_f, value_f, leafHw_f]

theorem memData_f (fs : Layout.Fields) (pos : Pos) (m : Names.Path) (t : Ty) (a : Agg) :
    FFollows (memData fs pos m t a) := by
  unfold memData
  ffollows [foldLeaves_f, lower_f _ _ _ (Nat.le_refl _), deep_f, leafHw_f, noFields_f]

theorem lowerMem_f (fs : Layout.Fields) (d : String) (body : Array Core.Stmt) (m : Mem) :
    FFollows (lowerMem fs d body m) := by
  unfold lowerMem
  ffollows [pathText_f, nameText_f, memReg_f, memLet_f, nameRef_f, memData_f, domainRef_f,
    lower_f _ _ _ (Nat.le_refl _), leafHw_f]

theorem lowerInst_f (fs : Layout.Fields) (i : Elab.Inst) : FFollows (lowerInst fs i) := by
  unfold lowerInst
  ffollows [nameText_f, pathText_f, domainRef_f, domainConns_f, value_f, constOf_f, foldPort_f,
    foldLeaves_f, leafHw_f, leafConst_f, noFields_f, lowerMem_f]

theorem lowerDesign_f (pos : Pos) (d : Elab.Design) : FFollows (lowerDesign pos d) := by
  unfold lowerDesign; ffollows [nameText_f, lowerInst_f]

theorem flatten_apply (fuel : Nat) (pos : Pos) (d : Elab.Design) :
    flatten fuel pos d = match lowerDesign pos d { fuel } with
      | .ok (l, s) => .ok (l, fuel - s.fuel)
      | .error e => .error e := by
  unfold flatten
  show (lowerDesign pos d { fuel } >>= fun x => Pure.pure (x.1, fuel - x.2.fuel)) = _
  cases lowerDesign pos d { fuel } <;> rfl

/--
The budget boundary of `flatten`. If the lowering uses `u` units, each fuel from `u` gives the
same lowered design and units, and each fuel below `u` gives `S015`.
-/
theorem flatten_budget {fuel : Nat} {pos : Pos} {d : Elab.Design} {l : Lowered} {u : Nat}
    (h : flatten fuel pos d = .ok (l, u)) (F : Nat) :
    (u ≤ F → flatten F pos d = .ok (l, u)) ∧
    (F < u → ∃ p m, flatten F pos d = .error (.source ⟨.S015, p, m⟩)) := by
  rw [flatten_apply] at h
  split at h
  next l' s' hx =>
    cases h
    have hf := lowerDesign_f pos d
    unfold FFollows at hf
    obtain ⟨_, k⟩ := hf _ _ _ hx
    have r := k F
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · rw [flatten_apply]
      show (match lowerDesign pos d { ({ fuel } : St) with fuel := F } with
        | .ok (l, s) => Except.ok (l, F - s.fuel) | .error e => Except.error e) = _
      rw [r.1 hu]
      dsimp only at hu ⊢
      congr 2
      omega
    · obtain ⟨p, m, he⟩ := r.2 hu
      refine ⟨p, m, ?_⟩
      rw [flatten_apply]
      show (match lowerDesign pos d { ({ fuel } : St) with fuel := F } with
        | .ok (l, s) => Except.ok (l, F - s.fuel) | .error e => Except.error e) = _
      rw [he]
  next => cases h

end Silicon.Source.Flatten.Fuel
