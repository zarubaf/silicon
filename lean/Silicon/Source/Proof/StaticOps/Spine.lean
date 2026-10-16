-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Flatten

/-!
The run of `Flatten.lower` on a left spine of binary nodes over a constant. The rows of section
7.4 that walk an aggregate by leaf make such a spine: the chain of `and` nodes of `==` and the
`xor` node of `!=`. `lower` takes the spine in two loops. The first loop walks down the left
operands and collects the links. The second loop lowers the right operand of each link,
innermost first. `runs_chain` states the result of both loops for each spine whose height stays
below 64, so the height rule binds no temporary.

The statements use `Ok`, a predicate on the run of an `FM` action from one state. A proof thus
follows the `do` block of `lower` one bind at a time.
-/
namespace Silicon.Source.StaticOps.Spine

open Eval Flatten

/-! `x` runs from `st` without an error, and its result and its end state meet `Q`. -/
def Ok (x : FM α) (st : Flatten.St) (Q : α → Flatten.St → Prop) : Prop :=
  ∃ a st', x.run st = .ok (a, st') ∧ Q a st'

theorem ok_pure {a : α} {st Q} (h : Q a st) : Ok (pure a) st Q := ⟨a, st, rfl, h⟩

theorem ok_bind {x : FM α} {k : α → FM β} {st Q}
    (h : Ok x st fun a st' => Ok (k a) st' Q) : Ok (x >>= k) st Q := by
  obtain ⟨a, st', hx, b, st'', hk, hq⟩ := h
  exact ⟨b, st'', by rw [StateT.run_bind, hx]; exact hk, hq⟩

theorem ok_mono {x : FM α} {st} {P Q : α → Flatten.St → Prop} (h : Ok x st P)
    (hpq : ∀ a st', P a st' → Q a st') : Ok x st Q := by
  obtain ⟨a, st', hx, hp⟩ := h
  exact ⟨a, st', hx, hpq _ _ hp⟩

theorem ok_charge {p n st Q} (hn : n ≤ st.fuel) (h : Q () { st with fuel := st.fuel - n }) :
    Ok (Flatten.charge p n) st Q :=
  ⟨(), _, by simp [Flatten.charge, hn]; rfl, h⟩

/--
`lower` runs `h` with `n` units of fuel from each state with enough fuel. It gives the
expression `e` with a height of at most `H`, and it changes only the fuel.
-/
def Runs (h : Hw) (n : Nat) (e : Core.Expr) (H : Nat) : Prop :=
  ∀ target root (st : Flatten.St), n ≤ st.fuel →
    Ok (lower target root h) st fun lo st' =>
      lo.expr = e ∧ lo.height ≤ H ∧ st' = { st with fuel := st.fuel - n }

theorem ok_deep {p target w root} {lo : Low} {st Q} (h : lo.height < 64) (hq : Q lo st) :
    Ok (deep p target w root lo) st Q := by
  refine ⟨lo, st, ?_, hq⟩
  have : ¬ 64 ≤ lo.height := by omega
  cases root <;> simp [deep, h] <;> rfl

theorem runs_lit (p : Pos) (t : Ty) (sz : Nat) (v : Value) (c : Core.Expr)
    (hc : ∀ st, (constOf (cpos p) v).run st = .ok (c, st)) :
    Runs (Hw.node p t sz (.lit v) []) 1 c 1 := by
  intro target root st hf
  rw [lower.eq_def]
  simp only
  refine ok_bind (ok_charge hf (ok_bind ⟨c, _, hc _, ok_bind (ok_pure ?_)⟩))
  exact ok_deep (by simp) ⟨rfl, Nat.le_refl _, rfl⟩

/-! A link of a left spine: a binary node, its core operation, and the run of its right operand. -/
structure Lk where
  pos : Pos
  ty : Ty
  op : BinOp
  core : Core.BinOp ⊕ Core.Pred
  right : Hw
  fuel : Nat
  expr : Core.Expr

/--
The core operation of the link does not depend on the sign, and its right operand runs with a
height of at most `a`.
-/
def Lk.Good (a : Nat) (l : Lk) : Prop :=
  (∀ sg, binOp l.op sg = some l.core) ∧ Runs l.right l.fuel l.expr a

/-! The spine over `base`, with its top link first. -/
def chain (base : Hw) : List Lk → Hw
  | [] => base
  | l :: ls => Hw.mk l.pos l.ty (.bin l.op) [chain base ls, l.right]

/-! The core expression of the spine, with `eb` for its base. -/
def chainExpr (eb : Core.Expr) : List Lk → Core.Expr
  | [] => eb
  | l :: ls => binExpr (cpos l.pos) l.core (chainExpr eb ls) l.expr

/-! The fuel of the spine: 1 for the base, and 1 plus the fuel of its right operand per link. -/
def chainFuel : List Lk → Nat
  | [] => 1
  | l :: ls => 1 + l.fuel + chainFuel ls

/-! The data of a link of `lower` and of a link here, without the size bound of `lower`. -/
def Link.view {b} (l : Link b) : Pos × Ty × (Core.BinOp ⊕ Core.Pred) × Hw :=
  (l.pos, l.ty, l.op, l.right.1)

def Lk.view (l : Lk) : Pos × Ty × (Core.BinOp ⊕ Core.Pred) × Hw := (l.pos, l.ty, l.core, l.right)

theorem size_chain (base : Hw) : ∀ R : List Lk, R.length ≤ (chain base R).size
  | [] => Nat.zero_le _
  | l :: R => by
    have := size_chain base R
    simp only [chain, Hw.mk, Hw.size.eq_1, Op.size, List.map, List.sum_cons, List.sum_nil,
      List.length_cons]
    omega

theorem fuel_sub (st : Flatten.St) (a b : Nat) :
    { { st with fuel := st.fuel - a } with fuel := st.fuel - a - b } =
      { st with fuel := st.fuel - (a + b) } := by
  simp [Nat.sub_sub]

/-! The first loop of `lower` walks down the spine and collects its links. -/
theorem ok_loop1 {b : Nat} {γ : Type} (mk : List (Link b) → {x : Hw // sizeOf x < b} → γ)
    (base : Hw) (f : Nat → γ → FM (ForInStep γ))
    (hbin : ∀ i ls q u s o l r j (hc : sizeOf (Hw.node q u s (.bin o) [l, r]) < b),
      binOp o (signed l.ty) = some j → ∃ hl hr,
        f i (mk ls ⟨.node q u s (.bin o) [l, r], hc⟩) =
          (do Flatten.charge q 1; pure (.yield (mk (⟨q, u, j, ⟨r, hr⟩⟩ :: ls) ⟨l, hl⟩))))
    (hbase : ∀ i ls (x : {x : Hw // sizeOf x < b}), x.1 = base →
      f i (mk ls x) = pure (.done (mk ls x))) :
    ∀ (R : List Lk) (idx : List Nat) ls hc (st : Flatten.St) (Q : γ → Flatten.St → Prop),
      (∀ l ∈ R, ∀ sg, binOp l.op sg = some l.core) → R.length ≤ idx.length →
      R.length ≤ st.fuel →
      (∀ ls' hb, ls'.map Link.view = R.reverse.map Lk.view ++ ls.map Link.view →
        Q (mk ls' ⟨base, hb⟩) { st with fuel := st.fuel - R.length }) →
      Ok (forIn idx (mk ls ⟨chain base R, hc⟩) f) st Q
  | [], idx, ls, hc, st, Q, _, _, _, hq => by
    have hst : st = { st with fuel := st.fuel - 0 } := by simp
    cases idx with
    | nil => exact ok_pure (hst ▸ hq ls hc (by simp))
    | cons i is =>
      rw [List.forIn_cons]
      refine ok_bind ?_
      rw [hbase i ls _ rfl]
      exact ok_pure (ok_pure (hst ▸ hq ls hc (by simp)))
  | l :: R, idx, ls, hc, st, Q, hR, hlen, hf, hq => by
    obtain ⟨i, is, rfl⟩ : ∃ i is, idx = i :: is := by
      cases idx with
      | nil => simp at hlen
      | cons i is => exact ⟨i, is, rfl⟩
    rw [List.forIn_cons]
    refine ok_bind ?_
    obtain ⟨hl, hr, hfe⟩ := hbin i ls l.pos l.ty _ l.op (chain base R) l.right l.core hc
      (hR l (by simp) _)
    simp only [chain, Hw.mk] at hfe ⊢
    rw [hfe]
    refine ok_bind (ok_charge (by simp at hf; omega) (ok_pure ?_))
    refine ok_loop1 mk base f hbin hbase R is _ hl _ Q (fun l h => hR l (by simp [h]))
      (by simp at hlen; omega) (by simp at hf ⊢; omega) ?_
    intro ls' hb hv
    rw [fuel_sub]
    have := hq ls' hb (by simp [hv, Link.view, Lk.view])
    simpa [Nat.add_comm] using this

theorem Runs.ok {h n e H} (hr : Runs h n e H) {target root st} {Q : Low → Flatten.St → Prop}
    (hf : n ≤ st.fuel)
    (hq : ∀ lo, lo.expr = e → lo.height ≤ H → Q lo { st with fuel := st.fuel - n }) :
    Ok (lower target root h) st Q :=
  ok_mono (hr target root st hf) fun lo _ ⟨he, hh, hs⟩ => hs ▸ hq lo he hh

/-! The second loop of `lower` lowers the right operand of each link, innermost first. -/
theorem ok_loop2 {b : Nat} (target : Names.Path) (g : Link b → Low → FM (ForInStep Low))
    (hg : ∀ l lo, g l lo = (do
      let r ← lower target false l.right.1
      let lo' ← deep l.pos target (width l.ty) false
        ⟨binExpr (cpos l.pos) l.op lo.expr r.expr, none, max lo.height r.height + 1⟩
      pure (.yield lo'))) :
    ∀ (a : Nat) (R : List Lk) (ls : List (Link b)) (lo : Low) (h : Nat) (st : Flatten.St)
      (Q : Low → Flatten.St → Prop),
      ls.map Link.view = R.map Lk.view → (∀ l ∈ R, l.Good a) → lo.height ≤ h → a ≤ h →
      h + R.length < 64 → (R.map Lk.fuel).sum ≤ st.fuel →
      (∀ lo', lo'.expr = R.foldl (fun e l => binExpr (cpos l.pos) l.core e l.expr) lo.expr →
        lo'.height ≤ h + R.length →
        Q lo' { st with fuel := st.fuel - (R.map Lk.fuel).sum }) →
      Ok (forIn ls lo g) st Q
  | _, [], [], lo, h, st, Q, _, _, hl, _, _, _, hq => by
    have hst : st = { st with fuel := st.fuel - 0 } := by simp
    exact ok_pure (hst ▸ hq lo rfl (by simpa using hl))
  | _, [], _ :: _, _, _, _, _, hv, _, _, _, _, _, _ => by simp at hv
  | _, _ :: _, [], _, _, _, _, hv, _, _, _, _, _, _ => by simp at hv
  | a, l :: R, k :: ks, lo, h, st, Q, hv, hR, hl, h2, hh, hf, hq => by
    simp only [List.map_cons, List.cons.injEq, Link.view, Lk.view, Prod.mk.injEq] at hv
    obtain ⟨⟨hp, ht, ho, hr⟩, hv⟩ := hv
    obtain ⟨_, hrun⟩ := hR l (by simp)
    simp only [List.map_cons, List.sum_cons] at hf
    simp only [List.length_cons] at hh
    rw [List.forIn_cons, hg, hr]
    refine ok_bind (ok_bind (hrun.ok (by omega) fun r he hrh => ?_))
    refine ok_bind (ok_deep (by simp; omega) (ok_pure ?_))
    refine ok_loop2 target g hg a R ks _ (h + 1) _ Q hv (fun l h => hR l (by simp [h]))
      (by simp; omega) (by omega) (by omega) (by simp; omega) ?_
    intro lo' he' hh'
    rw [fuel_sub]
    refine hq lo' ?_ (by simp; omega)
    simpa [hp, ht, ho, he] using he'

theorem Runs.mono {h n e H H'} (hr : Runs h n e H) (hH : H ≤ H') : Runs h n e H' :=
  fun target root st hf => ok_mono (hr target root st hf) fun _ _ ⟨he, hh, hs⟩ =>
    ⟨he, Nat.le_trans hh hH, hs⟩

theorem Lk.Good.mono {a b : Nat} {l : Lk} (h : l.Good a) (hab : a ≤ b) : l.Good b :=
  ⟨h.1, h.2.mono hab⟩

theorem chain_append (base : Hw) (l : Lk) : ∀ R : List Lk,
    chain base (R ++ [l]) = chain (Hw.mk l.pos l.ty (.bin l.op) [base, l.right]) R
  | [] => rfl
  | k :: R => by simp [chain, chain_append base l R]

/-! A left fold of binary nodes over `base` is the spine of the reversed links. -/
theorem chain_foldl : ∀ (ls : List Lk) (base : Hw),
    ls.foldl (fun e l => Hw.mk l.pos l.ty (.bin l.op) [e, l.right]) base = chain base ls.reverse
  | [], _ => rfl
  | l :: ls, base => by simp [chain_foldl ls, chain_append]

theorem chainExpr_foldl (eb : Core.Expr) : ∀ R : List Lk,
    chainExpr eb R = R.reverse.foldl (fun e l => binExpr (cpos l.pos) l.core e l.expr) eb
  | [] => rfl
  | l :: R => by simp [chainExpr, chainExpr_foldl eb R]

theorem chainFuel_eq : ∀ R : List Lk, chainFuel R = 1 + R.length + (R.map Lk.fuel).sum
  | [] => rfl
  | l :: R => by simp [chainFuel, chainFuel_eq R]; omega

theorem Lk.Good.op {a} {l : Lk} (h : l.Good a) : l.op ≠ .shl ∧ l.op ≠ .shr := by
  have := h.1 false
  constructor <;> intro e <;> simp [e, binOp] at this

/--
`lower` emits the spine `chain base R` as `chainExpr eb R`. The base is a constant, so the first
loop of `lower` stops there. Each right operand has a height of at most `a`, so the spine has a
height of at most `a` plus its length. This stays below 64, so no node binds.
-/
theorem runs_chain {pb tb sb v eb} (hb : Runs (Hw.node pb tb sb (.lit v) []) 1 eb 1) (a : Nat)
    (ha : 1 ≤ a) : ∀ R : List Lk, (∀ l ∈ R, l.Good a) → a + R.length < 64 →
      Runs (chain (Hw.node pb tb sb (.lit v) []) R) (chainFuel R) (chainExpr eb R)
        (a + R.length)
  | [], _, _ => hb.mono (by simp [ha])
  | l :: R, hR, hlen => by
    intro target root st hf
    have hl := hR l (by simp)
    have hR' : ∀ k ∈ R, k.Good a := fun k h => hR k (by simp [h])
    obtain ⟨hs1, hs2⟩ := hl.op
    have h1 : (l.op == BinOp.shl) = false := by revert hs1; cases l.op <;> decide
    have h2 : (l.op == BinOp.shr) = false := by revert hs2; cases l.op <;> decide
    simp only [chain, Hw.mk]
    rw [lower.eq_def]
    simp only [h1, h2, Bool.or_self, Bool.false_eq_true, ite_false, hl.1]
    have hfl := hf
    simp only [chainFuel, chainFuel_eq] at hfl
    simp only [List.length_cons] at hlen
    refine ok_bind (ok_charge (by omega) ?_)
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    refine ok_bind (ok_loop1 (fun ls x => (ls, x)) _ _ ?_ ?_ R _ [] _ _ _ (fun k h => (hR' k h).1)
      ?_ (by simp; omega) ?_)
    · intro i ls q u s o l r j hc hj
      refine ⟨?_, ?_, ?_⟩
      · simp only [Hw.node.sizeOf_spec, List.cons.sizeOf_spec] at hc ⊢; omega
      · simp only [Hw.node.sizeOf_spec, List.cons.sizeOf_spec] at hc ⊢; omega
      · simp only [hj]
    · intro i ls x hx
      obtain ⟨x, hx'⟩ := x
      simp only at hx
      subst hx
      rfl
    · have := size_chain (Hw.node pb tb sb (.lit v) []) R
      simp [Op.size]
      omega
    · intro ls hbx hv
      simp only [List.map_nil, List.append_nil] at hv
      refine ok_bind (hb.ok (by simp; omega) fun lo he hh => ?_)
      refine ok_bind (ok_loop2 target _ (fun _ _ => rfl) a R.reverse ls lo a _ _ hv
        (fun k h => hR' k (by simpa using h)) (by omega) (Nat.le_refl _) (by simp; omega)
        (by simp; omega) fun lo' he' hh' => ?_)
      refine ok_bind (hl.2.ok (by simp; omega) fun r her hrh => ?_)
      refine ok_bind (ok_pure (ok_deep (by simp at hh' ⊢; omega) ⟨?_, ?_, ?_⟩))
      · simp [chainExpr, he', her, he, chainExpr_foldl]
      · simp at hh' ⊢; omega
      · simp [chainFuel_eq]; omega

end Silicon.Source.StaticOps.Spine
