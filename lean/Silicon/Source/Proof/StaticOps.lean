-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Flatten
import Silicon.Core.Semantics.Expression

/-!
The finite static operations of the evaluator agree with the core (section 7.4 of the front-end
spec). Each statement names a core row `e` with constant leaves and makes two claims:

- The static operation gives the value of `e`. `evalExpr` evaluates `e` in each context.
- `Flatten.lower` emits the erasure of `e` for the hardware node of the operation. Its
  operands are the literals that `Eval.lit` makes. `lower` runs in a state monad with the fuel.
  The claim is thus about its run from each state with enough fuel.

The evaluator runs `&&` and `||` by a short circuit in `Eval.eval`, not by `Eval.binary`. Their
statement thus gives the static result as `a && b` and `a || b`.

A shift count is static: an `Int` or a `UInt`. `Eval.hwShift` makes an `Int` literal of both,
and `Flatten.lower` takes that literal as a constant. A `resize` row needs `1 ≤ w` for a sign
extension, and a result of at most 65536 bits for an extension. `Eval.family` gives both bounds
to each finite type.
-/
namespace Silicon.Source.StaticOps

open Eval Flatten
open Core.Semantics (Valuation Memories)

local notation "ev" => Core.Semantics.evalExpr

/-! The typed core expression of the width `w`. -/
local notation "Ex" ctx:max w:max => Core.Typed.Expr ctx (Core.Ty.bits w)

/-! The finite type of a signedness and a width. -/
def finiteTy (s : Bool) (w : Nat) : Ty := if s then .sint w else .uint w

/-! A literal node, as `Eval.lit` and `Eval.hwShift` make it. -/
def litHw (p : Pos) (t : Ty) (v : Value) : Hw := Hw.mk p t (.lit v) []

/-! A literal node of a finite value. -/
def leaf (p : Pos) (s : Bool) (w : Nat) (x : BitVec w) : Hw := litHw p (finiteTy s w) (finite s w x)

/-!
`lower` emits the row `e` for the node `h`. Each run from a state with at least `n` units of
fuel succeeds with the expression `e`. This holds for each target and each root flag.
-/
def Lowers (h : Hw) (n : Nat) (e : Core.Expr) : Prop :=
  ∀ (target : Names.Path) (root : Bool) (st : Flatten.St), n ≤ st.fuel →
    ∃ lo st', (lower target root h).run st = .ok (lo, st') ∧ lo.expr = e

/-! A static operation and its row: each operand, the step, and the result. -/

/-- `+%`, `-%`, `*%`, `&`, `|`, and `^`: the row `bin c a b`. -/
def BinAgrees : Prop :=
  ∀ (op : BinOp) (c : Core.BinOp) (hk : c ≠ .concat) (s : Bool) (w : Nat) (x y : BitVec w)
    (st : Step) (v : Value), coreOp op = some c →
    binary op (finite s w x) (finite s w y) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .bin q c hk (.const q w x.toNat) (.const q w y.toNat)
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.bin op) [leaf p s w x, leaf p s w y]) 3
        (e (cpos p)).erase

/-- `==`, `!=`, `<`, `<=`, `>`, and `>=` on finite integers: the row `icmp k a b`. -/
def CmpAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (k : Core.Pred) (w : Nat) (x y : BitVec w) (st : Step)
    (v : Value), binOp op s = some (.inr k) →
    binary op (finite s w x) (finite s w y) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .icmp q k (.const q w x.toNat) (.const q w y.toNat)
    (∀ q, ∃ b, v = .bool b ∧ ev vals mems (e q) = BitVec.ofBool b) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin op) [leaf p s w x, leaf p s w y]) 3 (e (cpos p)).erase

/-! The constant of a Boolean. -/
local notation "bit" b:max => (if b then 1 else 0 : Nat)

/-- `==` and `!=` on `Bool`: the row `icmp k a b`. -/
def BoolCmpAgrees : Prop :=
  ∀ (op : BinOp) (k : Core.Pred) (a b : Bool) (st : Step) (v : Value),
    (op = .eq ∨ op = .ne) → binOp op false = some (.inr k) →
    binary op (.bool a) (.bool b) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .icmp q k (.const q 1 (bit a)) (.const q 1 (bit b))
    (∀ q, ∃ r, v = .bool r ∧ ev vals mems (e q) = BitVec.ofBool r) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin op) [litHw p .bool (.bool a), litHw p .bool (.bool b)])
        3 (e (cpos p)).erase

/-- `&&` and `||` on `Bool`: the row `bin c a b`. -/
def LogicAgrees : Prop :=
  ∀ (op : BinOp) (c : Core.BinOp) (hk : c ≠ .concat) (a b : Bool),
    (op = .land ∨ op = .lor) → binOp op false = some (.inl c) →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .bin q c hk (.const q 1 (bit a)) (.const q 1 (bit b))
    (∀ q, ev vals mems (e q) = BitVec.ofBool (if op = .land then a && b else a || b)) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin op) [litHw p .bool (.bool a), litHw p .bool (.bool b)])
        3 (e (cpos p)).erase

/-- `~`: the row `not a`. -/
def InvAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    unary .inv (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .un q .not (.const q w x.toNat)
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.un .inv) [leaf p s w x]) 2 (e (cpos p)).erase

/-- Unary `-`: the row `sub (const w 0) a`. -/
def NegAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    unary .neg (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w :=
      .bin q .sub (by decide) (.const q w 0) (.const q w x.toNat)
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.un .neg) [leaf p s w x]) 3 (e (cpos p)).erase

/-- `!` on `Bool`: the row `xor a (const 1 1)`. -/
def NotAgrees : Prop :=
  ∀ (b : Bool) (st : Step) (v : Value),
    unary .not (.bool b) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .bin q .xor (by decide) (.const q 1 (bit b)) (.const q 1 1)
    (∀ q, ∃ r, v = .bool r ∧ ev vals mems (e q) = BitVec.ofBool r) ∧
      ∀ p, Lowers (Hw.mk p .bool (.un .not) [litHw p .bool (.bool b)]) 3 (e (cpos p)).erase

/--
`<<` and `>>` with a static count `k`, an `Int` or a `UInt` operand `b`: the row
`c a (const w (min k w))`. `Eval.hwShift` makes the literal `Int` `k` of both counts.
-/
def ShiftAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (c : Core.BinOp) (hk : c ≠ .concat) (w : Nat) (x : BitVec w)
    (b : Value) (k : Nat) (st : Step) (v : Value), (op = .shl ∨ op = .shr) →
    c = (if op == .shl then .shl else if s then .shrs else .shru) →
    (b = .int k ∨ ∃ (u : Nat) (y : BitVec u), b = .uint u y ∧ k = y.toNat) →
    binary op (finite s w x) b = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .bin q c hk (.const q w x.toNat) (.const q w (min k w))
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.bin op) [leaf p s w x, litHw p .int (.int k)]) 3
        (e (cpos p)).erase

/-- `resize` to the same width: the row is the operand. -/
def ResizeSameAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    resize (finiteTy s w) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .const q w x.toNat
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) .resize [leaf p s w x]) 1 (e (cpos p)).erase

/-- `resize` to a smaller width `n`: the row `extract a 0 n`. -/
def ResizeTruncAgrees : Prop :=
  ∀ (s : Bool) (n w : Nat) (hn : n < w) (x : BitVec w) (st : Step) (v : Value),
    resize (finiteTy s n) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx n := .extract q (.const q w x.toNat) 0 n (by omega)
    (∀ q, v = finite s n (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s n) .resize [leaf p s w x]) 2 (e (cpos p)).erase

/-- `resize` of a `UInt` to a larger width `n`: the row `concat (const (n - w) 0) a`. -/
def ResizeZextAgrees : Prop :=
  ∀ (n w : Nat) (hn : w < n) (hb : n ≤ 65536) (x : BitVec w) (st : Step) (v : Value),
    resize (.uint n) (.uint w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx (n - w + w) :=
      .concat q (.const q (n - w) 0) (.const q w x.toNat) (by omega)
    (∀ q, v = .uint n ((ev vals mems (e q)).cast (by omega))) ∧
      ∀ p, Lowers (Hw.mk p (.uint n) .resize [leaf p false w x]) 3 (e (cpos p)).erase

/--
`resize` of an `SInt` to a larger width `n`: the row
`concat (replicate (extract a (w - 1) 1) (n - w)) a`. The row uses the constant `a` twice.
-/
def ResizeSextAgrees : Prop :=
  ∀ (n w : Nat) (h0 : 1 ≤ w) (hn : w < n) (hb : n ≤ 65536) (x : BitVec w) (st : Step)
    (v : Value),
    resize (.sint n) (.sint w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let a (q : Core.Pos) : Ex ctx w := .const q w x.toNat
    let e (q : Core.Pos) : Ex ctx (1 * (n - w) + w) :=
      .concat q (.replicate q (.extract q (a q) (w - 1) 1 (by omega)) (n - w) (by omega)) (a q)
        (by omega)
    (∀ q, v = .sint n ((ev vals mems (e q)).cast (by omega))) ∧
      ∀ p, Lowers (Hw.mk p (.sint n) .resize [leaf p true w x]) 5 (e (cpos p)).erase

/-- `reinterpret` keeps the width: the row is the operand. -/
def ReinterpretAgrees : Prop :=
  ∀ (s r : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    reinterpret (finiteTy r w) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .const q w x.toNat
    (∀ q, v = finite r w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy r w) .reinterpret [leaf p s w x]) 1 (e (cpos p)).erase

/-! Facts about the lift and the operands. -/

private theorem constOf_finite (p : Core.Pos) (s : Bool) (w : Nat) (x : BitVec w) :
    constOf p (finite s w x) = .const p w x.toNat := by
  cases s <;> rfl

private theorem finitePair_finite (s : Bool) (w : Nat) (x y : BitVec w) :
    finitePair (finite s w x) (finite s w y) = some (s, ⟨w, x, y⟩) := by
  cases s <;> simp [finite, finitePair]

private theorem natCast_lt_zero (k : Nat) : ((k : Int) < 0) = False :=
  eq_false (by omega)

private theorem ofBool_beq_one (b : Bool) : (BitVec.ofBool b == 1#1) = b := by
  cases b <;> rfl

/--
`lower` on a small node: it splits the fuel into the charge and a rest, then computes the run.
-/
syntax "lowers" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| lowers) => `(tactic| lowers [])
  | `(tactic| lowers [$ts,*]) => `(tactic| (
    intro target root st hf
    obtain ⟨fuel, temps, count⟩ := st
    obtain ⟨rest, hrest⟩ := Nat.exists_eq_add_of_le' hf
    simp only at hrest
    subst hrest
    simp +arith +decide [lower, litHw, leaf, Hw.mk, Hw.ty, Flatten.charge, deep, binOp,
      finiteTy, signed, finite, width, constOf, twice, Core.Typed.Expr.erase, $[$ts:term],*]
    all_goals exact ⟨_, ⟨_, rfl⟩, rfl⟩))

/-! The proofs, one per row family. -/

theorem static_bin_agrees : BinAgrees := by
  intro op c hk s w x y st v hc h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases op <;> simp [coreOp] at hc <;> subst hc <;>
      simp [binary, finitePair_finite, coreOp, finiteOp] at h1 <;> subst h1 <;>
      simp at h2 <;> simp [← h2, Core.Semantics.evalExpr]
  · cases op <;> simp [coreOp] at hc <;> subst hc <;> cases s <;> lowers

theorem static_cmp_agrees : CmpAgrees := by
  intro op s k w x y st v hc h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> cases op <;> simp [binOp, pred] at hc <;> subst hc <;>
      simp [binary, equal, order, finite, finitePair, bind, Except.bind] at h1 <;> subst h1 <;>
      simp at h2 <;> subst h2 <;> refine ⟨_, rfl, ?_⟩ <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalPred, pred, ofBool_beq_one, bne]
  · cases s <;> cases op <;> simp [binOp, pred] at hc <;> subst hc <;> lowers

theorem static_bool_cmp_agrees : BoolCmpAgrees := by
  intro op k a b st v hop hc h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;>
      simp [binary, equal, bind, Except.bind] at h1 <;> subst h1 <;>
      simp at h2 <;> subst h2 <;> refine ⟨_, rfl, ?_⟩ <;> cases a <;> cases b <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalPred]
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;> lowers

theorem static_logic_agrees : LogicAgrees := by
  intro op c hk a b hop hc ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;> cases a <;> cases b <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalOp]
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;> lowers

theorem static_inv_agrees : InvAgrees := by
  intro s w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [unary, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      simp [← h2, Core.Semantics.evalExpr, finite]
  · cases s <;> lowers

theorem static_neg_agrees : NegAgrees := by
  intro s w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [unary, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      simp [← h2, Core.Semantics.evalExpr, Core.Semantics.evalOp, finite]
  · cases s <;> lowers

theorem static_not_agrees : NotAgrees := by
  intro b st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [unary] at h1; subst h1; simp at h2
    refine ⟨!b, h2.symm, ?_⟩
    cases b <;> simp [Core.Semantics.evalExpr, Core.Semantics.evalOp] <;> rfl
  · lowers

theorem static_shift_agrees : ShiftAgrees := by
  intro op s c hk w x b k st v hop hc hb h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hop with rfl | rfl <;> cases s <;> subst hc <;>
      rcases hb with rfl | ⟨u, y, rfl, rfl⟩ <;>
      simp +decide [binary, shift, finite, bind, Except.bind, natCast_lt_zero] at h1 <;>
      subst h1 <;> simp at h2 <;> subst h2 <;>
      simp +decide [Core.Semantics.evalExpr, finiteOp, finite, amount]
  · rcases hop with rfl | rfl <;> cases s <;> subst hc <;> lowers

theorem static_resize_same_agrees : ResizeSameAgrees := by
  intro s w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [resize, finiteTy, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      subst h2 <;> simp [Core.Semantics.evalExpr, finite]
  · cases s <;> lowers

theorem static_resize_trunc_agrees : ResizeTruncAgrees := by
  intro s n w hn x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [resize, finiteTy, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      subst h2 <;>
      simp [Core.Semantics.evalExpr, Core.Semantics.evalExtract, finite,
        BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hn),
        BitVec.setWidth_eq_extractLsb' (Nat.le_of_lt hn)]
  · cases s <;> lowers [Nat.ne_of_lt hn, hn]

theorem static_resize_zext_agrees : ResizeZextAgrees := by
  intro n w hn hb x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [resize] at h1; subst h1; simp at h2; subst h2
    simp [Core.Semantics.evalExpr, Core.Semantics.evalConcat,
      BitVec.setWidth_eq_append (Nat.le_of_lt hn)]
  · lowers [Nat.ne_of_gt hn, Nat.not_lt_of_gt hn]

theorem static_resize_sext_agrees : ResizeSextAgrees := by
  intro n w h0 hn hb x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [resize] at h1; subst h1; simp at h2; subst h2
    simp only [Core.Semantics.evalExpr, Core.Semantics.evalConcat,
      Core.Semantics.evalReplicate, Core.Semantics.evalExtract, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    congr 1
    ext i hi
    rw [BitVec.getElem_cast, BitVec.append_eq, BitVec.getElem_append, BitVec.getElem_signExtend]
    by_cases hw : i < w
    · simp [hw]
    · simp [hw, BitVec.getElem_replicate, BitVec.msb_eq_getLsbD_last, Nat.mod_one]
  · lowers [Nat.ne_of_gt hn, Nat.not_lt_of_gt hn]

theorem static_reinterpret_agrees : ReinterpretAgrees := by
  intro s r w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> cases r <;> simp [reinterpret, finiteTy, finite] at h1 <;> subst h1 <;>
      simp at h2 <;> subst h2 <;> simp [Core.Semantics.evalExpr, finite]
  · cases s <;> cases r <;> lowers

/-! Each finite static operation agrees with its core row, and `lower` emits that row. -/
theorem static_op_agrees :
    BinAgrees ∧ CmpAgrees ∧ BoolCmpAgrees ∧ LogicAgrees ∧ InvAgrees ∧ NegAgrees ∧
      NotAgrees ∧ ShiftAgrees ∧ ResizeSameAgrees ∧ ResizeTruncAgrees ∧ ResizeZextAgrees ∧
      ResizeSextAgrees ∧ ReinterpretAgrees :=
  ⟨static_bin_agrees, static_cmp_agrees, static_bool_cmp_agrees, static_logic_agrees,
    static_inv_agrees, static_neg_agrees, static_not_agrees, static_shift_agrees,
    static_resize_same_agrees, static_resize_trunc_agrees, static_resize_zext_agrees,
    static_resize_sext_agrees, static_reinterpret_agrees⟩

end Silicon.Source.StaticOps
