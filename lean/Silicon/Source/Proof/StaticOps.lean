-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Flatten
import Silicon.Core.Semantics.Expression

/-!
The finite static operations of the evaluator agree with the core (section 7.4 of the front-end
spec). A static operation gives the value of the core row that `Flatten.lower` builds for the
same operator, with the constants `Flatten.constOf` of the operands as its leaves. `evalExpr`
evaluates the row in each context. Each statement gives the row twice: as the typed expression
that `evalExpr` evaluates, and as its erasure, the untyped row of `Flatten.lower`.

A row of a static shift count takes the count as a constant, as `Flatten.lower` does for a
literal count. A `resize` row needs `1 ≤ w` for a sign extension, and a result of at most 65536
bits for an extension. `Eval.family` gives both bounds to each finite type.
-/
namespace Silicon.Source.StaticOps

open Eval Flatten
open Core.Semantics (Valuation Memories)

local notation "ev" => Core.Semantics.evalExpr

/-! The typed core expression of the width `w`. -/
local notation "Ex" ctx:max w:max => Core.Typed.Expr ctx (Core.Ty.bits w)

/-! A static operation and its row: each operand, the step, and the result. -/

/-- `+%`, `-%`, `*%`, `&`, `|`, and `^`: the row `bin c a b`. -/
def BinAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (c : Core.BinOp) (hk : c ≠ .concat) (w : Nat) (x y : BitVec w)
    (st : Step) (v : Value), binOp op s = some (.inl c) →
    binary op (finite s w x) (finite s w y) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx w := .bin p c hk (.const p w x.toNat) (.const p w y.toNat)
    e.erase = .bin p c (constOf p (finite s w x)) (constOf p (finite s w y)) ∧
      v = finite s w (ev vals mems e)

/-- `==`, `!=`, `<`, `<=`, `>`, and `>=`: the row `icmp k a b`. -/
def CmpAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (k : Core.Pred) (w : Nat) (x y : BitVec w) (st : Step)
    (v : Value), binOp op s = some (.inr k) →
    binary op (finite s w x) (finite s w y) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx 1 := .icmp p k (.const p w x.toNat) (.const p w y.toNat)
    e.erase = .icmp p k (constOf p (finite s w x)) (constOf p (finite s w y)) ∧
      ∃ b, v = .bool b ∧ ev vals mems e = BitVec.ofBool b

/-- `~`: the row `not a`. -/
def InvAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    unary .inv (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx w := .un p .not (.const p w x.toNat)
    e.erase = .un p .not (constOf p (finite s w x)) ∧ v = finite s w (ev vals mems e)

/-- Unary `-`: the row `sub (const w 0) a`. -/
def NegAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    unary .neg (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx w := .bin p .sub (by decide) (.const p w 0) (.const p w x.toNat)
    e.erase = .bin p .sub (.const p w 0) (constOf p (finite s w x)) ∧
      v = finite s w (ev vals mems e)

/-- `!` on `Bool`: the row `xor a (const 1 1)`. -/
def NotAgrees : Prop :=
  ∀ (b : Bool) (st : Step) (v : Value),
    unary .not (.bool b) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx 1 := .bin p .xor (by decide) (.const p 1 (if b then 1 else 0)) (.const p 1 1)
    e.erase = .bin p .xor (constOf p (.bool b)) (.const p 1 1) ∧
      ∃ r, v = .bool r ∧ ev vals mems e = BitVec.ofBool r

/-- `<<` and `>>` with a static count `n`: the row `c a (const w (min n w))`. -/
def ShiftAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (c : Core.BinOp) (hk : c ≠ .concat) (w : Nat) (x : BitVec w)
    (n : Int) (st : Step) (v : Value), (op = .shl ∨ op = .shr) →
    c = (if op == .shl then .shl else if s then .shrs else .shru) →
    binary op (finite s w x) (.int n) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx w := .bin p c hk (.const p w x.toNat) (.const p w (min n.toNat w))
    e.erase = .bin p c (constOf p (finite s w x)) (.const p w (min n.toNat w)) ∧
      v = finite s w (ev vals mems e)

/-- `resize` to the same width: the row is the operand. -/
def ResizeSameAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    resize (if s then .sint w else .uint w) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx w := .const p w x.toNat
    e.erase = constOf p (finite s w x) ∧ v = finite s w (ev vals mems e)

/-- `resize` to a smaller width `n`: the row `extract a 0 n`. -/
def ResizeTruncAgrees : Prop :=
  ∀ (s : Bool) (n w : Nat) (hn : n < w) (x : BitVec w) (st : Step) (v : Value),
    resize (if s then .sint n else .uint n) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx n := .extract p (.const p w x.toNat) 0 n (by omega)
    e.erase = .extract p (constOf p (finite s w x)) 0 n ∧ v = finite s n (ev vals mems e)

/-- `resize` of a `UInt` to a larger width `n`: the row `concat (const (n - w) 0) a`. -/
def ResizeZextAgrees : Prop :=
  ∀ (n w : Nat) (hn : w < n) (hb : n ≤ 65536) (x : BitVec w) (st : Step) (v : Value),
    resize (.uint n) (.uint w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx (n - w + w) := .concat p (.const p (n - w) 0) (.const p w x.toNat) (by omega)
    e.erase = .bin p .concat (.const p (n - w) 0) (constOf p (.uint w x)) ∧
      v = .uint n ((ev vals mems e).cast (by omega))

/--
`resize` of an `SInt` to a larger width `n`: the row
`concat (replicate (extract a (w - 1) 1) (n - w)) a`.
-/
def ResizeSextAgrees : Prop :=
  ∀ (n w : Nat) (h0 : 1 ≤ w) (hn : w < n) (hb : n ≤ 65536) (x : BitVec w) (st : Step)
    (v : Value),
    resize (.sint n) (.sint w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let a : Ex ctx w := .const p w x.toNat
    let e : Ex ctx (1 * (n - w) + w) :=
      .concat p (.replicate p (.extract p a (w - 1) 1 (by omega)) (n - w) (by omega)) a
        (by omega)
    let ca := constOf p (.sint w x)
    e.erase = .bin p .concat (.replicate p (.extract p ca (w - 1) 1) (n - w)) ca ∧
      v = .sint n ((ev vals mems e).cast (by omega))

/-- `reinterpret` keeps the width: the row is the operand. -/
def ReinterpretAgrees : Prop :=
  ∀ (s r : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    reinterpret (if r then .sint w else .uint w) (finite s w x) = .ok st →
    st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx) (p : Core.Pos),
    let e : Ex ctx w := .const p w x.toNat
    e.erase = constOf p (finite s w x) ∧ v = finite r w (ev vals mems e)

/-! Facts about the lift and the operands. -/

private theorem constOf_finite (p : Core.Pos) (s : Bool) (w : Nat) (x : BitVec w) :
    constOf p (finite s w x) = .const p w x.toNat := by
  cases s <;> rfl

private theorem finitePair_finite (s : Bool) (w : Nat) (x y : BitVec w) :
    finitePair (finite s w x) (finite s w y) = some (s, ⟨w, x, y⟩) := by
  cases s <;> simp [finite, finitePair]

private theorem ofBool_beq_one (b : Bool) : (BitVec.ofBool b == 1#1) = b := by
  cases b <;> rfl

/-! The proofs, one per row family. -/

theorem static_bin_agrees : BinAgrees := by
  intro op s c hk w x y st v hc h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases op <;> simp [binOp] at hc <;> subst hc <;>
    simp [binary, finitePair_finite, coreOp, finiteOp, typeError] at h1 <;> subst h1 <;>
    simp at h2 <;> simp [← h2, Core.Semantics.evalExpr]

theorem static_cmp_agrees : CmpAgrees := by
  intro op s k w x y st v hc h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases s <;> cases op <;> simp [binOp, pred] at hc <;> subst hc <;>
    simp [binary, equal, order, finite, finitePair, bind, Except.bind] at h1 <;> subst h1 <;>
    simp at h2 <;> subst h2 <;> refine ⟨_, rfl, ?_⟩ <;>
    simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalPred, pred, ofBool_beq_one, bne]

theorem static_inv_agrees : InvAgrees := by
  intro s w x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases s <;> simp [unary, finite] at h1 <;> subst h1 <;> simp at h2 <;>
    simp [← h2, Core.Semantics.evalExpr, finite]

theorem static_neg_agrees : NegAgrees := by
  intro s w x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases s <;> simp [unary, finite] at h1 <;> subst h1 <;> simp at h2 <;>
    simp [← h2, Core.Semantics.evalExpr, Core.Semantics.evalOp, finite]

theorem static_not_agrees : NotAgrees := by
  intro b st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf], ?_⟩
  simp [unary] at h1; subst h1; simp at h2
  refine ⟨!b, h2.symm, ?_⟩
  cases b <;> simp [Core.Semantics.evalExpr, Core.Semantics.evalOp] <;> rfl

theorem static_shift_agrees : ShiftAgrees := by
  intro op s c hk w x n st v hop hc h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  rcases hop with rfl | rfl <;> cases s <;> subst hc <;>
    by_cases hn : n < 0 <;>
    simp +decide [binary, shift, finite, bind, Except.bind, hn] at h1 <;>
    subst h1 <;> simp at h2 <;> subst h2 <;>
    simp +decide [Core.Semantics.evalExpr, finiteOp, finite, amount]

theorem static_resize_same_agrees : ResizeSameAgrees := by
  intro s w x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases s <;> simp [resize, finite] at h1 <;> subst h1 <;> simp at h2 <;> subst h2 <;>
    simp [Core.Semantics.evalExpr, finite]

theorem static_resize_trunc_agrees : ResizeTruncAgrees := by
  intro s n w hn x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases s <;> simp [resize, finite] at h1 <;> subst h1 <;> simp at h2 <;> subst h2 <;>
    simp [Core.Semantics.evalExpr, Core.Semantics.evalExtract, finite,
      BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hn),
      BitVec.setWidth_eq_extractLsb' (Nat.le_of_lt hn)]

theorem static_resize_zext_agrees : ResizeZextAgrees := by
  intro n w hn hb x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf], ?_⟩
  simp [resize] at h1; subst h1; simp at h2; subst h2
  simp [Core.Semantics.evalExpr, Core.Semantics.evalConcat,
    BitVec.setWidth_eq_append (Nat.le_of_lt hn)]

theorem static_resize_sext_agrees : ResizeSextAgrees := by
  intro n w h0 hn hb x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf], ?_⟩
  simp [resize] at h1; subst h1; simp at h2; subst h2
  simp only [Core.Semantics.evalExpr, Core.Semantics.evalConcat, Core.Semantics.evalReplicate,
    Core.Semantics.evalExtract, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  congr 1
  ext i hi
  rw [BitVec.getElem_cast, BitVec.append_eq, BitVec.getElem_append, BitVec.getElem_signExtend]
  by_cases hw : i < w
  · simp [hw]
  · simp [hw, BitVec.getElem_replicate, BitVec.msb_eq_getLsbD_last, Nat.mod_one]

theorem static_reinterpret_agrees : ReinterpretAgrees := by
  intro s r w x st v h1 h2 ctx vals mems p
  refine ⟨by simp [Core.Typed.Expr.erase, constOf_finite], ?_⟩
  cases s <;> cases r <;> simp [reinterpret, finite] at h1 <;> subst h1 <;> simp at h2 <;>
    subst h2 <;> simp [Core.Semantics.evalExpr, finite]

/-! Each finite static operation agrees with its core row. -/
theorem static_op_agrees :
    BinAgrees ∧ CmpAgrees ∧ InvAgrees ∧ NegAgrees ∧ NotAgrees ∧ ShiftAgrees ∧
      ResizeSameAgrees ∧ ResizeTruncAgrees ∧ ResizeZextAgrees ∧ ResizeSextAgrees ∧
      ReinterpretAgrees :=
  ⟨static_bin_agrees, static_cmp_agrees, static_inv_agrees, static_neg_agrees,
    static_not_agrees, static_shift_agrees, static_resize_same_agrees,
    static_resize_trunc_agrees, static_resize_zext_agrees, static_resize_sext_agrees,
    static_reinterpret_agrees⟩

end Silicon.Source.StaticOps
