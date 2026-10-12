-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Parse.Input

/-!
The parser monad for the parser lemma of `parse_print`, and the facts about single tokens.

`Runs m ctx i j Q` states that `m` reads the tokens from the index `i` to the index `j` without
an error, and that its result satisfies `Q`. The height mark of the state stays as it is.
`Runs.bind` composes two such facts.

`After c k` states that the kind `k` can follow an expression in the context `c`. Such a kind
starts no suffix, it is not `::`, and it is no infix operator of the level `c` or higher.
-/
namespace Silicon.Source.ParsePrint

open Lex Parse Print

/-! ## The parser monad -/

/-- The parser runs `m` from the token `i` to the token `j`, and its result satisfies `Q`. -/
def Runs {α : Type} (m : P α) (ctx : Ctx) (i j : Nat) (Q : α → Prop) : Prop :=
  ∀ h, ∃ a, (m.run ctx).run ⟨i, h⟩ = .ok (a, ⟨j, h⟩) ∧ Q a

theorem Runs.mono {α : Type} {m : P α} {ctx : Ctx} {i j : Nat} {Q R : α → Prop}
    (hm : Runs m ctx i j Q) (h : ∀ a, Q a → R a) : Runs m ctx i j R := fun s =>
  let ⟨a, ha, hq⟩ := hm s
  ⟨a, ha, h a hq⟩

theorem Runs.bind {α β : Type} {m : P α} {k : α → P β} {ctx : Ctx} {i j l : Nat}
    {Q : α → Prop} {R : β → Prop} (hm : Runs m ctx i j Q)
    (hk : ∀ a, Q a → Runs (k a) ctx j l R) : Runs (m >>= k) ctx i l R := by
  intro h
  obtain ⟨a, ha, hq⟩ := hm h
  obtain ⟨b, hb, hr⟩ := hk a hq h
  refine ⟨b, ?_, hr⟩
  simp only [ReaderT.run_bind, StateT.run_bind, ha]
  exact hb

theorem Runs.pure {α : Type} {a : α} {ctx : Ctx} {i : Nat} {Q : α → Prop} (h : Q a) :
    Runs (Pure.pure a : P α) ctx i i Q := fun _ => ⟨a, rfl, h⟩

theorem Runs.peek_bind {β : Type} {k : Token → P β} {ctx : Ctx} {i l : Nat} {R : β → Prop}
    (hk : Runs (k (tokenAt ctx.input i)) ctx i l R) : Runs (Parse.peek >>= k) ctx i l R :=
  Runs.bind (Q := (· = tokenAt ctx.input i)) (fun _ => ⟨_, rfl, rfl⟩) fun _ h => h ▸ hk

theorem Runs.bump {ctx : Ctx} {i : Nat} : Runs bump ctx i (i + 1) (fun _ => True) :=
  fun _ => ⟨(), rfl, trivial⟩

theorem Runs.bump_bind {β : Type} {k : Unit → P β} {ctx : Ctx} {i l : Nat} {R : β → Prop}
    (hk : Runs (k ()) ctx (i + 1) l R) : Runs (Parse.bump >>= k) ctx i l R :=
  Runs.bind (Q := fun _ => True) (fun _ => ⟨(), rfl, trivial⟩) fun _ _ => hk

theorem Runs.sym_bind {β : Type} {k : Unit → P β} {ctx : Ctx} {i l : Nat} {R : β → Prop}
    {s : String} (hs : (tokenAt ctx.input i).kind = .symbol s)
    (hk : Runs (k ()) ctx (i + 1) l R) : Runs (Parse.sym s >>= k) ctx i l R := by
  refine Runs.bind (Q := fun _ => True) ?_ fun _ _ => hk
  unfold Parse.sym
  refine Runs.peek_bind ?_
  simp only [isSym, hs, beq_self_eq_true, ite_true]
  exact Runs.bump

theorem Runs.kw_bind {β : Type} {k : Unit → P β} {ctx : Ctx} {i l : Nat} {R : β → Prop}
    {s : String} (hs : (tokenAt ctx.input i).kind = .keyword s)
    (hk : Runs (k ()) ctx (i + 1) l R) : Runs (Parse.kw s >>= k) ctx i l R := by
  refine Runs.bind (Q := fun _ => True) ?_ fun _ _ => hk
  unfold Parse.kw
  refine Runs.peek_bind ?_
  simp only [isKw, hs, beq_self_eq_true, ite_true]
  exact Runs.bump


/-! ## Single tokens -/

theorem Runs.idx {α : Type} {m : P α} {ctx : Ctx} {i j j' : Nat} {Q : α → Prop} (h : j = j')
    (hm : Runs m ctx i j Q) : Runs m ctx i j' Q := h ▸ hm

theorem Runs.start {α : Type} {m : P α} {ctx : Ctx} {i i' j : Nat} {Q : α → Prop}
    (h : i = i') (hm : Runs m ctx i' j Q) : Runs m ctx i j Q := h ▸ hm

theorem Runs.acceptSym_true {ctx : Ctx} {i : Nat} {s : String}
    (hs : (tokenAt ctx.input i).kind = .symbol s) :
    Runs (acceptSym s) ctx i (i + 1) (· = true) := by
  unfold acceptSym
  refine Runs.peek_bind ?_
  simp only [isSym, hs, beq_self_eq_true, ite_true]
  exact Runs.bump_bind (Runs.pure rfl)

theorem Runs.acceptSym_false {ctx : Ctx} {i : Nat} {s : String}
    (hs : (tokenAt ctx.input i).kind ≠ .symbol s) : Runs (acceptSym s) ctx i i (· = false) := by
  unfold acceptSym
  refine Runs.peek_bind ?_
  simp only [isSym, beq_iff_eq, hs, ite_false]
  exact Runs.pure rfl

theorem Runs.acceptKw_true {ctx : Ctx} {i : Nat} {s : String}
    (hs : (tokenAt ctx.input i).kind = .keyword s) :
    Runs (acceptKw s) ctx i (i + 1) (· = true) := by
  unfold acceptKw
  refine Runs.peek_bind ?_
  simp only [isKw, hs, beq_self_eq_true, ite_true]
  exact Runs.bump_bind (Runs.pure rfl)

theorem Runs.acceptKw_false {ctx : Ctx} {i : Nat} {s : String}
    (hs : (tokenAt ctx.input i).kind ≠ .keyword s) : Runs (acceptKw s) ctx i i (· = false) := by
  unfold acceptKw
  refine Runs.peek_bind ?_
  simp only [isKw, beq_iff_eq, hs, ite_false]
  exact Runs.pure rfl

/-! A kind that ends a suffix chain: no call, index, or field follows. -/
def suffixStart (k : Kind) : Bool := k == .symbol "(" || k == .symbol "[" || k == .symbol "."

/-!
A kind that can follow an expression printed in the context `c`: no suffix, no `::`, and no
infix operator of the level `c` or higher.
-/
def After (c : Nat) (k : Kind) : Prop :=
  suffixStart k = false ∧ k ≠ .symbol "::" ∧ ∀ op : BinOp, c ≤ op.level → k ≠ .symbol op.text

theorem After.mono {c c' : Nat} {k : Kind} (h : After c k) (hc : c ≤ c') : After c' k :=
  ⟨h.1, h.2.1, fun op hop => h.2.2 op (by omega)⟩

/-! A symbol that is no operator, no suffix, and not `::` follows each expression. -/
theorem After.sym {c : Nat} {s : String} (h : ∀ op : BinOp, op.text ≠ s)
    (h1 : s ≠ "(" ∧ s ≠ "[" ∧ s ≠ "." ∧ s ≠ "::") : After c (.symbol s) := by
  refine ⟨?_, by simpa using h1.2.2.2, fun op _ he => h op ?_⟩
  · simp [suffixStart, h1.1, h1.2.1, h1.2.2.1]
  · simp only [Kind.symbol.injEq] at he
    exact he.symm

theorem BinOp.text_inj {a b : BinOp} (h : a.text = b.text) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [BinOp.text] at h)

/-! An operator follows an expression in a context above its level. -/
theorem After.op {c : Nat} {op : BinOp} (h : op.level < c) : After c (.symbol op.text) := by
  refine ⟨by cases op <;> decide, by cases op <;> decide, fun op' hop he => ?_⟩
  simp only [Kind.symbol.injEq] at he
  rw [BinOp.text_inj he] at h
  omega

theorem opAt_none {k : Nat} {t : Token} (h : After k t.kind) : opAt k t = none := by
  unfold opAt
  rw [List.find?_eq_none]
  intro op _
  simp only [isSym, Bool.and_eq_true, beq_iff_eq, not_and]
  intro hl ht
  exact h.2.2 op (by omega) ht

theorem opAt_text {op : BinOp} {t : Token} (h : t.kind = .symbol op.text) :
    opAt op.level t = some op := by
  unfold opAt isSym
  rw [h]
  cases op <;> decide

/-! The kinds that start the text of a primary form. -/
def PStart (k : Kind) : Prop :=
  (∃ n, k = .ident n) ∨ (∃ v, k = .number v) ∨ (∃ s, k = .string s) ∨ k = .keyword "true" ∨
    k = .keyword "false" ∨ k = .symbol "(" ∨ k = .symbol "["

theorem unOp_pstart {t : Token} (h : PStart t.kind) : unOp t = none := by
  unfold unOp
  rcases h with ⟨n, h⟩ | ⟨v, h⟩ | ⟨s, h⟩ | h | h | h | h <;>
    simp [isSym, h, UnOp.text]

theorem isKw_pstart {t : Token} (h : PStart t.kind) : isKw "fn" t = false := by
  rcases h with ⟨n, h⟩ | ⟨v, h⟩ | ⟨s, h⟩ | h | h | h | h <;> simp [isKw, h]

theorem unOp_text {t : Token} {op : UnOp} (h : t.kind = .symbol op.text) : unOp t = some op := by
  unfold unOp isSym
  rw [h]
  cases op <;> decide


/-! ## The first token of an expression -/

theorem PStart.ne {k : Kind} (h : PStart k) : k ≠ .symbol ")" ∧ k ≠ .symbol "]" := by
  rcases h with ⟨n, h⟩ | ⟨v, h⟩ | ⟨s, h⟩ | h | h | h | h <;> simp [h]

theorem BinOp.level_pos (op : BinOp) : 1 ≤ op.level := by cases op <;> decide

theorem BinOp.level_lt (op : BinOp) : op.level < 10 := by cases op <;> decide

theorem Expr.toks_head11 (e : Expr) : ∃ k, (e.toks 11).head? = some k ∧ PStart k := by
  induction e using Expr.ind with
  | case1 p v => exact ⟨_, by simp [Expr.toks, Expr.level, postfixLevel], Or.inr (Or.inl ⟨v, rfl⟩)⟩
  | case2 p v => exact ⟨.keyword (boolean v), by simp [Expr.toks, Expr.level, postfixLevel], by
      cases v <;> simp [boolean, PStart]⟩
  | case3 p v => exact ⟨_, by simp [Expr.toks, Expr.level, postfixLevel],
      Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))⟩
  | case4 p n => exact ⟨_, by simp [Expr.toks, Expr.level, postfixLevel], Or.inl ⟨n, rfl⟩⟩
  | case5 | case17 => exact ⟨_, by simp [Expr.toks, Expr.level, unaryLevel],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | case6 p op => exact ⟨_, by
      simp [Expr.toks, Expr.level, (by have := BinOp.level_lt op; omega : op.level < 11)],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | case7 => exact ⟨_, by simp [Expr.toks, Expr.level],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | case8 p f xs ihf _ =>
    rw [Expr.toks.eq_def]
    simp only [Expr.level, postfixLevel, Nat.lt_irrefl, ite_false]
    split
    · exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
    · obtain ⟨k, h, hk⟩ := ihf
      exact ⟨k, by simp [List.head?_append, h], hk⟩
  | case9 p b xs ihb _ =>
    obtain ⟨k, h, hk⟩ := ihb
    exact ⟨k, by simp [Expr.toks, Expr.level, postfixLevel, List.head?_append, h], hk⟩
  | case10 p b f ihb =>
    obtain ⟨k, h, hk⟩ := ihb
    exact ⟨k, by simp [Expr.toks, Expr.level, postfixLevel, List.head?_append, h], hk⟩
  | case11 | case12 => exact ⟨_, by simp [Expr.toks, Expr.level, postfixLevel],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | case13 | case15 => exact ⟨_, by simp [Expr.toks, Expr.level, postfixLevel],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩
  | case14 p b q i ihb =>
    obtain ⟨k, h, hk⟩ := ihb
    exact ⟨k, by simp [Expr.toks, Expr.level, postfixLevel, List.head?_append, h], hk⟩
  | case16 p r m xs ihr _ =>
    obtain ⟨k, h, hk⟩ := ihr
    exact ⟨k, by simp [Expr.toks, Expr.level, postfixLevel, List.head?_append, h], hk⟩

/-! The first kind of an expression is no closing bracket. -/
def NotClose (k : Kind) : Prop := k ≠ .symbol ")" ∧ k ≠ .symbol "]"

theorem Expr.toks_head_post (e : Expr) (hl : e.level = 11) (c : Nat) :
    ∃ k, (e.toks c).head? = some k ∧ NotClose k := by
  obtain ⟨k, h, hk⟩ := Expr.toks_head11 e
  rw [Expr.toks_paren] at h ⊢
  split
  · exact ⟨_, rfl, by simp [NotClose]⟩
  · simp only [hl, Nat.lt_irrefl, ite_false] at h
    exact ⟨k, h, hk.ne⟩

theorem Expr.toks_head (e : Expr) : ∀ c, ∃ k, (e.toks c).head? = some k ∧ NotClose k := by
  induction e using Expr.ind with
  | case5 p op a _ =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, by simp [NotClose]⟩
    · exact ⟨.symbol op.text, by simp [Expr.toks], by cases op <;> simp [NotClose, UnOp.text]⟩
  | case6 p op l r ihl _ =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, by simp [NotClose]⟩
    · obtain ⟨k, h, hk⟩ := ihl (if op.associative then op.level else op.level + 1)
      exact ⟨k, by simp [Expr.toks, List.head?_append, h], hk⟩
  | case7 =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, by simp [NotClose]⟩
    · exact ⟨.keyword "if", by simp [Expr.toks], by simp [NotClose]⟩
  | case17 =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, by simp [NotClose]⟩
    · exact ⟨.keyword "fn", by simp [Expr.toks], by simp [NotClose]⟩
  | _ => exact Expr.toks_head_post _ (by simp [Expr.level, postfixLevel])


end Silicon.Source.ParsePrint
