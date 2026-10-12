-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Parse.Expr

/-!
The parser lemma of `parse_print` for statements and blocks.

`Runs.stmt_print` gives `SGoal s` for each statement `s`:

```lean
s.printable ctx.plainFn = true → Win ctx.input i (s.toks ++ t :: R) →
  t ≠ .keyword "else" → 4 * s.toks.length + 4 ≤ f → s.toks.length ≤ ctx.depth →
  Runs (stmt f) ctx i (i + s.toks.length) (fun s' => s'.erase = s.erase)
```

The parser reads exactly the kinds of `s`, and the result is `s` up to positions. The kind
after a statement is never `else`, so a `comptime if` without `else` stops after its block.
The fuel is linear in the number of kinds, so a block needs no more than four units of fuel
for each of its kinds.

The proof is an induction on the number of kinds. A statement that starts with a name reads
a postfix form. A place gives the flag `true`, and `=` or `:=` follows it. Another form starts
an expression statement.
-/
namespace Silicon.Source.ParsePrint

open Lex Parse Print

/-! ## Monad steps -/

theorem Runs.read_bind {β : Type} {k : Ctx → P β} {ctx : Ctx} {i l : Nat} {R : β → Prop}
    (hk : Runs (k ctx) ctx i l R) : Runs (read >>= k) ctx i l R :=
  Runs.bind (Q := (· = ctx)) (fun _ => ⟨ctx, rfl, rfl⟩) fun _ h => h ▸ hk

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

theorem Runs.noDomain {ctx : Ctx} {i : Nat} (h : (tokenAt ctx.input i).kind ≠ .keyword "in") :
    Runs noDomain ctx i i (fun _ => True) := by
  unfold Parse.noDomain
  refine Runs.peek_bind ?_
  simp only [isKw, beq_iff_eq, h, ite_false]
  exact Runs.pure trivial

theorem Ident.erase_of_name {a b : Ident} (h : a.name = b.name) : a.erase = b.erase := by
  simp [Ident.erase, h]

/-! `typeAnnotation` reads `:` and an outermost type. -/
theorem Runs.typeAnnotation (ty : TypeExpr) (hp : ty.printable = true) (ctx : Ctx) (i f : Nat)
    (u : Kind) (R : List Kind) (hw : Win ctx.input i (.symbol ":" :: (ty.toks ++ u :: R)))
    (hu : u ≠ .symbol "[" ∧ u ≠ .symbol "(" ∧ u ≠ .symbol "::") (hf : 4 * ty.toks.length ≤ f)
    (hd : ty.toks.length ≤ ctx.depth) :
    Runs (Parse.typeAnnotation f) ctx i (i + 1 + ty.toks.length)
      (fun r => r.erase = ty.erase) := by
  unfold Parse.typeAnnotation
  exact Runs.sym_bind hw.head (Runs.typeTop ty hp ctx (i + 1) f u R hw.tail hu hf hd)

/-! ## The first kind of an expression -/

/-! The kinds that start the text of an expression. -/
def EHead (k : Kind) : Prop :=
  PStart k ∨ k = .keyword "if" ∨ ∃ op : UnOp, k = .symbol op.text

theorem Expr.headKind (e : Expr) : ∀ c, ∃ k, (e.toks c).head? = some k ∧ EHead k := by
  have post : ∀ e : Expr, e.level = 11 → ∀ c, ∃ k, (e.toks c).head? = some k ∧ EHead k := by
    intro e hl c
    obtain ⟨k, h, hk⟩ := Expr.toks_head11 e
    rw [Expr.toks_paren] at h ⊢
    split
    · exact ⟨_, rfl, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
    · simp only [hl, Nat.lt_irrefl, ite_false] at h
      exact ⟨k, h, Or.inl hk⟩
  induction e using Expr.ind with
  | case5 p op a _ =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
    · exact ⟨.symbol op.text, by simp [Expr.toks], Or.inr (Or.inr ⟨op, rfl⟩)⟩
  | case6 p op l r ihl _ =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
    · obtain ⟨k, h, hk⟩ := ihl (if op.associative then op.level else op.level + 1)
      exact ⟨k, by simp [Expr.toks, List.head?_append, h], hk⟩
  | case7 =>
    intro c; rw [Expr.toks_paren]; split
    · exact ⟨_, rfl, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
    · exact ⟨.keyword "if", by simp [Expr.toks], Or.inr (Or.inl rfl)⟩
  | _ => exact post _ (by simp [Expr.level, postfixLevel])

theorem EHead.ne_kw {k : Kind} (h : EHead k) {w : String}
    (hw : w ≠ "if" ∧ w ≠ "true" ∧ w ≠ "false") : k ≠ .keyword w := by
  rintro rfl
  rcases h with (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | h) | h | ⟨op, h⟩ <;>
    simp_all

theorem EHead.ne_sym {k : Kind} (h : EHead k) {s : String}
    (hs : s ≠ "(" ∧ s ≠ "[" ∧ s ≠ "!" ∧ s ≠ "~" ∧ s ≠ "-") : k ≠ .symbol s := by
  rintro rfl
  rcases h with (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | h) | h | ⟨op, h⟩
  all_goals simp only [Kind.symbol.injEq, reduceCtorEq] at h
  · exact hs.1 h
  · exact hs.2.1 h
  · cases op <;> simp [UnOp.text] at h <;> simp_all

theorem EHead.ne_eof {k : Kind} (h : EHead k) : k ≠ .eof := by
  rintro rfl
  rcases h with (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | h) | h | ⟨op, h⟩ <;> simp at h

theorem EHead.ne_ident {k : Kind} (h : EHead k) (_hn : ∀ n, k ≠ .ident n) :
    ∀ w, k ≠ .keyword w ∨ w = "if" ∨ w = "true" ∨ w = "false" := by
  intro w
  by_cases hw : w = "if" ∨ w = "true" ∨ w = "false"
  · exact Or.inr hw
  · exact Or.inl (h.ne_kw (by simp_all))

theorem Expr.toks_noparen {e : Expr} {c : Nat} (h : ¬ e.level < c) : e.toks c = e.toks 0 := by
  rw [Expr.toks_paren, ite_eq_right_iff.2 (fun h' => absurd h' h)]

theorem Expr.noparen_of_ident {e : Expr} {c : Nat} {n : String}
    (hh : (e.toks c).head? = some (.ident n)) : ¬ e.level < c := by
  intro hl
  rw [Expr.toks_paren] at hh
  simp [hl] at hh

theorem head?_append_of {a b : List Kind} {k : Kind} (h : a.head? = some k) :
    (a ++ b).head? = some k := by
  cases a with
  | nil => simp at h
  | cons x xs => simpa using h

theorem head?_append_ne {a b : List Kind} (h : a ≠ []) : (a ++ b).head? = a.head? := by
  cases a with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem Expr.toks_ne_nil (e : Expr) (c : Nat) : e.toks c ≠ [] := by
  obtain ⟨k, hk, -⟩ := Expr.toks_head e c
  intro h; rw [h] at hk; simp at hk

theorem Runs.map_bind {α β γ : Type} {m : P α} {g : α → β} {k : β → P γ} {ctx : Ctx}
    {i j l : Nat} {Q : α → Prop} {R : γ → Prop} (hm : Runs m ctx i j Q)
    (hk : ∀ a, Q a → Runs (k (g a)) ctx j l R) : Runs (g <$> m >>= k) ctx i l R := by
  rw [map_eq_pure_bind, bind_assoc]
  exact Runs.bind hm fun a ha => by rw [pure_bind]; exact hk a ha

/-! ## Statements -/

/-! `stmt` reads the kinds of `s` back to `s`, up to positions. -/
def SGoal (s : Stmt) : Prop :=
  ∀ (ctx : Ctx) (i f : Nat) (t : Kind) (R : List Kind), s.printable ctx.plainFn = true →
    Win ctx.input i (s.toks ++ t :: R) → t ≠ .keyword "else" → 4 * s.toks.length + 4 ≤ f →
    s.toks.length ≤ ctx.depth →
    Runs (stmt f) ctx i (i + s.toks.length) (fun s' => s'.erase = s.erase)

/-! The check for a resource in a `fn` without `comptime` passes. -/
theorem stmt_res {ctx : Ctx} {tok : Token}
    (h : ctx.plainFn = false ∨ ∀ w ∈ resourceKeywords, tok.kind ≠ .keyword w) :
    (ctx.plainFn && resourceKeywords.any fun x => isKw x tok) = false := by
  rcases h with h | h
  · simp [h]
  · simp only [Bool.and_eq_false_iff, List.any_eq_false, isKw, beq_iff_eq]
    exact Or.inr fun w hw he => h w hw he

theorem not_res {k : Kind} (h : ∀ w, k = .keyword w → w ∉ resourceKeywords) :
    ∀ w ∈ resourceKeywords, k ≠ .keyword w := fun w hw he => h w he hw

/-! The window of a statement, with its kinds as a list of single kinds and parts. -/
macro "norm_win" : tactic => `(tactic| simp only [Stmt.toks, ite_true, ite_false,
  Bool.false_eq_true, Option.map, Option.getD, List.cons_append, List.nil_append,
  List.singleton_append, List.append_assoc, List.length_cons, List.length_append,
  List.length_nil, List.length_singleton] at *)

theorem isSym_of {tok : Token} {s : String} {k : Kind} (h : tok.kind = k) :
    isSym s tok = decide (k = .symbol s) := by
  simp only [isSym, h, Kind.beq_eq]

theorem isKw_of {tok : Token} {s : String} {k : Kind} (h : tok.kind = k) :
    isKw s tok = decide (k = .keyword s) := by
  simp only [isKw, h, Kind.beq_eq]

/-! Each lemma reduces the checks of the parser on a known kind. -/
macro "reduce_checks" : tactic => `(tactic| simp only [↓reduceIte, Kind.symbol.injEq,
  Kind.keyword.injEq, reduceCtorEq, String.reduceEq, decide_false, decide_true,
  Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true, Bool.or_false,
  Bool.false_or, Bool.or_true, Bool.true_or])

theorem After.semi {c : Nat} : After c (.symbol ";") :=
  After.sym (fun op => by cases op <;> decide) (by decide)

theorem After.eq {c : Nat} : After c (.symbol "=") :=
  After.sym (fun op => by cases op <;> decide) (by decide)

theorem Win.head' {inp : Input} {i : Nat} {a R : List Kind} {k : Kind} (h : Win inp i (a ++ R))
    (ha : a.head? = some k) : (tokenAt inp i).kind = k := by
  cases a with
  | nil => simp at ha
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at ha; subst ha; exact h.head

theorem stmt_res_kw {ctx : Ctx} {tok : Token} {w : String} (h : tok.kind = .keyword w)
    (hw : resourceKeywords.contains w = false) :
    (ctx.plainFn && resourceKeywords.any fun x => isKw x tok) = false :=
  stmt_res (Or.inr fun w' hw' he => by
    rw [h] at he; cases he; simp_all)

theorem stmt_res_nkw {ctx : Ctx} {tok : Token} (h : ∀ w, tok.kind ≠ .keyword w) :
    (ctx.plainFn && resourceKeywords.any fun x => isKw x tok) = false :=
  stmt_res (Or.inr fun w _ => h w)

theorem Runs.stmt_local (p : Pos) (m : Bool) (n : Ident) (ty : Option TypeExpr) (v : Expr) :
    SGoal (.local p m n ty v) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hn, hty⟩, hv⟩ := hp
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  have hk : (tokenAt ctx.input i).kind = .keyword "let" := hw.head' (by simp [Stmt.toks])
  simp only [stmt_res_kw hk (by decide), hk, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  have hm : ∀ R', Win ctx.input (i + 1) ((if m then [Kind.keyword "mut"] else []) ++
      .ident n.name :: R') →
      Runs (acceptKw "mut") ctx (i + 1) (i + 1 + (if m then 1 else 0)) (· = m) := by
    intro R' w
    cases m
    · exact Runs.acceptKw_false (by rw [w.head]; simp)
    · exact Runs.acceptKw_true w.head
  have hw1 : Win ctx.input (i + 1) ((if m then [Kind.keyword "mut"] else []) ++ .ident n.name ::
      (((ty.map fun t => .symbol ":" :: t.toks).getD []) ++ .symbol "=" :: (v.toks 0 ++
      .symbol ";" :: t :: R))) := by
    have e : (Stmt.local p m n ty v).toks ++ t :: R = .keyword "let" ::
        ((if m then [Kind.keyword "mut"] else []) ++ .ident n.name ::
        (((ty.map fun t => .symbol ":" :: t.toks).getD []) ++ .symbol "=" :: (v.toks 0 ++
        .symbol ";" :: t :: R))) := by
      simp [Stmt.toks]
    rw [e] at hw
    exact hw.tail
  refine Runs.bind (hm _ hw1) fun b hb => ?_
  subst b
  have hw2 := hw1.drop
  have hlm : (if m then [Kind.keyword "mut"] else []).length = if m then 1 else 0 := by
    cases m <;> rfl
  rw [hlm] at hw2
  refine Runs.bind (Runs.ident hw2.head) fun id hid => ?_
  have hw3 := hw2.tail
  have hT : (Stmt.local p m n ty v).toks.length = 1 + (if m then 1 else 0) + 1 +
      ((ty.map fun t => .symbol ":" :: t.toks).getD []).length + 1 + (v.toks 0).length + 1 := by
    cases m <;> simp [Stmt.toks] <;> omega
  rw [hT] at hf hd ⊢
  have tail : ∀ (o : Option TypeExpr) (j : Nat), o.map TypeExpr.erase = ty.map TypeExpr.erase →
      Win ctx.input j (.symbol "=" :: (v.toks 0 ++ .symbol ";" :: t :: R)) →
      j = i + 1 + (if m then 1 else 0) + 1 +
        ((ty.map fun t => .symbol ":" :: t.toks).getD []).length →
      Runs (sym "=" >>= fun _ => Parse.value f >>= fun v => sym ";" >>= fun _ =>
          Pure.pure (Stmt.local (tokenAt ctx.input i).pos m id o v)) ctx j
        (i + (1 + (if m then 1 else 0) + 1 +
          ((ty.map fun t => .symbol ":" :: t.toks).getD []).length + 1 + (v.toks 0).length + 1))
        (fun s' => s'.erase = (Stmt.local p m n ty v).erase) := by
    intro o j ho w hj
    refine Runs.sym_bind w.head ?_
    refine Runs.bind (Runs.value v hv ctx _ f _ _ w.tail After.semi (by omega) (by omega))
      fun v' hv' => ?_
    refine Runs.sym_bind w.tail.drop.head (Runs.idx (by omega) (Runs.pure ?_))
    simp [Stmt.erase, Ident.erase_of_name (b := n) hid, hv', ho]
  refine Runs.peek_bind ?_
  cases ty with
  | none =>
    simp only [Option.map, Option.getD] at hw3 tail ⊢
    simp only [List.nil_append] at hw3
    simp only [isSym_of hw3.head]
    reduce_checks
    exact Runs.bind (Runs.pure (Q := (· = none)) rfl) fun o ho => tail o _ (by rw [ho]) hw3
      (by simp)
  | some ty =>
    simp only [Option.map, Option.getD, Option.all] at hw3 tail hty ⊢
    simp only [List.cons_append] at hw3
    simp only [isSym_of hw3.head]
    reduce_checks
    refine Runs.map_bind (Runs.typeAnnotation ty hty ctx _ f _ _ hw3 (by decide)
      (by simp at hf; omega) (by simp at hd; omega)) fun ty' hty' => ?_
    exact tail _ _ (by simp [hty']) hw3.tail.drop (by simp; omega)

theorem After.dots {c : Nat} : After c (.symbol "..") :=
  After.sym (fun op => by cases op <;> decide) (by decide)

theorem After.brace {c : Nat} : After c (.symbol "{") :=
  After.sym (fun op => by cases op <;> decide) (by decide)

theorem Runs.stmt_reg (p : Pos) (n : Ident) (ty : TypeExpr) (v : Expr) :
    SGoal (.reg p n ty v) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨hpl, hn⟩, hty⟩, hv⟩ := hp
  have e : (Stmt.reg p n ty v).toks ++ t :: R = .keyword "reg" :: .ident n.name ::
      .symbol ":" :: (ty.toks ++ .symbol "=" :: (v.toks 0 ++ .symbol ";" :: t :: R)) := by
    simp [Stmt.toks]
  have hT : (Stmt.reg p n ty v).toks.length = ty.toks.length + (v.toks 0).length + 5 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res (Or.inl hpl), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  have w := hw.tail.tail
  refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ w (by decide) (by omega) (by omega))
    fun ty' hty' => ?_
  have w2 := w.tail.drop
  refine Runs.bind (Runs.noDomain (by rw [w2.head]; decide)) fun _ _ => ?_
  refine Runs.sym_bind w2.head ?_
  refine Runs.bind (Runs.value v hv ctx _ f _ _ w2.tail After.semi (by omega) (by omega))
    fun v' hv' => ?_
  refine Runs.sym_bind w2.tail.drop.head (Runs.idx (by omega) (Runs.pure ?_))
  simp [Stmt.erase, Ident.erase_of_name (b := n) hid, hv', hty']

theorem Runs.stmt_wire (p : Pos) (n : Ident) (ty : TypeExpr) : SGoal (.wire p n ty) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hpl, hn⟩, hty⟩ := hp
  have e : (Stmt.wire p n ty).toks ++ t :: R = .keyword "wire" :: .ident n.name ::
      .symbol ":" :: (ty.toks ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.wire p n ty).toks.length = ty.toks.length + 4 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res (Or.inl hpl), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  have w := hw.tail.tail
  refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ w (by decide) (by omega) (by omega))
    fun ty' hty' => ?_
  have w2 := w.tail.drop
  refine Runs.bind (Runs.noDomain (by rw [w2.head]; decide)) fun _ _ => ?_
  refine Runs.sym_bind w2.head (Runs.idx (by omega) (Runs.pure ?_))
  simp [Stmt.erase, Ident.erase_of_name (b := n) hid, hty']

/-! A port: `input` or `output`, a name, and a type. -/
theorem Runs.port {ctx : Ctx} {i f : Nat} {k : Kind} (n : Ident) (ty : TypeExpr)
    (hty : ty.printable = true) (make : Pos → Ident → TypeExpr → Stmt) (t : Kind)
    (R : List Kind) (hw : Win ctx.input i (k :: .ident n.name :: .symbol ":" ::
      (ty.toks ++ .symbol ";" :: t :: R)))
    (hf : 4 * ty.toks.length + 1 ≤ f) (hd : ty.toks.length ≤ ctx.depth) :
    Runs (port f (tokenAt ctx.input i) make) ctx i (i + (ty.toks.length + 4))
      (fun s' => ∃ id ty', id.name = n.name ∧ ty'.erase = ty.erase ∧
        s' = make (tokenAt ctx.input i).pos id ty') := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.port]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  have w := hw.tail.tail
  refine Runs.peek_bind ?_
  simp only [isSym_of w.head]
  reduce_checks
  refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ w (by decide) (by omega) (by omega))
    fun ty' hty' => ?_
  have w2 := w.tail.drop
  refine Runs.bind (Runs.noDomain (by rw [w2.head]; decide)) fun _ _ => ?_
  refine Runs.peek_bind ?_
  simp only [isKw_of w2.head]
  reduce_checks
  exact Runs.sym_bind w2.head (Runs.idx (by omega) (Runs.pure ⟨id, ty', hid, hty', rfl⟩))

theorem Runs.stmt_input (p : Pos) (n : Ident) (ty : TypeExpr) : SGoal (.input p n ty) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hpl, hn⟩, hty⟩ := hp
  have e : (Stmt.input p n ty).toks ++ t :: R = .keyword "input" :: .ident n.name ::
      .symbol ":" :: (ty.toks ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.input p n ty).toks.length = ty.toks.length + 4 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res (Or.inl hpl), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.mono (Runs.port n ty hty _ t R hw (by omega) (by omega)) ?_
  rintro _ ⟨id, ty', hid, hty', rfl⟩
  simp [Stmt.erase, Ident.erase_of_name (b := n) hid, hty']

theorem Runs.stmt_output (p : Pos) (n : Ident) (ty : TypeExpr) : SGoal (.output p n ty) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hpl, hn⟩, hty⟩ := hp
  have e : (Stmt.output p n ty).toks ++ t :: R = .keyword "output" :: .ident n.name ::
      .symbol ":" :: (ty.toks ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.output p n ty).toks.length = ty.toks.length + 4 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res (Or.inl hpl), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.mono (Runs.port n ty hty _ t R hw (by omega) (by omega)) ?_
  rintro _ ⟨id, ty', hid, hty', rfl⟩
  simp [Stmt.erase, Ident.erase_of_name (b := n) hid, hty']

theorem Runs.stmt_inst (p : Pos) (n m : Ident) (xs : List Expr) : SGoal (.inst p n m xs) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true, Bool.not_eq_true', Expr.printableAll_eq,
    List.all_eq_true] at hp
  obtain ⟨⟨⟨hpl, hn⟩, hm⟩, hxs⟩ := hp
  have e : (Stmt.inst p n m xs).toks ++ t :: R = .keyword "instance" :: .ident n.name ::
      .symbol "=" :: .ident m.name :: .symbol "(" :: (argToks (xs.map (Expr.toks 0)) ++
      .symbol ")" :: .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.inst p n m xs).toks.length = (argToks (xs.map (Expr.toks 0))).length + 7 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res (Or.inl hpl), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  have w := hw.tail.tail
  refine Runs.sym_bind w.head ?_
  refine Runs.bind (Runs.path w.tail.head (by rw [w.tail.tail.head]; decide)) fun id' hid' => ?_
  refine Runs.sym_bind w.tail.tail.head ?_
  have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx => ⟨Runs.expr_print x, hxs x hx⟩
  refine Runs.bind (Runs.args (Or.inl rfl) (allowEmpty := true) (top := true) hE (fun _ => rfl)
    ctx _ f _ w.tail.tail.tail (by omega) (fun _ => by omega)) fun ns hns => ?_
  have w2 := w.tail.tail.tail.drop.tail
  refine Runs.peek_bind ?_
  simp only [isKw_of w2.head]
  reduce_checks
  refine Runs.sym_bind w2.head (Runs.idx (by omega) (Runs.pure ?_))
  simp [Stmt.erase, Ident.erase_of_name (b := n) hid, Ident.erase_of_name (b := m) hid',
    List.map_map, Function.comp_def, hns.1]

theorem Runs.stmt_ret_none (p : Pos) : SGoal (.ret p none) := by
  intro ctx i f t R hp hw ht hf hd
  have e : (Stmt.ret p none).toks ++ t :: R = .keyword "return" :: .symbol ";" :: t :: R := by
    simp [Stmt.toks]
  rw [e] at hw
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [Stmt.toks] at hf; omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_kw hw.head (by decide), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.acceptSym_true hw.tail.head) fun b hb => ?_
  subst b
  reduce_checks
  exact Runs.idx (by simp [Stmt.toks]) (Runs.pure (by simp [Stmt.erase]))

theorem EHead.ne_semi {k : Kind} (h : EHead k) : k ≠ .symbol ";" := h.ne_sym (by decide)

theorem Runs.stmt_ret_some (p : Pos) (v : Expr) : SGoal (.ret p (some v)) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Option.all] at hp
  have e : (Stmt.ret p (some v)).toks ++ t :: R =
      .keyword "return" :: (v.toks 0 ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.ret p (some v)).toks.length = (v.toks 0).length + 2 := by
    simp [Stmt.toks]
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_kw hw.head (by decide), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  obtain ⟨k, hk, hek⟩ := Expr.headKind v 0
  refine Runs.bind (Runs.acceptSym_false (by rw [hw.tail.head' hk]; exact hek.ne_semi))
    fun b hb => ?_
  subst b
  reduce_checks
  refine Runs.bind (Runs.value v hp ctx _ f _ _ hw.tail After.semi (by omega) (by omega))
    fun v' hv' => ?_
  refine Runs.sym_bind hw.tail.drop.head (Runs.idx (by omega) (Runs.pure ?_))
  simp [Stmt.erase, hv']

/-! `block` reads the kinds of the body `b` back to `b`, up to positions. -/
def BGoal (b : List Stmt) : Prop :=
  ∀ (ctx : Ctx) (i f : Nat) (R : List Kind), Stmt.printableAll ctx.plainFn b = true →
    Win ctx.input i (Stmt.bodyToks b ++ R) → 4 * (Stmt.bodyToks b).length ≤ f →
    (Stmt.bodyToks b).length ≤ ctx.depth →
    Runs (block f) ctx i (i + (Stmt.bodyToks b).length)
      (fun r => r.map Stmt.erase = b.map Stmt.erase)

theorem After.rparen {c : Nat} : After c (.symbol ")") := After.close (Or.inl rfl)

theorem Runs.stmt_ctIf_none (p : Pos) (c : Expr) (y : List Stmt) (hB : BGoal y) :
    SGoal (.ctIf p c y none) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  obtain ⟨hc, hy⟩ := hp
  have e : (Stmt.ctIf p c y none).toks ++ t :: R = .keyword "comptime" :: .keyword "if" ::
      .symbol "(" :: (c.toks 0 ++ .symbol ")" :: (Stmt.bodyToks y ++ t :: R)) := by
    simp [Stmt.toks]
  have hT : (Stmt.ctIf p c y none).toks.length =
      (c.toks 0).length + (Stmt.bodyToks y).length + 4 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_kw hw.head (by decide), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind (Runs.peek_bind ?_)
  simp only [isKw_of hw.tail.head]
  reduce_checks
  refine Runs.bump_bind (Runs.sym_bind hw.tail.tail.head ?_)
  have w := hw.tail.tail.tail
  refine Runs.bind (Runs.value c hc ctx _ f _ _ w After.rparen (by omega) (by omega))
    fun c' hc' => ?_
  have w2 := w.drop
  refine Runs.sym_bind w2.head ?_
  refine Runs.bind (hB ctx _ f _ hy w2.tail (by omega) (by omega)) fun y' hy' => ?_
  have w3 := w2.tail.drop
  refine Runs.bind (Runs.acceptKw_false (by rw [w3.head]; exact ht)) fun b hb => ?_
  subst b
  reduce_checks
  refine Runs.bind (Runs.pure (Q := (· = none)) rfl) fun o ho => ?_
  subst o
  refine Runs.idx (by omega) (Runs.pure ?_)
  simp [Stmt.erase, hc', hy']

theorem Runs.stmt_ctIf_some (p : Pos) (c : Expr) (y n : List Stmt) (hBy : BGoal y)
    (hBn : BGoal n) : SGoal (.ctIf p c y (some n)) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hc, hy⟩, hn⟩ := hp
  have e : (Stmt.ctIf p c y (some n)).toks ++ t :: R = .keyword "comptime" :: .keyword "if" ::
      .symbol "(" :: (c.toks 0 ++ .symbol ")" :: (Stmt.bodyToks y ++ .keyword "else" ::
      (Stmt.bodyToks n ++ t :: R))) := by
    simp [Stmt.toks]
  have hT : (Stmt.ctIf p c y (some n)).toks.length =
      (c.toks 0).length + (Stmt.bodyToks y).length + (Stmt.bodyToks n).length + 5 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_kw hw.head (by decide), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind (Runs.peek_bind ?_)
  simp only [isKw_of hw.tail.head]
  reduce_checks
  refine Runs.bump_bind (Runs.sym_bind hw.tail.tail.head ?_)
  have w := hw.tail.tail.tail
  refine Runs.bind (Runs.value c hc ctx _ f _ _ w After.rparen (by omega) (by omega))
    fun c' hc' => ?_
  have w2 := w.drop
  refine Runs.sym_bind w2.head ?_
  refine Runs.bind (hBy ctx _ f _ hy w2.tail (by omega) (by omega)) fun y' hy' => ?_
  have w3 := w2.tail.drop
  refine Runs.bind (Runs.acceptKw_true w3.head) fun b hb => ?_
  subst b
  reduce_checks
  refine Runs.map_bind (hBn ctx _ f _ hn w3.tail (by omega) (by omega)) fun n' hn' => ?_
  refine Runs.idx (by omega) (Runs.pure ?_)
  simp [Stmt.erase, hc', hy', hn']

theorem Runs.stmt_ctFor (p : Pos) (x : Ident) (lo hi : Expr) (b : List Stmt) (hB : BGoal b) :
    SGoal (.ctFor p x lo hi b) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨hx, hlo⟩, hhi⟩, hb⟩ := hp
  have e : (Stmt.ctFor p x lo hi b).toks ++ t :: R = .keyword "comptime" :: .keyword "for" ::
      .ident x.name :: .keyword "in" :: (lo.toks 0 ++ .symbol ".." :: (hi.toks 0 ++
      .symbol "{" :: (Stmt.linesToks b ++ .symbol "}" :: t :: R))) := by
    simp [Stmt.toks, Stmt.bodyToks]
  have eb : Stmt.bodyToks b ++ t :: R =
      .symbol "{" :: (Stmt.linesToks b ++ .symbol "}" :: t :: R) := by
    simp [Stmt.bodyToks]
  have hT : (Stmt.ctFor p x lo hi b).toks.length =
      (lo.toks 0).length + (hi.toks 0).length + (Stmt.bodyToks b).length + 5 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_kw hw.head (by decide), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.bump_bind (Runs.peek_bind ?_)
  simp only [isKw_of hw.tail.head]
  reduce_checks
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.ident hw.tail.tail.head) fun id hid => ?_
  refine Runs.kw_bind hw.tail.tail.tail.head ?_
  have w := hw.tail.tail.tail.tail
  refine Runs.bind (Runs.value lo hlo ctx _ f _ _ w After.dots (by omega) (by omega))
    fun lo' hlo' => ?_
  have w2 := w.drop
  refine Runs.sym_bind w2.head ?_
  refine Runs.bind (Runs.value hi hhi ctx _ f _ _ w2.tail After.brace (by omega) (by omega))
    fun hi' hhi' => ?_
  have w3 := w2.tail.drop
  rw [← eb] at w3
  refine Runs.bind (hB ctx _ f _ hb w3 (by omega) (by omega)) fun b' hb' => ?_
  refine Runs.idx (by omega) (Runs.pure ?_)
  simp [Stmt.erase, Ident.erase_of_name (b := x) hid, hlo', hhi', hb']

theorem Runs.stmt_block (p : Pos) (b : List Stmt) (hB : BGoal b) : SGoal (.block p b) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable] at hp
  have hT : (Stmt.block p b).toks = Stmt.bodyToks b := by simp [Stmt.toks]
  rw [hT] at hw hf hd ⊢
  have hk : (tokenAt ctx.input i).kind = .symbol "{" := hw.head' (by simp [Stmt.bodyToks])
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_nkw (ctx := ctx) (tok := tokenAt ctx.input i) (by simp [hk]), hk,
    Bool.false_eq_true, ite_false]
  refine Runs.bind (hB ctx i f _ hp hw (by omega) hd) fun b' hb' => Runs.pure ?_
  simp [Stmt.erase, hb']

/-! A statement that starts with an expression and with no name: an expression statement. -/
theorem Runs.stmt_fallback {ctx : Ctx} {i f l : Nat} {k : Kind} {Q : Stmt → Prop}
    (hk : (tokenAt ctx.input i).kind = k) (hE : EHead k) (hn : ∀ n, k ≠ .ident n)
    (h : Runs (Parse.value f >>= fun e => sym ";" >>= fun _ =>
      Pure.pure (Stmt.expr (tokenAt ctx.input i).pos e)) ctx i l Q) :
    Runs (stmt (f + 1)) ctx i l Q := by
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  have hres : (ctx.plainFn && resourceKeywords.any fun x => isKw x (tokenAt ctx.input i)) =
      false := by
    refine stmt_res (Or.inr fun w hw => ?_)
    rw [hk]
    refine hE.ne_kw ?_
    simp only [resourceKeywords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [hres, Bool.false_eq_true, ite_false]
  generalize (tokenAt ctx.input i).kind = K at hk
  subst hk
  split
  all_goals first
    | exact h
    | exact absurd rfl (hE.ne_kw (by decide))
    | exact absurd rfl (hE.ne_sym (by decide))
    | exact absurd rfl (hn _)

/-! A statement that starts with a name. -/
theorem Runs.stmt_ident {ctx : Ctx} {i f j l : Nat} {n : String} {Q : Stmt → Prop}
    {P' : Node × Bool → Prop} (hk : (tokenAt ctx.input i).kind = .ident n)
    (hpost : Runs (postfixExpr f) ctx i j P')
    (hplace : ∀ e pl, P' (e, pl) → Runs (placeStmt f (tokenAt ctx.input i).pos e pl) ctx j l Q) :
    Runs (stmt (f + 1)) ctx i l Q := by
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_nkw (ctx := ctx) (tok := tokenAt ctx.input i) (by simp [hk]), hk,
    Bool.false_eq_true, ite_false]
  refine Runs.bind hpost ?_
  rintro ⟨e, pl⟩ h
  exact hplace e pl h

theorem Runs.stmt_expr (p : Pos) (v : Expr) : SGoal (.expr p v) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable] at hp
  have e : (Stmt.expr p v).toks ++ t :: R = v.toks 0 ++ .symbol ";" :: t :: R := by
    simp [Stmt.toks]
  have hT : (Stmt.expr p v).toks.length = (v.toks 0).length + 1 := by simp [Stmt.toks]
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨k, hk, hek⟩ := Expr.headKind v 0
  have hk0 := hw.head' hk
  by_cases hid : ∃ n, k = .ident n
  · obtain ⟨n, rfl⟩ := hid
    obtain ⟨T1, hT1, htok, hpost⟩ :=
      Runs.postfix_climb v hp ⟨n, hk⟩ ctx i f _ (t :: R) hw After.semi (by omega)
    refine Runs.stmt_ident hk0 hpost ?_
    rintro e pl ⟨-, hclimb⟩
    rw [Parse.placeStmt]
    refine Runs.peek_bind ?_
    have h1 : isSym "=" (tokenAt ctx.input (i + T1)) = false ∧
        isSym ":=" (tokenAt ctx.input (i + T1)) = false := by
      rcases htok with h | ⟨op, h⟩
      · simp [isSym, h]
      · simp only [isSym, h, Kind.beq_eq]; cases op <;> decide
    simp only [h1.1, h1.2, Bool.or_false, Bool.false_eq_true, ite_false]
    refine Runs.bind (hclimb _) fun n' hn' => ?_
    refine Runs.bind (Runs.checkHeight (by have := hn'.2; omega)) fun _ _ => ?_
    refine Runs.sym_bind hw.drop.head (Runs.pure ?_)
    simp [Stmt.erase, hn'.1]
  · refine Runs.stmt_fallback hk0 hek (fun n h => hid ⟨n, h⟩) ?_
    refine Runs.bind (Runs.value v hp ctx i f _ _ hw After.semi (by omega) (by omega))
      fun v' hv' => ?_
    refine Runs.sym_bind hw.drop.head (Runs.pure ?_)
    simp [Stmt.erase, hv']

theorem Expr.place_level {e : Expr} (h : e.place = true) : e.level = 11 := by
  cases e <;> simp_all [Expr.place, Expr.level, postfixLevel]

theorem Expr.toks_place {e : Expr} (h : e.place = true) (c : Nat) (hc : c ≤ 11) :
    e.toks c = e.toks 0 :=
  Expr.toks_noparen (by rw [Expr.place_level h]; omega)

theorem Expr.place_head (e : Expr) : e.place = true → ∃ n, (e.toks 0).head? = some (.ident n) := by
  induction e using Expr.ind with
  | case4 p n => intro _; exact ⟨n, by simp [Expr.toks, Expr.level, postfixLevel]⟩
  | case10 p b m ihb =>
    intro h
    simp only [Expr.place] at h
    obtain ⟨n, hn⟩ := ihb h
    refine ⟨n, ?_⟩
    rw [← Expr.toks_place (e := .field p b m) (by simpa [Expr.place] using h) 11 (Nat.le_refl _),
      Expr.toks11_field, Expr.toks_place h 11 (Nat.le_refl _)]
    exact head?_append_of hn
  | case9 p b xs ihb _ =>
    intro h
    simp only [Expr.place] at h
    obtain ⟨n, hn⟩ := ihb h
    refine ⟨n, ?_⟩
    rw [← Expr.toks_place (e := .index p b xs) (by simpa [Expr.place] using h) 11
      (Nat.le_refl _), Expr.toks11_index, Expr.toks_place h 11 (Nat.le_refl _)]
    exact head?_append_of hn
  | case14 p b q k ihb =>
    intro h
    simp only [Expr.place] at h
    obtain ⟨n, hn⟩ := ihb h
    refine ⟨n, ?_⟩
    have h11 : (Expr.select p b q k).toks 0 = b.toks 11 ++ [.symbol ".", .number k] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [h11, Expr.toks_place h 11 (Nat.le_refl _)]
    exact head?_append_of hn
  | _ => intro h; simp [Expr.place] at h

/-! An assignment or a connection: a place, `=` or `:=`, a value, and `;`. -/
theorem Runs.stmt_place {ctx : Ctx} {i f : Nat} {t : Kind} {R : List Kind} (p : Pos)
    (tg v : Expr) (sy : String) (hsy : sy = "=" ∨ sy = ":=") (hpl : tg.place = true)
    (hpt : tg.printable = true) (hv : v.printable = true)
    (hw : Win ctx.input i (tg.toks 0 ++ .symbol sy :: (v.toks 0 ++ .symbol ";" :: t :: R)))
    (hf : 4 * ((tg.toks 0).length + (v.toks 0).length + 2) + 3 ≤ f)
    (hd : (tg.toks 0).length + (v.toks 0).length + 2 ≤ ctx.depth) :
    Runs (stmt (f + 1)) ctx i (i + ((tg.toks 0).length + (v.toks 0).length + 2))
      (fun s' => s'.erase =
        (if sy = "=" then Stmt.assign p tg v else Stmt.connect p tg v).erase) := by
  obtain ⟨n, hn⟩ := Expr.place_head tg hpl
  have hk0 := hw.head' hn
  have hsy' : (tokenAt ctx.input (i + (tg.toks 0).length)).kind = .symbol sy := hw.drop.head
  have h11 := Expr.toks_place hpl 11 (Nat.le_refl _)
  have hpost := Runs.postfix_end tg hpt (fun x _ => Runs.expr_print x) ctx i f (.symbol sy) _
    (by rw [h11]; exact hw) (by rcases hsy with rfl | rfl <;> decide)
    (by rcases hsy with rfl | rfl <;> decide) (by rw [h11]; omega)
  rw [h11] at hpost
  refine Runs.stmt_ident hk0 hpost ?_
  rintro e pl ⟨hres, hpl'⟩
  simp only at hpl'
  subst pl
  rw [Parse.placeStmt]
  refine Runs.peek_bind ?_
  have hc : (isSym "=" (tokenAt ctx.input (i + (tg.toks 0).length)) ||
      isSym ":=" (tokenAt ctx.input (i + (tg.toks 0).length))) = true := by
    rcases hsy with rfl | rfl <;> simp [isSym, hsy']
  simp only [hc, hpl, ite_true]
  reduce_checks
  simp only at hres
  refine Runs.bind (Runs.checkHeight (by have := hres.2; omega)) fun _ _ => ?_
  refine Runs.bump_bind ?_
  have w := hw.drop.tail
  refine Runs.bind (Runs.value v hv ctx _ f _ _ w After.semi (by omega) (by omega))
    fun v' hv' => ?_
  refine Runs.sym_bind w.drop.head (Runs.idx (by omega) (Runs.pure ?_))
  rcases hsy with rfl | rfl
  · simp [isSym, hsy', Stmt.erase, hres.1, hv']
  · simp [isSym, hsy', Stmt.erase, hres.1, hv']

theorem Runs.stmt_assign (p : Pos) (tg v : Expr) : SGoal (.assign p tg v) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hpl, hpt⟩, hv⟩ := hp
  have e : (Stmt.assign p tg v).toks ++ t :: R =
      tg.toks 0 ++ .symbol "=" :: (v.toks 0 ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.assign p tg v).toks.length = (tg.toks 0).length + (v.toks 0).length + 2 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simpa using Runs.stmt_place p tg v "=" (Or.inl rfl) hpl hpt hv hw (by omega) hd

theorem Runs.stmt_connect (p : Pos) (tg v : Expr) : SGoal (.connect p tg v) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hpl, hpt⟩, hv⟩ := hp
  have e : (Stmt.connect p tg v).toks ++ t :: R =
      tg.toks 0 ++ .symbol ":=" :: (v.toks 0 ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.connect p tg v).toks.length = (tg.toks 0).length + (v.toks 0).length + 2 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simpa using Runs.stmt_place p tg v ":=" (Or.inr rfl) hpl hpt hv hw (by omega) hd

/-! `aliasDecl` reads `type N = T;` at an item or a statement. -/
theorem Runs.aliasDecl {α : Type} (n : Ident) (ty : TypeExpr) (hty : ty.printable = true)
    (ctx : Ctx) (i f : Nat) (start : Pos) (make : Pos → Ident → TypeExpr → α) (R : List Kind)
    (hw : Win ctx.input i (.keyword "type" :: .ident n.name :: .symbol "=" ::
      (ty.toks ++ .symbol ";" :: R)))
    (hf : 4 * ty.toks.length ≤ f) (hd : ty.toks.length ≤ ctx.depth) :
    Runs (aliasDecl f start make) ctx i (i + (ty.toks.length + 4))
      (fun r => ∃ id ty', id.name = n.name ∧ ty'.erase = ty.erase ∧ r = make start id ty') := by
  unfold Parse.aliasDecl
  refine Runs.kw_bind hw.head ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  refine Runs.sym_bind hw.tail.tail.head ?_
  have w := hw.tail.tail.tail
  refine Runs.bind (Runs.typeTop ty hty ctx _ f _ _ w (by decide) hf hd) fun ty' hty' => ?_
  exact Runs.sym_bind w.drop.head (Runs.idx (by omega) (Runs.pure ⟨id, ty', hid, hty', rfl⟩))

theorem Runs.stmt_alias (p : Pos) (n : Ident) (ty : TypeExpr) : SGoal (.alias p n ty) := by
  intro ctx i f t R hp hw ht hf hd
  simp only [Stmt.printable, Bool.and_eq_true] at hp
  have e : (Stmt.alias p n ty).toks ++ t :: R = .keyword "type" :: .ident n.name ::
      .symbol "=" :: (ty.toks ++ .symbol ";" :: t :: R) := by
    simp [Stmt.toks]
  have hT : (Stmt.alias p n ty).toks.length = ty.toks.length + 4 := by
    simp [Stmt.toks] <;> omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.stmt]
  refine Runs.peek_bind (Runs.read_bind ?_)
  simp only [stmt_res_kw hw.head (by decide), hw.head, Bool.false_eq_true, ite_false]
  refine Runs.mono (Runs.aliasDecl n ty hp.2 ctx i f _ _ _ hw (by omega) (by omega)) ?_
  rintro _ ⟨id, ty', hid, hty', rfl⟩
  simp [Stmt.erase, Ident.erase_of_name (b := n) hid, hty']

/-! ## Blocks -/

/-! The first kind of a statement: no `else`, no `}`, and no `eof`. -/
theorem Stmt.headKind (s : Stmt) : ∃ k, s.toks.head? = some k ∧ k ≠ .keyword "else" ∧
    k ≠ .symbol "}" ∧ k ≠ .eof := by
  have hE : ∀ (e : Expr) (rest : List Kind), ∃ k, (e.toks 0 ++ rest).head? = some k ∧
      k ≠ .keyword "else" ∧ k ≠ .symbol "}" ∧ k ≠ .eof := by
    intro e rest
    obtain ⟨k, hk, he⟩ := Expr.headKind e 0
    exact ⟨k, head?_append_of hk, he.ne_kw (by decide), he.ne_sym (by decide), he.ne_eof⟩
  cases s with
  | assign p t v => simpa [Stmt.toks] using hE t (.symbol "=" :: (v.toks 0 ++ [.symbol ";"]))
  | connect p t v => simpa [Stmt.toks] using hE t (.symbol ":=" :: (v.toks 0 ++ [.symbol ";"]))
  | expr p v => simpa [Stmt.toks] using hE v [.symbol ";"]
  | ctIf p c y o => cases o <;> simp [Stmt.toks]
  | block p b => simp [Stmt.toks, Stmt.bodyToks]
  | ret p o => cases o <;> simp [Stmt.toks]
  | _ => simp [Stmt.toks]

theorem Stmt.toks_ne_nil (s : Stmt) : s.toks ≠ [] := by
  obtain ⟨k, hk, -⟩ := Stmt.headKind s
  intro h; rw [h] at hk; simp at hk

theorem Stmt.linesToks_cons (s : Stmt) (ss : List Stmt) :
    Stmt.linesToks (s :: ss) = s.toks ++ Stmt.linesToks ss := by
  simp [Stmt.linesToks]

theorem Runs.stmts (b : List Stmt) (hS : ∀ s ∈ b, SGoal s) : ∀ (ctx : Ctx) (i f : Nat)
    (R : List Kind) (acc : List Stmt), Stmt.printableAll ctx.plainFn b = true →
    Win ctx.input i (Stmt.linesToks b ++ .symbol "}" :: R) →
    4 * (Stmt.linesToks b).length + 5 ≤ f → (Stmt.linesToks b).length ≤ ctx.depth →
    Runs (stmts f acc) ctx i (i + (Stmt.linesToks b).length + 1)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧ ms.map Stmt.erase = b.map Stmt.erase) := by
  induction b with
  | nil =>
    intro ctx i f R acc _ hw hf _
    simp only [Stmt.linesToks, List.nil_append, List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.stmts]
    refine Runs.peek_bind ?_
    simp only [isSym_of hw.head]
    reduce_checks
    exact Runs.bump_bind (Runs.pure ⟨[], by simp, rfl⟩)
  | cons s ss ih =>
    intro ctx i f R acc hp hw hf hd
    simp only [Stmt.printableAll, Bool.and_eq_true] at hp
    rw [Stmt.linesToks_cons, List.append_assoc] at hw
    simp only [Stmt.linesToks_cons, List.length_append] at hf hd ⊢
    have h1 : 1 ≤ s.toks.length := by
      have := Stmt.toks_ne_nil s; cases h : s.toks <;> simp_all
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨k, hk, hke, hkc, hkf⟩ := Stmt.headKind s
    have hk0 := hw.head' hk
    obtain ⟨t', R', hR, ht'⟩ : ∃ t' R', Stmt.linesToks ss ++ .symbol "}" :: R = t' :: R' ∧
        t' ≠ .keyword "else" := by
      cases ss with
      | nil => exact ⟨.symbol "}", R, by simp [Stmt.linesToks], by decide⟩
      | cons s2 ss2 =>
        obtain ⟨k2, hk2, hk2e, -⟩ := Stmt.headKind s2
        obtain ⟨ks2, hks2⟩ := List.head?_eq_some_iff.1 hk2
        exact ⟨k2, _, by rw [Stmt.linesToks_cons, hks2]; rfl, hk2e⟩
    rw [Parse.stmts]
    refine Runs.peek_bind ?_
    simp only [isSym_of hk0, hk0, decide_eq_false hkc, Bool.false_eq_true, ite_false]
    simp only [show (k == Kind.eof) = false from by rw [Kind.beq_eq]; exact decide_eq_false hkf,
      Bool.false_eq_true, ite_false]
    have hw1 := hw
    rw [hR] at hw1
    refine Runs.bind (hS s (by simp) ctx i f t' R' hp.1 hw1 ht' (by omega) (by omega))
      fun s' hs' => ?_
    have hw2 := hw.drop
    refine Runs.idx (by omega) (Runs.mono (ih (fun x hx => hS x (by simp [hx])) ctx _ f R
      (s' :: acc) hp.2 hw2 (by omega) (by omega)) ?_)
    rintro r ⟨ms, rfl, hms⟩
    exact ⟨s' :: ms, by simp, by simp [hs', hms]⟩

theorem Runs.block_of (b : List Stmt) (hS : ∀ s ∈ b, SGoal s) : BGoal b := by
  intro ctx i f R hp hw hf hd
  have e : Stmt.bodyToks b ++ R = .symbol "{" :: (Stmt.linesToks b ++ .symbol "}" :: R) := by
    simp [Stmt.bodyToks]
  have hT : (Stmt.bodyToks b).length = (Stmt.linesToks b).length + 2 := by
    simp [Stmt.bodyToks]
  rw [e] at hw
  rw [hT] at hf hd ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.block]
  refine Runs.sym_bind hw.head ?_
  refine Runs.idx (by omega) (Runs.mono (Runs.stmts b hS ctx _ f R [] hp hw.tail (by omega)
    (by omega)) ?_)
  rintro r ⟨ms, rfl, hms⟩
  simpa using hms

theorem Stmt.toks_lt_body {b : List Stmt} {x : Stmt} (hx : x ∈ b) :
    x.toks.length < (Stmt.bodyToks b).length := by
  have : x.toks.length ≤ (Stmt.linesToks b).length := by
    induction b with
    | nil => simp at hx
    | cons s ss ih =>
      rw [Stmt.linesToks_cons, List.length_append]
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · have := ih hx; omega
  simp [Stmt.bodyToks]; omega

theorem Runs.stmt_of (s : Stmt) (hIH : ∀ x : Stmt, x.toks.length < s.toks.length → SGoal x) :
    SGoal s := by
  have hB : ∀ b : List Stmt, (Stmt.bodyToks b).length ≤ s.toks.length → BGoal b :=
    fun b hb => Runs.block_of b fun x hx => hIH x (by have := Stmt.toks_lt_body hx; omega)
  cases s with
  | «local» p m n ty v => exact Runs.stmt_local p m n ty v
  | assign p t v => exact Runs.stmt_assign p t v
  | connect p t v => exact Runs.stmt_connect p t v
  | reg p n ty v => exact Runs.stmt_reg p n ty v
  | wire p n ty => exact Runs.stmt_wire p n ty
  | input p n ty => exact Runs.stmt_input p n ty
  | output p n ty => exact Runs.stmt_output p n ty
  | inst p n m xs => exact Runs.stmt_inst p n m xs
  | ret p o => cases o with
    | none => exact Runs.stmt_ret_none p
    | some v => exact Runs.stmt_ret_some p v
  | ctIf p c y o => cases o with
    | none => exact Runs.stmt_ctIf_none p c y (hB y (by simp [Stmt.toks]; omega))
    | some n =>
      exact Runs.stmt_ctIf_some p c y n (hB y (by simp [Stmt.toks]; omega))
        (hB n (by simp [Stmt.toks]; omega))
  | ctFor p x lo hi b => exact Runs.stmt_ctFor p x lo hi b (hB b (by simp [Stmt.toks]; omega))
  | block p b => exact Runs.stmt_block p b (hB b (by simp [Stmt.toks]))
  | expr p v => exact Runs.stmt_expr p v
  | alias p n ty => exact Runs.stmt_alias p n ty

theorem sgoals (n : Nat) : ∀ s : Stmt, s.toks.length < n → SGoal s := by
  induction n with
  | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih => intro s hs; exact Runs.stmt_of s fun x hx => ih x (by omega)

/-!
The statement lemma: `stmt` reads the kinds of a printable statement back to it, up to
positions. It reads exactly its kinds.
-/
theorem Runs.stmt_print (s : Stmt) : SGoal s := sgoals _ s (Nat.lt_succ_self _)

/-! The block lemma: `block` reads the kinds of a printable body back to it. -/
theorem Runs.block_print (b : List Stmt) : BGoal b :=
  Runs.block_of b fun s _ => Runs.stmt_print s

end Silicon.Source.ParsePrint
