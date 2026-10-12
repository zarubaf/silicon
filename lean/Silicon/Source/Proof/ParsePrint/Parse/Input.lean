-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Parse
import Silicon.Source.Proof.ParsePrint.Lex

/-!
The token windows of the parser lemma of `parse_print`.

`Win inp i ks` states that the parser input `inp` holds the token kinds `ks` from the index `i`.
It also gives two results of the bracket pass `Input.of` for each balanced segment of `ks`.
The pass matches the opening bracket of the segment. It finds no `,` directly in a `(` that
holds an expression. `Input.of_win` proves these results for each token list. A window of the
whole file thus gives a window of each part of the file.

The lemmas take a token list with the given kinds and with any positions. The parser puts a
position only into a node or into an error, and `parse_print` erases the positions of the nodes.
-/
namespace Silicon.Source.ParsePrint

open Lex Parse Print

theorem Kind.beq_eq (a b : Kind) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> simp [BEq.beq, instBEqKind.beq]

instance : LawfulBEq Kind where
  eq_of_beq h := by rw [Kind.beq_eq] at h; exact of_decide_eq_true h
  rfl := by intro a; rw [Kind.beq_eq]; exact decide_eq_true rfl

/-! ## Token windows -/

/-! The opening brackets and the closing brackets. -/
def OpenK (k : Kind) : Prop := k = .symbol "(" ∨ k = .symbol "[" ∨ k = .symbol "{"

def CloseK (k : Kind) : Prop := k = .symbol ")" ∨ k = .symbol "]" ∨ k = .symbol "}"

instance (k : Kind) : Decidable (OpenK k) := inferInstanceAs (Decidable (_ ∨ _))
instance (k : Kind) : Decidable (CloseK k) := inferInstanceAs (Decidable (_ ∨ _))

/-!
The bracket depth after `ks` from the depth `d`. It fails at a closing bracket at the depth 0.
If `strict`, it also fails at a `,` at the depth 0.
-/
def scan (strict : Bool) : Nat → List Kind → Option Nat
  | d, [] => some d
  | d, k :: ks =>
    if OpenK k then scan strict (d + 1) ks
    else if CloseK k then
      match d with
      | 0 => none
      | d + 1 => scan strict d ks
    else if k = .symbol "," ∧ strict = true ∧ d = 0 then none
    else scan strict d ks

/-! A balanced segment. -/
def Bal (ks : List Kind) : Prop := scan false 0 ks = some 0

/-! A balanced segment with no `,` at its own depth. -/
def Seg (ks : List Kind) : Prop := scan true 0 ks = some 0

/-!
The parser input holds the kinds `ks` from the index `i`. The bracket pass matches each opening
bracket of `ks` that starts a balanced segment, and it finds no `,` in a `(` of a `Seg`.
-/
structure Win (inp : Input) (i : Nat) (ks : List Kind) : Prop where
  kind : ∀ k (h : k < ks.length), (tokenAt inp (i + k)).kind = ks[k]
  comma : ∀ a m b, ks = a ++ .symbol "(" :: (m ++ .symbol ")" :: b) → Seg m →
    inp.comma.getD (i + a.length) false = false
  close : ∀ a o m c b, ks = a ++ o :: (m ++ c :: b) → OpenK o → CloseK c → Bal m →
    inp.close.getD (i + a.length) inp.tokens.size = i + a.length + 1 + m.length

theorem Win.head {inp : Input} {i : Nat} {k : Kind} {ks : List Kind} (h : Win inp i (k :: ks)) :
    (tokenAt inp i).kind = k := by
  exact h.kind 0 (by simp)

theorem Win.drop {inp : Input} {i : Nat} {a ks : List Kind} (h : Win inp i (a ++ ks)) :
    Win inp (i + a.length) ks where
  kind k hk := by
    have := h.kind (a.length + k) (by simp; omega)
    rw [← Nat.add_assoc] at this
    simpa [List.getElem_append_right] using this
  comma a' m b he hs := by
    have := h.comma (a ++ a') m b (by rw [he, List.append_assoc]) hs
    simpa [Nat.add_assoc] using this
  close a' o m c b he ho hc hb := by
    have := h.close (a ++ a') o m c b (by rw [he, List.append_assoc]) ho hc hb
    simpa [Nat.add_assoc] using this

theorem Win.tail {inp : Input} {i : Nat} {k : Kind} {ks : List Kind} (h : Win inp i (k :: ks)) :
    Win inp (i + 1) ks :=
  Win.drop (a := [k]) h

/-! ## Transparent segments -/

/-! `ks` leaves each depth as it is, and it never fails. -/
def Trans (strict : Bool) (ks : List Kind) : Prop :=
  ∀ d rest, scan strict d (ks ++ rest) = scan strict d rest

/-! `ks` leaves each positive depth as it is. A `,` can occur at its own depth. -/
def Inner (strict : Bool) (ks : List Kind) : Prop :=
  ∀ d rest, scan strict (d + 1) (ks ++ rest) = scan strict (d + 1) rest

theorem Trans.append {s : Bool} {a b : List Kind} (ha : Trans s a) (hb : Trans s b) :
    Trans s (a ++ b) :=
  fun d rest => by rw [List.append_assoc, ha, hb]

theorem Inner.append {s : Bool} {a b : List Kind} (ha : Inner s a) (hb : Inner s b) :
    Inner s (a ++ b) :=
  fun d rest => by rw [List.append_assoc, ha, hb]

theorem Trans.inner {s : Bool} {a : List Kind} (h : Trans s a) : Inner s a :=
  fun d rest => h (d + 1) rest

theorem Trans.nil {s : Bool} : Trans s [] := fun _ _ => rfl

theorem Trans.seg {a : List Kind} (h : Trans true a) : Seg a := by
  have := h 0 []
  simpa [Seg, scan] using this

theorem Trans.bal {a : List Kind} (h : Trans false a) : Bal a := by
  have := h 0 []
  simpa [Bal, scan] using this

theorem Inner.comma {s : Bool} : Inner s [.symbol ","] := fun d rest => by
  simp [scan, OpenK, CloseK]

theorem Trans.comma : Trans false [.symbol ","] := fun d rest => by
  simp [scan, OpenK, CloseK]

theorem Trans.single {s : Bool} {k : Kind}
    (h : k ≠ .symbol "(" ∧ k ≠ .symbol "[" ∧ k ≠ .symbol "{" ∧ k ≠ .symbol ")" ∧
      k ≠ .symbol "]" ∧ k ≠ .symbol "}" ∧ k ≠ .symbol ",") : Trans s [k] := fun d rest => by
  simp [scan, OpenK, CloseK, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2]

theorem Trans.paren {s : Bool} {m : List Kind} (h : Inner s m) :
    Trans s (.symbol "(" :: m ++ [.symbol ")"]) := fun d rest => by
  simp only [List.cons_append, List.append_assoc]
  simp [scan, OpenK, CloseK, h d]

theorem Inner.argToks {s : Bool} {xss : List (List Kind)} (h : ∀ x ∈ xss, Trans s x) :
    Inner s (argToks xss) := by
  induction xss with
  | nil => exact (Trans.nil).inner
  | cons x xs ih =>
    have ih := ih fun y hy => h y (by simp [hy])
    cases xs with
    | nil => simpa [Print.argToks] using (h x (by simp)).inner
    | cons y ys =>
      have := (h x (by simp)).inner.append (Inner.comma.append ih)
      simpa [Print.argToks, List.intercalate_cons_cons] using this

/-! Without `strict`, a list of arguments is transparent: its `,` cannot fail. -/
theorem Trans.argToks {xss : List (List Kind)} (h : ∀ x ∈ xss, Trans false x) :
    Trans false (argToks xss) := by
  induction xss with
  | nil => exact Trans.nil
  | cons x xs ih =>
    have ih := ih fun y hy => h y (by simp [hy])
    cases xs with
    | nil => simpa [Print.argToks] using h x (by simp)
    | cons y ys =>
      have := (h x (by simp)).append (Trans.comma.append ih)
      simpa [Print.argToks, List.intercalate_cons_cons] using this

theorem Expr.trans_paren {s : Bool} (e : Expr) (h : Trans s (e.toks 0)) (c : Nat) :
    Trans s (e.toks c) := by
  rw [Expr.toks_paren]
  split
  · exact Trans.paren h.inner
  · exact h

theorem BinOp.trans {s : Bool} (op : BinOp) : Trans s [.symbol op.text] :=
  Trans.single (by cases op <;> decide)

theorem UnOp.trans {s : Bool} (op : UnOp) : Trans s [.symbol op.text] :=
  Trans.single (by cases op <;> decide)

theorem Expr.trans (s : Bool) (e : Expr) : ∀ c, Trans s (e.toks c) := by
  induction e using Expr.erase.induct with
  | case5 p op a ih =>
    refine Expr.trans_paren _ ?_
    intro d rest
    have h1 := UnOp.trans (s := s) op d
    simp only [List.singleton_append] at h1
    simp [Expr.toks, h1, ih unaryLevel d]
  | case6 p op l r ihl ihr =>
    refine Expr.trans_paren _ ?_
    intro d rest
    have h1 := BinOp.trans (s := s) op d
    simp only [List.singleton_append] at h1
    simp [Expr.toks, h1, ihl _ d, ihr _ d]
  | case7 p c y n ihc ihy ihn =>
    refine Expr.trans_paren _ ?_
    intro d rest
    simp [Expr.toks, scan, OpenK, CloseK, ihc _ (d + 1), ihy _ (d + 1), ihn _ (d + 1)]
  | case8 p f xs ihf ih =>
    refine Expr.trans_paren _ ?_
    have ha := Inner.argToks (xss := xs.map (Expr.toks 0)) (by simpa using fun x hx => ih x hx 0)
    intro d rest
    rw [Expr.toks.eq_def]
    simp only [Nat.not_lt_zero, ite_false]
    split
    · simp [scan, OpenK, CloseK, ihf _ (d + 1), ha d]
    · simp [scan, OpenK, CloseK, ihf _ d, ha d]
  | case9 p b xs ihb ih =>
    refine Expr.trans_paren _ ?_
    have ha := Inner.argToks (xss := xs.map (Expr.toks 0)) (by simpa using fun x hx => ih x hx 0)
    intro d rest
    simp [Expr.toks, scan, OpenK, CloseK, ihb _ d, ha d]
  | case10 p b f ih =>
    refine Expr.trans_paren _ ?_
    intro d rest
    simp [Expr.toks, scan, OpenK, CloseK, ih _ d]
  | case12 p xs ih =>
    refine Expr.trans_paren _ ?_
    have ha := Inner.argToks (xss := xs.map (Expr.toks 0)) (by simpa using fun x hx => ih x hx 0)
    rw [Expr.toks.eq_def]
    simp only [Expr.level, Nat.not_lt_zero, ite_false]
    split
    · simpa using Trans.paren (ha.append Inner.comma)
    · simpa using Trans.paren ha
  | case13 p xs ih =>
    refine Expr.trans_paren _ ?_
    have ha := Inner.argToks (xss := xs.map (Expr.toks 0)) (by simpa using fun x hx => ih x hx 0)
    intro d rest
    simp [Expr.toks, scan, OpenK, CloseK, ha d]
  | case14 p b q i ih =>
    refine Expr.trans_paren _ ?_
    intro d rest
    simp [Expr.toks, scan, OpenK, CloseK, ih _ d]
  | _ =>
    refine Expr.trans_paren _ ?_
    intro d rest
    simp [Expr.toks, scan, OpenK, CloseK]


/-! The arguments of a call or an index are balanced. -/
theorem Bal.args (xs : List Expr) : Bal (argToks (xs.map (Expr.toks 0))) :=
  (Trans.argToks (by simpa using fun x _ => Expr.trans false x 0)).bal

/-! ## The bracket pass -/

/-!
One step of the loop of `Input.of`, on the close array, the comma array, the semicolon array,
and the stack.
-/
def stepT (t : Token) (i : Nat) (s : Array Nat × Array Bool × Array Bool × List Nat) :
    Array Nat × Array Bool × Array Bool × List Nat :=
  if opening t then (s.1, s.2.1, s.2.2.1, i :: s.2.2.2)
  else if closing t then
    match s.2.2.2 with
    | j :: rest => (s.1.set! j i, s.2.1, s.2.2.1, rest)
    | [] => s
  else if isSym "," t then
    match s.2.2.2 with
    | j :: _ => (s.1, s.2.1.set! j true, s.2.2.1, s.2.2.2)
    | [] => s
  else if isSym ";" t then
    match s.2.2.2 with
    | j :: _ => (s.1, s.2.1, s.2.2.1.set! j true, s.2.2.2)
    | [] => s
  else s

def stepB (ts : Array Token) (s : Array Nat × Array Bool × Array Bool × List Nat) (i : Nat) :
    Array Nat × Array Bool × Array Bool × List Nat :=
  stepT (ts.getD i ⟨⟨0, 0⟩, .eof⟩) i s

theorem forIn'_id_foldl {β : Type} {l : List Nat}
    (f : (a : Nat) → a ∈ l → β → Id (ForInStep β)) (g : β → Nat → β)
    (h : ∀ a m b, f a m b = pure (.yield (g b a))) (init : β) :
    forIn' l init f = pure (l.foldl g init) := by
  have : f = fun a m b => pure (.yield (g b a)) := by funext a m b; exact h a m b
  subst this
  rw [List.forIn'_pure_yield_eq_foldl]
  simp

/-! The state after the loop of `Input.of`. -/
def bracketState (ts : Array Token) : Array Nat × Array Bool × Array Bool × List Nat :=
  (List.range ts.size).foldl (stepB ts)
    (Array.replicate ts.size ts.size, Array.replicate ts.size false,
      Array.replicate ts.size false, [])

/-! The loop of `Input.of` is a fold of `stepB`. -/
theorem Input.of_eq (ts : Array Token) :
    Input.of ts = ⟨ts, (bracketState ts).1, (bracketState ts).2.1, (bracketState ts).2.2.1⟩ := by
  unfold Input.of
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [forIn'_id_foldl _ (stepB ts)]
  · rfl
  · intro a m s
    have ha : a < ts.size := by simpa using m
    have : ts.getD a ⟨⟨0, 0⟩, .eof⟩ = ts[a] := by simp [Array.getD, ha]
    obtain ⟨c, cm, sm, o⟩ := s
    simp only [stepB, stepT, this]
    split
    · rfl
    · split
      · cases o <;> rfl
      · split
        · cases o <;> rfl
        · split
          · cases o <;> rfl
          · rfl

theorem Input.of_tokens (ts : Array Token) : (Input.of ts).tokens = ts := rfl

theorem getD_set_ne {α : Type} {a : Array α} {x j : Nat} {v d : α} (h : x ≠ j) :
    (a.set! x v).getD j d = a.getD j d := by
  unfold Array.getD Array.set!
  by_cases hj : j < a.size
  · simp [hj, h]
  · simp [hj]

theorem getD_set_self {α : Type} {a : Array α} {j : Nat} {v d : α} (h : j < a.size) :
    (a.set! j v).getD j d = v := by
  unfold Array.getD Array.set!
  simp [h]

/-! A step keeps the comma flag at `j` if it sets no flag at `j`. -/
theorem stepT_comma (t : Token) (s : Array Nat × Array Bool × Array Bool × List Nat) (i j : Nat)
    (h : opening t = false → closing t = false → isSym "," t = true → s.2.2.2.head? ≠ some j) :
    (stepT t i s).2.1.getD j false = s.2.1.getD j false := by
  obtain ⟨c, cm, sm, o⟩ := s
  cases o with
  | nil =>
    by_cases h1 : opening t = true <;> by_cases h2 : closing t = true <;>
    by_cases h3 : isSym "," t = true <;> by_cases h4 : isSym ";" t = true <;>
    simp only [stepT, h1, h2, h3, h4] <;> rfl
  | cons x o =>
    by_cases h1 : opening t = true <;> by_cases h2 : closing t = true <;>
    by_cases h3 : isSym "," t = true <;> by_cases h4 : isSym ";" t = true <;>
    try (simp only [stepT, h1, h2, h3, h4]; rfl)
    all_goals
      have hx : x ≠ j := by simpa [h1, h2, h3] using h
      simp only [stepT, h1, h2, h3, Bool.false_eq_true, ite_false, ite_true, getD_set_ne hx]

/-! A step keeps the match at `j` if it closes no bracket at `j`. -/
theorem stepT_close (t : Token) (s : Array Nat × Array Bool × Array Bool × List Nat)
    (i j d : Nat)
    (h : opening t = false → closing t = true → s.2.2.2.head? ≠ some j) :
    (stepT t i s).1.getD j d = s.1.getD j d := by
  obtain ⟨c, cm, sm, o⟩ := s
  cases o with
  | nil =>
    by_cases h1 : opening t = true <;> by_cases h2 : closing t = true <;>
    by_cases h3 : isSym "," t = true <;> by_cases h4 : isSym ";" t = true <;>
    simp only [stepT, h1, h2, h3, h4] <;> rfl
  | cons x o =>
    by_cases h1 : opening t = true <;> by_cases h2 : closing t = true <;>
    try (simp only [stepT, h1, h2]; rfl)
    · have hx : x ≠ j := by simpa [h1, h2] using h
      simp only [stepT, h1, h2, Bool.false_eq_true, ite_false, ite_true, getD_set_ne hx]
    · by_cases h3 : isSym "," t = true <;> by_cases h4 : isSym ";" t = true <;>
        simp only [stepT, h1, h2, h3, h4] <;> rfl

theorem stepT_close_self (t : Token) (s : Array Nat × Array Bool × Array Bool × List Nat)
    (i j d : Nat)
    (h1 : opening t = false) (h2 : closing t = true) (hj : s.2.2.2.head? = some j)
    (hs : j < s.1.size) : (stepT t i s).1.getD j d = i := by
  obtain ⟨c, cm, sm, o⟩ := s
  cases o with
  | nil => cases hj
  | cons x o =>
    simp only [List.head?_cons, Option.some.injEq] at hj
    subst hj
    simp only [stepT, h1, h2, Bool.false_eq_true, ite_false, ite_true]
    exact getD_set_self hs

theorem stepT_size (t : Token) (s : Array Nat × Array Bool × Array Bool × List Nat) (i : Nat) :
    (stepT t i s).1.size = s.1.size := by
  obtain ⟨c, cm, sm, o⟩ := s
  cases o <;> by_cases h1 : opening t = true <;> by_cases h2 : closing t = true <;>
    by_cases h3 : isSym "," t = true <;> by_cases h4 : isSym ";" t = true <;>
    simp [stepT, h1, h2, h3, h4]

theorem stepT_stack (t : Token) (s : Array Nat × Array Bool × Array Bool × List Nat) (i : Nat) :
    (stepT t i s).2.2.2 = if opening t then i :: s.2.2.2
      else if closing t then s.2.2.2.tail else s.2.2.2 := by
  obtain ⟨c, cm, sm, o⟩ := s
  cases o <;> by_cases h1 : opening t = true <;> by_cases h2 : closing t = true <;>
    by_cases h3 : isSym "," t = true <;> by_cases h4 : isSym ";" t = true <;>
    simp only [stepT, h1, h2, h3, h4] <;> rfl

theorem foldl_range_succ {β : Type} (g : β → Nat → β) (init : β) (k : Nat) :
    (List.range (k + 1)).foldl g init = g ((List.range k).foldl g init) k := by
  rw [List.range_succ, List.foldl_append]; rfl

theorem scan_append (st : Bool) (d : Nat) (a b : List Kind) :
    scan st d (a ++ b) = (scan st d a).bind (scan st · b) := by
  induction a generalizing d with
  | nil => rfl
  | cons k a ih =>
    simp only [List.cons_append, scan]
    split
    · exact ih _
    · split
      · cases d with
        | zero => rfl
        | succ d => exact ih _
      · split
        · rfl
        · exact ih _

theorem scan_strict (d d' : Nat) (l : List Kind) (h : scan true d l = some d') :
    scan false d l = some d' := by
  induction l generalizing d with
  | nil => exact h
  | cons k l ih =>
    simp only [scan] at h ⊢
    split
    · simp_all
    · split
      · rename_i h1 h2
        simp only [h1, h2, ite_false, ite_true] at h
        cases d with
        | zero => cases h
        | succ d => exact ih _ h
      · rename_i h1 h2
        simp only [h1, h2, ite_false] at h
        split at h
        · cases h
        · simp; exact ih _ h

theorem Seg.bal {m : List Kind} (h : Seg m) : Bal m := scan_strict 0 0 m h

theorem opening_eq (t : Token) : opening t = decide (OpenK t.kind) := by
  unfold opening OpenK
  rw [Kind.beq_eq, Kind.beq_eq, Kind.beq_eq]
  by_cases h1 : t.kind = .symbol "(" <;> by_cases h2 : t.kind = .symbol "[" <;>
    by_cases h3 : t.kind = .symbol "{" <;> simp [h1, h2, h3]

theorem closing_eq (t : Token) : closing t = decide (CloseK t.kind) := by
  unfold closing CloseK
  rw [Kind.beq_eq, Kind.beq_eq, Kind.beq_eq]
  by_cases h1 : t.kind = .symbol ")" <;> by_cases h2 : t.kind = .symbol "]" <;>
    by_cases h3 : t.kind = .symbol "}" <;> simp [h1, h2, h3]

theorem isSym_eq (s : String) (t : Token) : isSym s t = decide (t.kind = .symbol s) := by
  simp only [isSym, Kind.beq_eq]

theorem OpenK.not_close {k : Kind} (h : OpenK k) : ¬ CloseK k := by
  unfold OpenK at h; unfold CloseK; rcases h with rfl | rfl | rfl <;> decide

theorem CloseK.not_open {k : Kind} (h : CloseK k) : ¬ OpenK k := fun h' => h'.not_close h

/-! The prefixes of a segment that does not fail do not fail. -/
theorem scan_take_ne (st : Bool) (m : List Kind) (hm : scan st 0 m = some 0) (r : Nat) :
    scan st 0 (m.take r) ≠ none := by
  intro h
  have := congrArg (scan st 0) (List.take_append_drop r m)
  rw [scan_append, h, hm] at this
  cases this

/-!
The bracket pass on a segment `o m c` with balanced `m`: the match of `o` is `c`. If `m` is a
`Seg`, then the comma flag of `o` stays false.
-/
theorem Input.of_seg (toks : List Token) (a m b : List Kind) (o c : Kind)
    (he : toks.map Token.kind = a ++ o :: (m ++ c :: b)) (ho : OpenK o) (hc : CloseK c)
    (hb : Bal m) :
    (Input.of toks.toArray).close.getD a.length toks.length = a.length + 1 + m.length ∧
      (Seg m → (Input.of toks.toArray).comma.getD a.length false = false) := by
  let ts := toks.toArray
  let init : Array Nat × Array Bool × Array Bool × List Nat :=
    (Array.replicate ts.size ts.size, Array.replicate ts.size false,
      Array.replicate ts.size false, [])
  let S : Nat → Array Nat × Array Bool × Array Bool × List Nat := fun k =>
    (List.range k).foldl (stepB ts) init
  have hS : ∀ k, S (k + 1) = stepT (ts.getD k ⟨⟨0, 0⟩, .eof⟩) k (S k) := fun k =>
    foldl_range_succ _ _ k
  have hsize : ∀ k, (S k).1.size = toks.length := by
    intro k
    induction k with
    | zero => simp [S, init, ts]
    | succ k ih => rw [hS, stepT_size, ih]
  have hn : toks.length = a.length + 1 + m.length + 1 + b.length := by
    have := congrArg List.length he; simp at this; omega
  have hk? : ∀ i, i < toks.length → some (ts.getD i ⟨⟨0, 0⟩, .eof⟩).kind =
      (a ++ o :: (m ++ c :: b))[i]? := by
    intro i hi; rw [← he]; simp [ts, Array.getD, hi]
  let j := a.length
  have hkj : (ts.getD j ⟨⟨0, 0⟩, .eof⟩).kind = o := by
    have := hk? j (by omega); simpa [j] using this
  have hkm : ∀ r (hr : r < m.length), (ts.getD (j + 1 + r) ⟨⟨0, 0⟩, .eof⟩).kind = m[r] := by
    intro r hr
    have := hk? (j + 1 + r) (by omega)
    have e2 : (a ++ o :: (m ++ c :: b))[j + 1 + r]? = some m[r] := by
      rw [show j + 1 + r = a.length + (r + 1) by omega, List.getElem?_append_right (by omega),
        show a.length + (r + 1) - a.length = r + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_left hr, List.getElem?_eq_getElem hr]
    rw [e2] at this
    exact Option.some.inj this
  have hkc : (ts.getD (j + 1 + m.length) ⟨⟨0, 0⟩, .eof⟩).kind = c := by
    have := hk? (j + 1 + m.length) (by omega)
    have e2 : (a ++ o :: (m ++ c :: b))[j + 1 + m.length]? = some c := by
      rw [show j + 1 + m.length = a.length + (m.length + 1) by omega,
        List.getElem?_append_right (by omega),
        show a.length + (m.length + 1) - a.length = m.length + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [e2] at this
    exact Option.some.inj this
  -- Phase 1: before `o`, each index on the stack is below the current index.
  have p1 : ∀ k, k ≤ j → (∀ x ∈ (S k).2.2.2, x < k) ∧ (S k).2.1.getD j false = false ∧
      (S k).1.getD j toks.length = toks.length := by
    intro k
    induction k with
    | zero => intro _; exact ⟨by simp [S, init], by simp [S, init, Array.getD],
        by simp [S, init, ts, Array.getD]⟩
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
      rw [hS]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [stepT_stack] at hx
        split at hx
        · simp only [List.mem_cons] at hx; rcases hx with rfl | hx
          · omega
          · have := ih1 x hx; omega
        · split at hx
          · have := ih1 x (List.mem_of_mem_tail hx); omega
          · have := ih1 x hx; omega
      · rw [stepT_comma _ _ _ _ (fun _ _ _ h => by
          have := ih1 j (List.mem_of_head? h); omega)]
        exact ih2
      · rw [stepT_close _ _ _ _ _ (fun _ _ h => by
          have := ih1 j (List.mem_of_head? h); omega)]
        exact ih3
  obtain ⟨p1s, p1c, p1m⟩ := p1 j (Nat.le_refl _)
  let S0 := (S j).2.2.2
  -- Phase 2: in `m`, the stack holds `j` under the brackets that `m` opens.
  have p2 : ∀ r, r ≤ m.length → ∃ X : List Nat, (S (j + 1 + r)).2.2.2 = X ++ j :: S0 ∧
      (∀ x ∈ X, j < x) ∧ scan false 0 (m.take r) = some X.length ∧
      (S (j + 1 + r)).1.getD j toks.length = toks.length ∧
      (Seg m → (S (j + 1 + r)).2.1.getD j false = false) := by
    intro r
    induction r with
    | zero =>
      intro _
      have hop : opening (ts.getD j ⟨⟨0, 0⟩, .eof⟩) = true := by
        rw [opening_eq, hkj]; simpa using ho
      refine ⟨[], ?_, by simp, by simp [scan], ?_, fun _ => ?_⟩
      · rw [Nat.add_zero, hS, stepT_stack]; simp only [hop, ite_true]; rfl
      · rw [Nat.add_zero, hS, stepT_close _ _ _ _ _ (fun h => by rw [hop] at h; cases h)]
        exact p1m
      · rw [Nat.add_zero, hS, stepT_comma _ _ _ _ (fun h => by rw [hop] at h; cases h)]
        exact p1c
    | succ r ih =>
      intro hr
      obtain ⟨X, hX, hXj, hXs, hXm, hXc⟩ := ih (by omega)
      have hk := hkm r (by omega)
      have hsc : ∀ st, scan st 0 (m.take (r + 1)) = (scan st 0 (m.take r)).bind
          (scan st · [m[r]]) := fun st => by
        rw [List.take_succ_eq_append_getElem (by omega), scan_append]
      have hne := scan_take_ne false m hb (r + 1)
      rw [hsc, hXs] at hne
      simp only [Option.bind_some] at hne
      rw [show j + 1 + (r + 1) = (j + 1 + r) + 1 by omega, hS]
      generalize ts.getD (j + 1 + r) ⟨⟨0, 0⟩, .eof⟩ = t at hk
      rw [hsc, hXs, Option.bind_some]
      by_cases h1 : OpenK m[r]
      · have hop : opening t = true := by rw [opening_eq, hk]; simpa using h1
        refine ⟨(j + 1 + r) :: X, ?_, ?_, by simp [scan, h1], ?_, fun hs => ?_⟩
        · rw [stepT_stack, hX]; simp only [hop, ite_true]; rfl
        · intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
          · omega
          · exact hXj x hx
        · rw [stepT_close _ _ _ _ _ (fun h => by rw [hop] at h; cases h)]; exact hXm
        · rw [stepT_comma _ _ _ _ (fun h => by rw [hop] at h; cases h)]; exact hXc hs
      · have hop : opening t = false := by rw [opening_eq, hk]; simpa using h1
        by_cases h2 : CloseK m[r]
        · have hcl : closing t = true := by rw [closing_eq, hk]; simpa using h2
          simp only [scan, h1, h2, ite_false, ite_true] at hne ⊢
          obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
            cases X with
            | nil => simp at hne
            | cons x X' => exact ⟨x, X', rfl⟩
          have hxj : x ≠ j := by have := hXj x (by simp); omega
          refine ⟨X', ?_, fun y hy => hXj y (by simp [hy]), by simp, ?_, fun hs => ?_⟩
          · rw [stepT_stack, hop, hcl, hX]; rfl
          · rw [stepT_close _ _ _ _ _ (fun _ _ h => by
              rw [hX] at h; simp at h; exact hxj h)]
            exact hXm
          · rw [stepT_comma _ _ _ _ (fun _ h => by rw [hcl] at h; cases h)]; exact hXc hs
        · have hcl : closing t = false := by rw [closing_eq, hk]; simpa using h2
          refine ⟨X, ?_, hXj, ?_, ?_, fun hs => ?_⟩
          · rw [stepT_stack, hop, hcl, hX]; rfl
          · simp [scan, h1, h2]
          · rw [stepT_close _ _ _ _ _ (fun _ h => by rw [hcl] at h; cases h)]; exact hXm
          · rw [stepT_comma _ _ _ _ (fun _ _ h => ?_)]
            · exact hXc hs
            · have hcm : m[r] = .symbol "," := by rw [isSym_eq, hk] at h; simpa using h
              have hne2 := scan_take_ne true m hs (r + 1)
              have hXs2 : scan true 0 (m.take r) = some X.length := by
                obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 (scan_take_ne true m hs r)
                rw [hd', ← Option.some.inj ((scan_strict _ _ _ hd').symm.trans hXs)]
              rw [hsc, hXs2, Option.bind_some] at hne2
              simp only [hcm] at hne2
              simp [scan, OpenK, CloseK] at hne2
              obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
                cases X with
                | nil => simp at hne2
                | cons x X' => exact ⟨x, X', rfl⟩
              rw [hX]
              have := hXj x (by simp)
              simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
              omega
  -- At `c`, the stack is `j` on the stack before `o`, so `c` matches `o`.
  obtain ⟨X, hX, -, hXs, hXm, hXc⟩ := p2 m.length (Nat.le_refl _)
  rw [List.take_length] at hXs
  have hX0 : X = [] := by
    unfold Bal at hb; rw [hb] at hXs; simp at hXs; exact List.eq_nil_of_length_eq_zero hXs.symm
  subst hX0
  have hcl : closing (ts.getD (j + 1 + m.length) ⟨⟨0, 0⟩, .eof⟩) = true := by
    rw [closing_eq, hkc]; simpa using hc
  have hop : opening (ts.getD (j + 1 + m.length) ⟨⟨0, 0⟩, .eof⟩) = false := by
    rw [opening_eq, hkc]; simpa using hc.not_open
  -- Phase 3: after `c`, `j` is never on the stack.
  have p3 : ∀ d, j + 2 + m.length + d ≤ toks.length →
      j ∉ (S (j + 2 + m.length + d)).2.2.2 ∧
      (S (j + 2 + m.length + d)).1.getD j toks.length = j + 1 + m.length ∧
      (Seg m → (S (j + 2 + m.length + d)).2.1.getD j false = false) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, show j + 2 + m.length = (j + 1 + m.length) + 1 by omega, hS]
      refine ⟨?_, ?_, fun hs => ?_⟩
      · rw [stepT_stack, hop, hcl, hX]
        simp only [Bool.false_eq_true, ite_false, ite_true, List.nil_append, List.tail_cons]
        intro hj; have := p1s j hj; omega
      · exact stepT_close_self _ _ _ _ _ hop hcl (by rw [hX]; rfl) (by rw [hsize]; omega)
      · rw [stepT_comma _ _ _ _ (fun _ h => by rw [hcl] at h; cases h)]; exact hXc hs
    | succ d ih =>
      intro hd
      obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
      rw [show j + 2 + m.length + (d + 1) = (j + 2 + m.length + d) + 1 by omega, hS]
      refine ⟨?_, ?_, fun hs => ?_⟩
      · rw [stepT_stack]
        split
        · simp only [List.mem_cons, not_or]; exact ⟨by omega, ih1⟩
        · split
          · exact fun h => ih1 (List.mem_of_mem_tail h)
          · exact ih1
      · rw [stepT_close _ _ _ _ _ (fun _ _ h => ih1 (List.mem_of_head? h))]; exact ih2
      · rw [stepT_comma _ _ _ _ (fun _ _ _ h => ih1 (List.mem_of_head? h))]; exact ih3 hs
  obtain ⟨-, h3m, h3c⟩ := p3 b.length (by omega)
  rw [show j + 2 + m.length + b.length = toks.length by omega] at h3m h3c
  rw [Input.of_eq]
  exact ⟨h3m, h3c⟩

/-! The bracket pass gives a window for the whole token list. -/
theorem Input.of_win (toks : List Token) : Win (Input.of toks.toArray) 0 (toks.map Token.kind) where
  kind k hk := by
    simp only [List.length_map] at hk
    rw [tokenAt, Input.of_tokens]
    simp [Array.getD, hk]
  comma a m b he hs := by
    rw [Nat.zero_add]
    exact (Input.of_seg toks a m b _ _ he (Or.inl rfl) (Or.inl rfl) hs.bal).2 hs
  close a o m c b he ho hc hb := by
    simp only [Nat.zero_add, Input.of_tokens, List.size_toArray]
    exact (Input.of_seg toks a m b o c he ho hc hb).1

/-! The bracket pass on the tokens of a printed file. -/
theorem Input.win_print (items : List Item) (h : Printable items) (N : Nat)
    (hN : (Print.print items).length ≤ N) :
    Win (Input.of (Lex.lex N (Print.print items)).toArray) 0 (Print.toks items ++ [.eof]) := by
  rw [← lex_print items h N hN]
  exact Input.of_win _

end Silicon.Source.ParsePrint
