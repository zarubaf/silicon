-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Erase

/-!
The lexer facts for the lexer lemma of `parse_print`. They describe `Lex.run` on a text that
is a sequence of known parts.

`Lexes D f cs ks` states that the lexer reads the characters `cs` as the token kinds `ks`. It
starts and ends in the mode `top`, so two such parts compose. The characters after `cs` must
satisfy the condition `f`. A word or a number needs a separator after it. A symbol needs a
character that does not make a longer symbol. Each character opens at most one bracket. Thus
the bracket depth stays below the syntax depth `D` if `D` is at least the length of the text.

`glue` is a small checked lexer for the fixed texts of the printer, such as `" = "`. A proof by
`decide` gives the tokens of each such text.
-/
namespace Silicon.Source.ParsePrint

open Lex

/-! The character pairs that `begin` reads as one token or as the start of a comment. -/
def pairs : List (Char × Char) :=
  [('/', '/'), ('/', '*'), (':', '='), (':', ':'), ('-', '>'), ('=', '>'), ('.', '.'),
   ('+', '%'), ('-', '%'), ('*', '%'), ('=', '='), ('!', '='), ('<', '='), ('>', '='),
   ('<', '<'), ('>', '>'), ('&', '&'), ('|', '|')]

/-! The condition on the character after a part. `none` is the end of the text. -/
inductive Follow where
  | any
  | sep
  | sym (c : Char)
  deriving DecidableEq

def Follow.ok : Follow → Option Char → Bool
  | .sep, some c => !identChar c
  | .sym c, some d => !pairs.contains (c, d)
  | _, _ => true

/-! The lexer reads `cs` as the kinds `ks`, if the text after `cs` satisfies `f`. -/
def Lexes (D : Nat) (f : Follow) (cs : List Char) (ks : List Kind) : Prop :=
  ∀ d p acc r, f.ok r.head? = true → d + cs.length ≤ D →
    ∃ d' p' ts, d' ≤ d + cs.length ∧ ts.map Token.kind = ks.reverse ∧
      run D d .top p acc (cs ++ r) = run D d' .top p' (ts ++ acc) r

/-! Each text that starts with `cs` satisfies `f`. -/
def Starts (f : Follow) (cs : List Char) : Prop := ∀ r, f.ok (cs ++ r).head? = true

theorem Lexes.nil {D : Nat} {f : Follow} : Lexes D f [] [] :=
  fun d p acc _ _ _ => ⟨d, p, [], by omega, rfl, rfl⟩

theorem Lexes.append {D : Nat} {f g : Follow} {cs cs' : List Char} {ks ks' : List Kind}
    (h₁ : Lexes D f cs ks) (h₂ : Lexes D g cs' ks') (hs : Starts f cs') :
    Lexes D g (cs ++ cs') (ks ++ ks') := by
  intro d p acc r hr hd
  simp only [List.length_append] at hd
  obtain ⟨d₁, p₁, ts₁, hd₁, hk₁, he₁⟩ := h₁ d p acc (cs' ++ r) (hs r) (by omega)
  obtain ⟨d₂, p₂, ts₂, hd₂, hk₂, he₂⟩ := h₂ d₁ p₁ (ts₁ ++ acc) r hr (by omega)
  refine ⟨d₂, p₂, ts₂ ++ ts₁, by simp only [List.length_append]; omega,
    by simp [hk₁, hk₂], ?_⟩
  rw [List.append_assoc, he₁, he₂, List.append_assoc]

theorem Lexes.mono {D : Nat} {f g : Follow} {cs : List Char} {ks : List Kind}
    (h : Lexes D f cs ks) (hg : ∀ o, g.ok o = true → f.ok o = true) : Lexes D g cs ks :=
  fun d p acc r hr hd => h d p acc r (hg _ hr) hd

theorem Lexes.any {D : Nat} {f : Follow} {cs : List Char} {ks : List Kind}
    (h : Lexes D .any cs ks) : Lexes D f cs ks :=
  h.mono fun _ _ => by simp [Follow.ok]

theorem Starts.any (cs : List Char) : Starts .any cs := fun _ => by simp [Follow.ok]

theorem Starts.append {f : Follow} {cs : List Char} (h : Starts f cs) (cs' : List Char) :
    Starts f (cs ++ cs') := fun r => by rw [List.append_assoc]; exact h _

theorem Starts.cons {f : Follow} {c : Char} (h : f.ok (some c) = true) (cs : List Char) :
    Starts f (c :: cs) := fun _ => h

/-! Facts about characters. -/

theorem val_le {c : Char} {n : UInt32} : n ≤ c.val ↔ n.toNat ≤ c.toNat :=
  UInt32.le_iff_toNat_le

theorem le_val {c : Char} {n : UInt32} : c.val ≤ n ↔ c.toNat ≤ n.toNat :=
  UInt32.le_iff_toNat_le

theorem identStart_facts {c : Char} (h : identStart c = true) :
    whitespace c = false ∧ c ≠ '/' ∧ c ≠ '"' ∧ c.isDigit = false ∧ identChar c = true := by
  simp [identStart, whitespace, identChar, Char.isAlphanum, Char.isDigit, Char.isAlpha,
    Char.isUpper, Char.isLower, ← Char.toNat_inj, val_le, le_val] at h ⊢
  omega

theorem digit_facts {c : Char} (h : c.isDigit = true) :
    whitespace c = false ∧ c ≠ '/' ∧ c ≠ '"' ∧ identStart c = false ∧ identChar c = true ∧
      c ≠ 'x' ∧ c ≠ 'b' ∧ isDigitOf 10 c = true ∧ digitValue c = c.toNat - '0'.toNat := by
  simp [whitespace, identStart, identChar, Char.isAlphanum, Char.isAlpha,
    Char.isUpper, Char.isLower, ← Char.toNat_inj, isDigitOf, digitValue, h, val_le, le_val]
  simp [Char.isDigit, val_le, le_val] at h
  omega

theorem isDigitOf_identChar {r : Nat} {c : Char} (h : isDigitOf r c = true) :
    identChar c = true := by
  simp only [isDigitOf, Bool.and_eq_true] at h
  have := h.1
  simp [identChar, Char.isAlphanum, Char.isDigit, Char.isAlpha,
    Char.isUpper, Char.isLower, val_le, le_val, Char.le_def] at this ⊢
  omega

theorem ofList_pair_beq {c d : Char} {s : String} :
    (String.ofList [c, d] == s) = ([c, d] == s.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← String.toList_inj, String.toList_ofList]

theorem contains_ofList_pair {c d : Char} {l : List String} :
    l.contains (String.ofList [c, d]) = l.any (fun s => [c, d] == s.toList) := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [List.contains_cons, List.any_cons, ih]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← String.toList_inj, String.toList_ofList,
      eq_comm]

/-! A pair outside `pairs` is no comment start and no long symbol. -/
theorem not_pair {c d : Char} (h : pairs.contains (c, d) = false) :
    (String.ofList [c, d] == "//") = false ∧ (String.ofList [c, d] == "/*") = false ∧
      longSymbols.contains (String.ofList [c, d]) = false := by
  simp only [ofList_pair_beq, contains_ofList_pair]
  simpa [pairs, longSymbols] using h

theorem pair_ne {c : Char} {o : Option Char} (h : c ≠ '/') :
    (o.map fun d => String.ofList [c, d]) ≠ some "//" ∧
      (o.map fun d => String.ofList [c, d]) ≠ some "/*" := by
  cases o with
  | none => simp
  | some x =>
    simp only [Option.map_some, ne_eq, Option.some.injEq, ← String.toList_inj,
      String.toList_ofList]
    simp [h]

theorem radixAfter_none {c : Char} {rest : List Char}
    (h : c ≠ '0' ∨ ∀ x, rest.head? = some x → x ≠ 'x' ∧ x ≠ 'b') : radixAfter c rest = none := by
  unfold radixAfter
  split
  · rcases h with h | h
    · simp [h]
    · exact absurd rfl (h 'x' rfl).1
  · rcases h with h | h
    · simp [h]
    · exact absurd rfl (h 'b' rfl).2
  · rfl

/-! Steps of `run`. -/

theorem push_some {ts : List Token} {t : Token} (h : ∀ m, t.kind ≠ .error m) :
    push ts (some t) = .ok (t :: ts) := by
  rcases t with ⟨p, k⟩
  cases k <;> first | rfl | exact absurd rfl (h _)

theorem run_top {D d e : Nat} {p : Pos} {acc acc' : List Token} {c : Char} {cs : List Char}
    {m : Mode} {t t' : Option Token}
    (hb : begin p c cs = (m, t)) (hn : nest D d t = (t', e)) (hp : push acc t' = .ok acc') :
    run D d .top p acc (c :: cs) = run D e m (advance p c) acc' cs := by
  rw [run]; simp only [hb, hn]; rw [show push acc none = .ok acc from rfl]; simp only [hp]

/-! The end of a word or a number at a character that cannot extend it. -/
theorem run_word_end {D d : Nat} {s p : Pos} {acc : List Char} {ts : List Token}
    {r : List Char} (h : Follow.sep.ok r.head? = true) :
    run D d (.word s acc) p ts r = run D d .top p (wordToken s acc :: ts) r := by
  have hp : push ts (some (wordToken s acc)) = .ok (wordToken s acc :: ts) :=
    push_some fun m => by unfold wordToken; dsimp only; split <;> simp
  cases r with
  | nil => rw [run, hp]; rfl
  | cons c cs =>
    simp only [Follow.ok, List.head?_cons, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    rw [run, run]; simp only [h, hp]; rfl

theorem run_word_cons {D d : Nat} {s p : Pos} {acc : List Char} {ts : List Token} {c : Char}
    {cs : List Char} (h : identChar c = true) :
    run D d (.word s acc) p ts (c :: cs) = run D d (.word s (c :: acc)) (advance p c) ts cs := by
  rw [run]; simp only [h, ite_true]

theorem run_word_all {D d : Nat} {s : Pos} {ts : List Token} (cs r : List Char)
    (h : cs.all identChar = true) :
    ∀ acc p, ∃ p', run D d (.word s acc) p ts (cs ++ r) =
      run D d (.word s (cs.reverse ++ acc)) p' ts r := by
  induction cs with
  | nil => intro acc p; exact ⟨p, rfl⟩
  | cons c cs ih =>
    intro acc p
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨p', hp'⟩ := ih h.2 (c :: acc) (advance p c)
    refine ⟨p', ?_⟩
    rw [List.cons_append, run_word_cons h.1, hp']
    simp

def wordKind (s : String) : Kind := if keywords.contains s then .keyword s else .ident s

/-! A word: an identifier or a keyword. -/
theorem Lexes.word {D : Nat} {c : Char} {cs : List Char} (hc : identStart c = true)
    (hcs : cs.all identChar = true) :
    Lexes D .sep (c :: cs) [wordKind (String.ofList (c :: cs))] := by
  intro d p acc r hr hd
  obtain ⟨hw, hsl, hq, -, -⟩ := identStart_facts hc
  have hb : begin p c (cs ++ r) = (.word p [c], none) := by
    have h1 := pair_ne (o := (cs ++ r).head?) hsl
    unfold begin
    simp only [hw, Bool.false_eq_true, ite_false, beq_iff_eq, h1.1, h1.2, hq, hc, ite_true]
  obtain ⟨p', hp'⟩ := run_word_all (D := D) (d := d) (s := p) (ts := acc) cs r hcs [c]
    (advance p c)
  refine ⟨d, p', [wordToken p (cs.reverse ++ [c])], by omega, ?_, ?_⟩
  · simp [wordToken, wordKind]
  · rw [List.cons_append, run_top hb rfl rfl, hp', run_word_end hr]
    rfl

/-! Whitespace. -/
theorem Lexes.ws {D : Nat} {c : Char} (h : whitespace c = true) : Lexes D .any [c] [] := by
  intro d p acc r _ hd
  refine ⟨d, advance p c, [], by omega, rfl, ?_⟩
  have hb : begin p c r = (.top, none) := by simp [begin, h]
  exact run_top hb rfl rfl

/-! A symbol. `shortOk` and `longOk` hold for the symbols that `begin` reads as such. -/
def shortOk (c : Char) : Bool :=
  shortSymbols.contains c && !whitespace c && c != '"' && !identStart c && !c.isDigit

def longOk (c d : Char) : Bool :=
  longSymbols.contains (String.ofList [c, d]) && c != '/' && shortOk c

/-! The condition after a short symbol: only a pair that starts with it is a risk. -/
def symFollow (c : Char) : Follow := if pairs.any (·.1 == c) then .sym c else .any

theorem nest_some {D d : Nat} {t : Token} (hd : d < D) :
    ∃ e, nest D d (some t) = (some t, e) ∧ e ≤ d + 1 := by
  simp only [nest]
  by_cases ho : opening t
  · exact ⟨d + 1, by simp [ho, hd], Nat.le_refl _⟩
  · by_cases hc : closing t
    · exact ⟨d - 1, by simp [ho, hc], by omega⟩
    · exact ⟨d, by simp [ho, hc], by omega⟩

theorem shortOk_facts {c : Char} (h : shortOk c = true) :
    shortSymbols.contains c = true ∧ whitespace c = false ∧ c ≠ '"' ∧ identStart c = false ∧
      c.isDigit = false := by
  simp only [shortOk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem not_pair_follow {c : Char} {r : List Char} (h : (symFollow c).ok r.head? = true) :
    ∀ x, r.head? = some x → pairs.contains (c, x) = false := by
  intro x hx
  rw [hx] at h
  unfold symFollow at h
  split at h
  · simpa [Follow.ok] using h
  · rename_i hn
    cases hc : pairs.contains (c, x)
    · rfl
    · exact absurd (List.any_eq_true.2 ⟨(c, x), by simpa using hc, by simp⟩) hn

theorem begin_short {p : Pos} {c : Char} {rest : List Char} (hc : shortOk c = true)
    (hr : ∀ x, rest.head? = some x → pairs.contains (c, x) = false) :
    begin p c rest = (.top, some ⟨p, .symbol (String.singleton c)⟩) := by
  obtain ⟨hs, hw, hq, hi, hd⟩ := shortOk_facts hc
  have h0 : c ≠ '0' := by rintro rfl; simp at hd
  unfold begin
  cases rest with
  | nil =>
    have hs' : c ∈ shortSymbols := by simpa using hs
    simp [hw, hq, hi, hd, radixAfter, begin.short, hs']
  | cons x xs =>
    obtain ⟨h1, h2, h3⟩ := not_pair (hr x rfl)
    simp only [List.head?_cons, Option.map_some, Option.some_beq_some, h1, h2,
      Bool.false_eq_true, ite_false, hw, beq_iff_eq, hq, hi, radixAfter_none (.inl h0), hd, h3,
      begin.short, hs, ite_true]

theorem Lexes.short {D : Nat} {c : Char} (hc : shortOk c = true) :
    Lexes D (symFollow c) [c] [.symbol (String.singleton c)] := by
  intro d p acc r hr hd
  obtain ⟨e, hn, he⟩ := nest_some (D := D) (d := d) (t := ⟨p, .symbol (String.singleton c)⟩)
    (by simp at hd; omega)
  refine ⟨e, advance p c, [⟨p, .symbol (String.singleton c)⟩], by simp; omega, rfl, ?_⟩
  exact run_top (begin_short hc (not_pair_follow hr)) hn (push_some fun _ => by simp)

theorem Lexes.long {D : Nat} {c x : Char} (hc : longOk c x = true) :
    Lexes D .any [c, x] [.symbol (String.ofList [c, x])] := by
  intro d p acc r _ hd
  simp only [longOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hl, hsl⟩, hs⟩ := hc
  obtain ⟨-, hw, hq, hi, hdg⟩ := shortOk_facts hs
  have h0 : c ≠ '0' := by rintro rfl; simp at hdg
  have hb : begin p c (x :: r) = (.skip .top, some ⟨p, .symbol (String.ofList [c, x])⟩) := by
    have h1 := pair_ne (o := some x) hsl
    simp only [Option.map_some, ne_eq, Option.some.injEq] at h1
    unfold begin
    simp only [List.head?_cons, Option.map_some, hw, Bool.false_eq_true, ite_false, beq_iff_eq,
      Option.some.injEq, h1.1, h1.2, hq, hi, radixAfter_none (.inl h0), hdg, hl, ite_true]
  obtain ⟨e, hn, he⟩ := nest_some (D := D) (d := d)
    (t := ⟨p, .symbol (String.ofList [c, x])⟩) (by simp at hd; omega)
  refine ⟨e, advance (advance p c) x, [⟨p, .symbol (String.ofList [c, x])⟩], by simp; omega,
    rfl, ?_⟩
  simp only [List.cons_append, List.nil_append]
  rw [run_top hb hn (push_some fun _ => by simp), run]

/-! A number in decimal, as the printer writes it. -/

theorem numberValue_dropZeros (r : Nat) (l : List Char) :
    numberValue r (l.dropWhile (· == '0')) = numberValue r l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.dropWhile_cons]
    split
    · rename_i h
      simp only [beq_iff_eq] at h
      subst h
      rw [ih]
      simp [numberValue, digitValue]
    · rfl

theorem numberValue_digits (l : List Char) (h : ∀ c ∈ l, c.isDigit = true) (init : Nat) :
    l.foldl (fun n c => n * 10 + digitValue c) init = Nat.ofDigitChars 10 l init := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons, Nat.ofDigitChars_cons, ih (fun c hc => h c (by simp [hc])),
      (digit_facts (h a (by simp))).2.2.2.2.2.2.2.2, Nat.mul_comm]

theorem run_number_cons {D d rad : Nat} {s p : Pos} {acc : List Char} {ts : List Token}
    {c : Char} {cs : List Char} (h : isDigitOf rad c = true) :
    run D d (.number s rad acc) p ts (c :: cs) =
      run D d (.number s rad (c :: acc)) (advance p c) ts cs := by
  rw [run]; simp only [h, ite_true]

theorem run_number_all {D d rad : Nat} {s : Pos} {ts : List Token} (cs r : List Char)
    (h : cs.all (isDigitOf rad) = true) :
    ∀ acc p, ∃ p', run D d (.number s rad acc) p ts (cs ++ r) =
      run D d (.number s rad (cs.reverse ++ acc)) p' ts r := by
  induction cs with
  | nil => intro acc p; exact ⟨p, rfl⟩
  | cons c cs ih =>
    intro acc p
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨p', hp'⟩ := ih h.2 (c :: acc) (advance p c)
    refine ⟨p', ?_⟩
    rw [List.cons_append, run_number_cons h.1, hp']
    simp

theorem run_number_end {D d rad : Nat} {s p : Pos} {acc : List Char} {ts : List Token}
    {r : List Char} (h : Follow.sep.ok r.head? = true)
    (hk : ∀ m, (numberToken s rad acc).kind ≠ .error m) :
    run D d (.number s rad acc) p ts r = run D d .top p (numberToken s rad acc :: ts) r := by
  have hp := push_some (ts := ts) hk
  cases r with
  | nil => rw [run, hp]; rfl
  | cons c cs =>
    simp only [Follow.ok, List.head?_cons, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    have hd : isDigitOf rad c = false := by
      cases hc : isDigitOf rad c
      · rfl
      · rw [isDigitOf_identChar hc] at h; cases h
    rw [run, run]; simp only [hd, hp, Bool.false_eq_true, ite_false]; rfl

theorem two_pow_lt : 2 ^ 65536 < 10 ^ 19729 := by decide +kernel

theorem numberToken_digits {s : Pos} {v : Nat} (hv : v < 2 ^ 65536) :
    numberToken s 10 (Nat.toDigits 10 v).reverse = ⟨s, .number v⟩ := by
  have hl : (Nat.toDigits 10 v).length ≤ 19729 :=
    (Nat.length_toDigits_le_iff (by decide) (by decide)).2 (Nat.lt_trans hv two_pow_lt)
  have hdig : ∀ c ∈ Nat.toDigits 10 v, c.isDigit = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hval : numberValue 10 ((Nat.toDigits 10 v).dropWhile (· == '0')) = v := by
    rw [numberValue_dropZeros]
    unfold numberValue
    rw [numberValue_digits _ hdig, Nat.ofDigitChars_ten_toDigits]
  unfold numberToken
  simp only [List.reverse_reverse]
  have hlen : ¬ ((Nat.toDigits 10 v).dropWhile (· == '0')).length > maxDigits 10 := by
    have := congrArg List.length
      (List.takeWhile_append_dropWhile (p := (· == '0')) (l := Nat.toDigits 10 v))
    simp only [List.length_append] at this
    show ¬ _ > 19729
    omega
  simp only [hlen, ↓reduceIte, hval, hv]

theorem Lexes.number {D v : Nat} (hv : v < 2 ^ 65536) :
    Lexes D .sep (Nat.toDigits 10 v) [.number v] := by
  intro d p acc r hr hd
  have hdig : ∀ c ∈ Nat.toDigits 10 v, c.isDigit = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  obtain ⟨c, cs, hl⟩ : ∃ c cs, Nat.toDigits 10 v = c :: cs := by
    cases h : Nat.toDigits 10 v with
    | nil => exact absurd h Nat.toDigits_ne_nil
    | cons c cs => exact ⟨c, cs, rfl⟩
  rw [hl] at hdig ⊢
  have hc := digit_facts (hdig c (by simp))
  obtain ⟨hw, hsl, hq, hi, -, -, -, -, -⟩ := hc
  have hcs : cs.all (isDigitOf 10) = true :=
    List.all_eq_true.2 fun x hx => (digit_facts (hdig x (by simp [hx]))).2.2.2.2.2.2.2.1
  have hrad : radixAfter c (cs ++ r) = none := by
    apply radixAfter_none (.inr _)
    intro x hx
    cases cs with
    | cons y ys =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hx
      subst hx
      have := digit_facts (hdig y (by simp))
      exact ⟨this.2.2.2.2.2.1, this.2.2.2.2.2.2.1⟩
    | nil =>
      simp only [List.nil_append] at hx
      rw [hx] at hr
      simp only [Follow.ok, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
      constructor <;> (rintro rfl; simp [identChar] at hr)
  have hb : begin p c (cs ++ r) = (.number p 10 [c], none) := by
    have h1 := pair_ne (o := (cs ++ r).head?) hsl
    unfold begin
    simp only [hw, Bool.false_eq_true, ite_false, beq_iff_eq, h1.1, h1.2, hq, hi, hrad,
      (hdig c (by simp)), ite_true]
  obtain ⟨p', hp'⟩ := run_number_all (D := D) (d := d) (s := p) (ts := acc) cs r hcs [c]
    (advance p c)
  have hk := numberToken_digits (s := p) hv
  rw [hl, List.reverse_cons] at hk
  refine ⟨d, p', [numberToken p 10 (cs.reverse ++ [c])], by omega, by simp [hk], ?_⟩
  rw [List.cons_append, run_top hb rfl rfl, hp', run_number_end hr (by simp [hk])]
  rfl

/-! A string literal, as `quote` writes it. -/

theorem run_string_char {D d : Nat} {st : Pos} {ts : List Token} {ch : Char}
    (h : printableChar ch = true) (rest : List Char) :
    ∀ acc p, ∃ p', run D d (.string st acc false) p ts ((Print.quote.escape ch).toList ++ rest) =
      run D d (.string st (ch :: acc) false) p' ts rest := by
  intro acc p
  unfold Print.quote.escape
  split
  · exact ⟨_, by simp [run, escaped]; rfl⟩
  · exact ⟨_, by simp [run, escaped]; rfl⟩
  · exact ⟨_, by simp [run, escaped]; rfl⟩
  · exact ⟨_, by simp [run, escaped]; rfl⟩
  · exact ⟨_, by simp [run, escaped]; rfl⟩
  · rename_i h1 h2 h3 h4 h5
    have h1' : ch ≠ '"' := h1
    have h2' : ch ≠ '\\' := h2
    have hc : control ch = false := by
      simp only [printableChar, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
      rcases h with ((h | h) | h) | h
      · exact h
      · exact absurd h h3
      · exact absurd h h4
      · exact absurd h h5
    refine ⟨advance p ch, ?_⟩
    rw [String.toList_singleton, List.singleton_append, run]
    simp [h1', h2', hc]

theorem run_string_all {D d : Nat} {st : Pos} {ts : List Token} (l rest : List Char)
    (h : l.all printableChar = true) :
    ∀ acc p, ∃ p', run D d (.string st acc false) p ts
        ((l.flatMap fun c => (Print.quote.escape c).toList) ++ rest) =
      run D d (.string st (l.reverse ++ acc) false) p' ts rest := by
  induction l with
  | nil => intro acc p; exact ⟨p, rfl⟩
  | cons c cs ih =>
    intro acc p
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨p₁, hp₁⟩ := run_string_char (D := D) (d := d) (st := st) (ts := ts) h.1
      ((cs.flatMap fun c => (Print.quote.escape c).toList) ++ rest) acc p
    obtain ⟨p₂, hp₂⟩ := ih h.2 (c :: acc) p₁
    refine ⟨p₂, ?_⟩
    rw [List.flatMap_cons, List.append_assoc, hp₁, hp₂]
    simp

theorem Lexes.string {D : Nat} {s : String} (h : s.toList.all printableChar = true) :
    Lexes D .any (Print.quote s).toList [.string s] := by
  intro d p acc r _ hd
  have hb : begin p '"' ((s.toList.flatMap fun c => (Print.quote.escape c).toList) ++
      (['"'] ++ r)) = (.string p [] false, none) := by
    have h1 := pair_ne (c := '"') (o := ((s.toList.flatMap fun c =>
      (Print.quote.escape c).toList) ++ (['"'] ++ r)).head?) (by decide)
    unfold begin
    simp only [h1.1, h1.2, beq_iff_eq]
    simp [whitespace]
  obtain ⟨p', hp'⟩ := run_string_all (D := D) (d := d) (st := p) (ts := acc) s.toList
    (['"'] ++ r) h [] (advance p '"')
  refine ⟨d, advance p' '"', [⟨p, .string s⟩], by omega, rfl, ?_⟩
  simp only [Print.quote, String.toList_append, String.toList_join, List.flatMap_map]
  have he : ("\"".toList : List Char) = ['"'] := by decide
  rw [he, List.singleton_append, List.append_assoc, List.cons_append, run_top hb rfl rfl]
  rw [hp', List.singleton_append, run]
  simp

/-!
`glue` lexes a fixed text of whitespace, words, and symbols. It fails on each other text, and
on a symbol that the next character could extend. The fuel is the length of the text.
-/
def glue : Nat → List Char → Option (Follow × List Kind)
  | _, [] => some (.any, [])
  | 0, _ :: _ => none
  | n + 1, c :: cs =>
    if whitespace c then glue n cs
    else if identStart c then
      let k := wordKind (String.ofList (c :: cs.takeWhile identChar))
      let rest := cs.dropWhile identChar
      if rest.isEmpty then some (.sep, [k])
      else (glue n rest).map fun (f, ks) => (f, k :: ks)
    else match cs with
      | x :: xs =>
        if longOk c x then
          (glue n xs).map fun (f, ks) => (f, .symbol (String.ofList [c, x]) :: ks)
        else if shortOk c && !pairs.contains (c, x) then
          (glue n (x :: xs)).map fun (f, ks) => (f, .symbol (String.singleton c) :: ks)
        else none
      | [] => if shortOk c then some (symFollow c, [.symbol (String.singleton c)]) else none

theorem head_dropWhile {p : Char → Bool} {l : List Char} {x : Char}
    (h : (l.dropWhile p).head? = some x) : p x = false := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rw [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · rename_i hn
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simpa using hn

theorem glue_sound {D : Nat} :
    ∀ n cs f ks, glue n cs = some (f, ks) → Lexes D f cs ks
  | _, [], f, ks, h => by
    simp only [glue, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Lexes.nil
  | 0, _ :: _, _, _, h => by simp [glue] at h
  | n + 1, c :: cs, f, ks, h => by
    unfold glue at h
    split at h
    · rename_i hw
      have := (Lexes.ws (D := D) hw).append (glue_sound n cs f ks h) (Starts.any _)
      simpa using this
    split at h
    · rename_i _ hi
      have hw : (c :: cs.takeWhile identChar).all identChar = true := by
        simp [(identStart_facts hi).2.2.2.2, List.all_takeWhile]
      have hword := Lexes.word (D := D) hi (List.all_takeWhile (p := identChar) (l := cs))
      have hsplit : c :: cs = (c :: cs.takeWhile identChar) ++ cs.dropWhile identChar := by
        simp [List.takeWhile_append_dropWhile]
      rw [hsplit]
      dsimp only at h
      split at h
      · rename_i he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.isEmpty_iff] at he
        rw [he, List.append_nil]
        exact hword
      · rename_i he
        obtain ⟨⟨f', ks'⟩, hg, hfk⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at hfk
        obtain ⟨rfl, rfl⟩ := hfk
        refine hword.append (glue_sound n _ _ _ hg) ?_
        cases hd : cs.dropWhile identChar with
        | nil => simp [hd] at he
        | cons x xs =>
          apply Starts.cons
          have := head_dropWhile (p := identChar) (l := cs) (x := x) (by simp [hd])
          simp [Follow.ok, this]
    · split at h
      · rename_i x xs
        split at h
        · rename_i hl
          obtain ⟨⟨f', ks'⟩, hg, hfk⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hfk
          obtain ⟨rfl, rfl⟩ := hfk
          have := (Lexes.long (D := D) hl).append (glue_sound n xs _ _ hg) (Starts.any _)
          simpa using this
        · split at h
          · rename_i hs
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
            obtain ⟨⟨f', ks'⟩, hg, hfk⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hfk
            obtain ⟨rfl, rfl⟩ := hfk
            refine (Lexes.short (D := D) hs.1).append (glue_sound n _ _ _ hg) ?_
            apply Starts.cons
            unfold symFollow
            split
            · simp only [Follow.ok, hs.2, Bool.not_false]
            · rfl
          · cases h
      · split at h
        · rename_i hs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Lexes.short hs
        · cases h

/-! The tokens of a fixed text, by `decide` on `glue`. -/
theorem Lexes.glue {D : Nat} {f : Follow} {cs : List Char} {ks : List Kind}
    (h : glue cs.length cs = some (f, ks)) : Lexes D f cs ks :=
  glue_sound _ _ _ _ h

end Silicon.Source.ParsePrint
