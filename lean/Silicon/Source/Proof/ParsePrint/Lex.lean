-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Run
import Silicon.Source.Proof.ParsePrint.Tokens

/-!
The lexer lemma of `parse_print`. For a `Printable` AST and a syntax depth `N` of at least the
length of the printed text, the lexer gives the kinds `Print.toks items`, then `eof`:

```lean
theorem lex_print (items : List Item) (h : Printable items)
    (N : Nat) (hN : (Print.print items).length ≤ N) :
    (Lex.lex N (Print.print items)).map Token.kind = Print.toks items ++ [.eof]
```

The lemma gives the kinds of the tokens, not their positions. The parser uses a position only
in a node or in an error, and `parse_print` erases the positions of the nodes.

The proof goes over the AST. Each node gives `Lexes` for its text. A part that follows a word
or a number starts with a separator. A part that follows a symbol starts with a character
that makes no longer symbol. No pair of `pairs` ends with a character that starts an
expression.
-/
namespace Silicon.Source.ParsePrint

open Lex Print

/-! The first character of the text of an expression. -/
def exprStart (x : Char) : Bool :=
  identStart x || x.isDigit || x == '"' || x == '(' || x == '[' || x == '-' || x == '!' ||
    x == '~'

theorem sym_ok_exprStart {c x : Char} (h : exprStart x = true) :
    (Follow.sym c).ok (some x) = true := by
  simp only [Follow.ok, Bool.not_eq_true']
  cases hc : pairs.contains (c, x)
  · rfl
  · have hm : x ∈ pairs.map Prod.snd := List.mem_map.2 ⟨(c, x), by simpa using hc, rfl⟩
    have hall : ∀ y ∈ pairs.map Prod.snd, exprStart y = false := by decide
    rw [hall x hm] at h
    cases h

/-! A text that starts with an expression satisfies each condition except `sep`. -/
theorem starts_of_exprStart {f : Follow} {cs : List Char} (hf : f ≠ .sep)
    (h : ∃ x xs, cs = x :: xs ∧ exprStart x = true) : Starts f cs := by
  obtain ⟨x, xs, rfl, hx⟩ := h
  cases f with
  | any => exact Starts.any _
  | sep => exact absurd rfl hf
  | sym c => exact Starts.cons (sym_ok_exprStart hx) _

/-! A fixed text that is not empty: its first character decides. -/
theorem Starts.lit {f : Follow} {cs : List Char} (h : cs ≠ [] ∧ f.ok cs.head? = true) :
    Starts f cs := by
  obtain ⟨hne, hok⟩ := h
  cases cs with
  | nil => exact absurd rfl hne
  | cons x xs => exact Starts.cons hok _

/-! A fixed text, then any text. -/
theorem Starts.glue {f : Follow} (s : String) (h : s.toList ≠ [] ∧ f.ok s.toList.head? = true)
    (rest : List Char) : Starts f (s.toList ++ rest) :=
  (Starts.lit h).append rest

theorem validName_cons {n : String} (h : validName n = true) :
    ∃ c cs, n.toList = c :: cs ∧ identStart c = true ∧ cs.all identChar = true ∧
      keywords.contains n = false := by
  unfold validName at h
  split at h
  · rename_i c cs hn
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨c, cs, hn, h.1.1, h.1.2, h.2⟩
  · cases h

theorem Lexes.name {D : Nat} {n : String} (h : validName n = true) :
    Lexes D .sep n.toList [.ident n] := by
  obtain ⟨c, cs, hn, hc, hcs, hk⟩ := validName_cons h
  have := Lexes.word (D := D) hc hcs
  rw [← hn, String.ofList_toList] at this
  have hk' : n ∉ keywords := by simpa using hk
  simpa [wordKind, hk'] using this

theorem name_exprStart {n : String} (h : validName n = true) :
    ∃ x xs, n.toList = x :: xs ∧ exprStart x = true := by
  obtain ⟨c, cs, hn, hc, -⟩ := validName_cons h
  exact ⟨c, cs, hn, by simp [exprStart, hc]⟩

theorem indent_toList (n : Nat) : (indent n).toList = List.replicate (4 * n) ' ' := by
  unfold indent String.pushn
  generalize 4 * n = k
  induction k with
  | zero => rfl
  | succ k ih => simp [Nat.repeat, ih, List.replicate_succ']

theorem Lexes.indent {D : Nat} (n : Nat) : Lexes D .any (indent n).toList [] := by
  rw [indent_toList]
  generalize 4 * n = k
  induction k with
  | zero => exact Lexes.nil
  | succ k ih =>
    have := (Lexes.ws (D := D) (c := ' ') (by decide)).append ih (Starts.any _)
    simpa [List.replicate_succ] using this

/-! The arguments of a call, an index, or a declaration, with `, ` between two of them. -/
theorem Lexes.args {D : Nat} {α : Type} (P : α → String) (T : α → List Kind) (xs : List α)
    (h : ∀ x ∈ xs, Lexes D .sep (P x).toList (T x)) :
    Lexes D .sep (args (xs.map P)).toList (argToks (xs.map T)) := by
  have hc : Lexes D .any ", ".toList [.symbol ","] := Lexes.glue (by decide)
  have hs : Starts .sep ", ".toList := Starts.lit (by decide)
  induction xs with
  | nil => exact Lexes.nil
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih := ih fun y hy => h y (by simp [hy])
    cases xs with
    | nil => simpa [Print.args, argToks] using hx
    | cons y ys =>
      have := hx.append (hc.append ih (Starts.any _)) (Starts.append hs _)
      simpa [Print.args, argToks, String.intercalate_cons_cons, List.intercalate_cons_cons]
        using this

/-! The parentheses of an expression in a context of a higher level. -/
theorem Lexes.paren {D : Nat} {s : String} {ks : List Kind} (c : Prop) [Decidable c]
    (h : Lexes D .sep s.toList ks) :
    Lexes D .sep (if c then "(" ++ s ++ ")" else s).toList
      (if c then .symbol "(" :: ks ++ [.symbol ")"] else ks) := by
  by_cases hc : c
  · have ho : Lexes D .any "(".toList [.symbol "("] := Lexes.glue (by decide)
    have hcl : Lexes D .any ")".toList [.symbol ")"] := Lexes.glue (by decide)
    have := (ho.append h (Starts.any _)).append hcl (Starts.lit (by decide))
    simpa [hc] using Lexes.any this
  · simpa [hc] using h

theorem Lexes.ite {D : Nat} {f : Follow} {a b : String} {ka kb : List Kind} (c : Prop)
    [Decidable c] (ha : c → Lexes D f a.toList ka) (hb : ¬c → Lexes D f b.toList kb) :
    Lexes D f (if c then a else b).toList (if c then ka else kb) := by
  by_cases hc : c
  · simpa [hc] using ha hc
  · simpa [hc] using hb hc

theorem Expr.print_paren (e : Expr) (ctx : Nat) :
    e.print ctx = if e.level < ctx then "(" ++ e.print 0 ++ ")" else e.print 0 := by
  rw [Expr.print.eq_def, Expr.print.eq_def (ctx := 0)]
  simp only [Nat.not_lt_zero, ite_false]

theorem Expr.toks_paren (e : Expr) (ctx : Nat) :
    e.toks ctx = if e.level < ctx then .symbol "(" :: e.toks 0 ++ [.symbol ")"] else e.toks 0 := by
  rw [Expr.toks.eq_def, Expr.toks.eq_def (ctx := 0)]
  simp only [Nat.not_lt_zero, ite_false]

theorem head_of_cons {l : List Char} {x : Char} (h : l.head? = some x)
    (hx : exprStart x = true) : ∃ x xs, l = x :: xs ∧ exprStart x = true := by
  cases l with
  | nil => cases h
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at h
    exact ⟨y, ys, rfl, h ▸ hx⟩

theorem Expr.head_paren (e : Expr)
    (h : ∃ x xs, (e.print 0).toList = x :: xs ∧ exprStart x = true) (ctx : Nat) :
    ∃ x xs, (e.print ctx).toList = x :: xs ∧ exprStart x = true := by
  rw [Expr.print_paren]
  split
  · exact head_of_cons (x := '(') (by simp) (by decide)
  · exact h

theorem head_append {s t : String} (h : ∃ x xs, s.toList = x :: xs ∧ exprStart x = true) :
    ∃ x xs, (s ++ t).toList = x :: xs ∧ exprStart x = true := by
  obtain ⟨x, xs, hs, hx⟩ := h
  exact ⟨x, xs ++ t.toList, by simp [hs], hx⟩

theorem Expr.head (e : Expr) :
    e.printable = true → ∀ ctx, ∃ x xs, (e.print ctx).toList = x :: xs ∧ exprStart x = true := by
  induction e using Expr.ind with
  | case17 =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    exact head_of_cons (x := 'f') (by simp [fnText]) (by decide)
  | case16 p r m xs ihr _ =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    exact head_append (ihr h.1.1 _)
  | case13 | case15 =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    exact head_of_cons (x := '[') (by simp) (by decide)
  | case11 | case12 =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    exact head_of_cons (x := '(') (by simp) (by decide)
  | case14 p b q i ihb =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    exact head_append (ihb h.1 _)
  | case1 p v =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    simp only [Nat.not_lt_zero, ite_false, Nat.toString_eq_repr, Nat.toList_repr]
    cases hd : Nat.toDigits 10 v with
    | nil => exact absurd hd Nat.toDigits_ne_nil
    | cons x xs =>
      have hx : x.isDigit = true :=
        Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
          (by rw [hd]; exact List.mem_cons_self)
      exact ⟨x, xs, rfl, by simp [exprStart, hx]⟩
  | case2 p v =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    cases v
    · exact head_of_cons (x := 'f') (by simp [boolean]) (by decide)
    · exact head_of_cons (x := 't') (by simp [boolean]) (by decide)
  | case3 p v =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    exact head_of_cons (x := '"') (by simp [Print.quote]) (by decide)
  | case4 p n =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable] at h
    simpa using name_exprStart h
  | case5 p op a _ =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    cases op
    · exact head_of_cons (x := '!') (by simp [UnOp.text]) (by decide)
    · exact head_of_cons (x := '~') (by simp [UnOp.text]) (by decide)
    · exact head_of_cons (x := '-') (by simp [UnOp.text]) (by decide)
  | case6 p op l r ihl _ =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    exact head_append (ihl h.1 _)
  | case7 p c y n =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    exact head_of_cons (x := 'i') (by simp) (by decide)
  | case8 p f xs ihf _ =>
    intro h; apply Expr.head_paren
    rw [Expr.print.eq_def]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    apply head_append
    split
    · exact head_of_cons (x := '(') (by simp) (by decide)
    · exact ihf h.1 _
  | case9 p b xs ihb _ =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    exact head_append (ihb h.1.1 _)
  | case10 p b f ihb =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    exact head_append (ihb h.1 _)
  | case18 p t v =>
    intro h; apply Expr.head_paren
    rw [Expr.print]
    simp only [Expr.printable, Bool.and_eq_true] at h
    simp only [Nat.not_lt_zero, ite_false, String.append_assoc]
    exact head_append (name_exprStart h.1)
  | case19 =>
    intro _; apply Expr.head_paren
    rw [Expr.print]
    exact head_of_cons (x := 'm') (by simp) (by decide)

theorem Expr.starts {f : Follow} (hf : f ≠ .sep) (e : Expr) (h : e.printable = true)
    (ctx : Nat) : Starts f (e.print ctx).toList :=
  starts_of_exprStart hf (Expr.head e h ctx)

theorem Lexes.wrap {D : Nat} (e : Expr) (h : Lexes D .sep (e.print 0).toList (e.toks 0))
    (ctx : Nat) : Lexes D .sep (e.print ctx).toList (e.toks ctx) := by
  rw [Expr.print_paren, Expr.toks_paren]
  exact Lexes.paren _ h

theorem UnOp.lexes {D : Nat} (op : UnOp) :
    ∃ f, f ≠ .sep ∧ Lexes D f op.text.toList [.symbol op.text] := by
  cases op
  · exact ⟨.sym '!', by decide, Lexes.glue (by decide)⟩
  · exact ⟨.any, by decide, Lexes.glue (by decide)⟩
  · exact ⟨.sym '-', by decide, Lexes.glue (by decide)⟩

theorem BinOp.lexes {D : Nat} (op : BinOp) :
    Lexes D .any (" " ++ op.text ++ " ").toList [.symbol op.text] ∧
      Starts .sep (" " ++ op.text ++ " ").toList := by
  cases op <;> exact ⟨Lexes.glue (by decide), Starts.lit (by decide)⟩

/-! The arguments of a call or an index, and the closing bracket. -/
theorem Lexes.argsClose {D : Nat} (xs : List Expr) {close : String} {kc : List Kind}
    (h : ∀ x ∈ xs, Lexes D .sep (x.print 0).toList (x.toks 0))
    (hc : Lexes D .any close.toList kc) (hs : Starts .sep close.toList) :
    Lexes D .any ((Print.args (xs.map (Expr.print 0))).toList ++ close.toList)
      (argToks (xs.map (Expr.toks 0)) ++ kc) :=
  (Lexes.args _ _ xs h).append hc hs

/-! A pattern. A negative literal is `-` and a number. -/
theorem Pattern.lexes {D : Nat} (q : Pattern) (h : q.printable = true) :
    Lexes D .sep q.print.toList q.toks := by
  cases q with
  | wild => rw [Pattern.print, Pattern.toks]; exact Lexes.glue (by decide)
  | bool p v =>
    rw [Pattern.print, Pattern.toks]
    cases v
    · exact Lexes.glue (cs := "false".toList) (by decide)
    · exact Lexes.glue (cs := "true".toList) (by decide)
  | int p neg v =>
    simp only [Pattern.printable] at h
    unfold numberBound at h
    have hn := Lexes.number (D := D) (of_decide_eq_true h)
    rw [Pattern.print, Pattern.toks]
    cases neg
    · simpa using hn
    · have hm : Lexes D (.sym '-') "-".toList [.symbol "-"] := Lexes.glue (by decide)
      have hs : Starts (.sym '-') (Nat.toDigits 10 v) := by
        cases hdg : Nat.toDigits 10 v with
        | nil => exact absurd hdg Nat.toDigits_ne_nil
        | cons x xs =>
          have hx : x.isDigit = true :=
            Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
              (by rw [hdg]; exact List.mem_cons_self)
          exact starts_of_exprStart (by decide) ⟨x, xs, rfl, by simp [exprStart, hx]⟩
      simpa using hm.append hn hs
  | variant p t v bs =>
    simp only [Pattern.printable, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨ht, -⟩, hv⟩, -⟩, hbs⟩ := h
    have hc : Lexes D .any "::".toList [.symbol "::"] := Lexes.glue (by decide)
    have hpath := (Lexes.name (D := D) ht).append (hc.append (Lexes.name hv) (Starts.any _))
      (Starts.glue "::" (by decide) _)
    rw [Pattern.print, Pattern.toks]
    cases bs with
    | nil => simpa using hpath
    | cons b bs =>
      have hb : ∀ x ∈ b :: bs, Lexes D .sep (Pattern.binderText x).toList
          (Pattern.binderToks x) := by
        intro x hx
        have := hbs x hx
        cases x with
        | none => exact Lexes.glue (by decide)
        | some i =>
          simp only [binderOk, Bool.and_eq_true] at this
          exact Lexes.name this.1
      have ho : Lexes D .any "(".toList [.symbol "("] := Lexes.glue (by decide)
      have hcl : Lexes D .any ")".toList [.symbol ")"] := Lexes.glue (by decide)
      have ha := Lexes.args (D := D) Pattern.binderText Pattern.binderToks (b :: bs) hb
      have hpar := ho.append (ha.append hcl (Starts.lit (by decide))) (Starts.any _)
      have := hpath.append hpar (Starts.glue "(" (by decide) _)
      simpa using Lexes.any (f := .sep) this

/-! The arms of a `match`, each with a space before it and a `,` after it. -/
theorem Lexes.arms {D : Nat} (arms : List Arm)
    (h : ∀ a ∈ arms, Lexes D .any (" " ++ a.print ++ ",").toList a.toks) :
    Lexes D .any (armsText (arms.map Arm.print)).toList (arms.map Arm.toks).flatten := by
  induction arms with
  | nil => exact Lexes.nil
  | cons a as ih =>
    have := (h a (by simp)).append (ih fun x hx => h x (by simp [hx])) (Starts.any _)
    simpa [armsText] using this

private theorem lexes_all (D : Nat) :
    (∀ e : Expr, e.printable = true → ∀ ctx, Lexes D .sep (e.print ctx).toList (e.toks ctx)) ∧
      ∀ t : TypeExpr, t.printable = true → Lexes D .sep t.print.toList t.toks := by
  suffices h : (∀ e : Expr, e.printable = true → ∀ ctx,
      Lexes D .sep (e.print ctx).toList (e.toks ctx)) ∧
      (∀ a : Arm, a.printable = true → Lexes D .any (" " ++ a.print ++ ",").toList a.toks) ∧
      (∀ p : FnParam, p.printable = true → Lexes D .sep p.print.toList p.toks) ∧
      ∀ t : TypeExpr, t.printable = true → Lexes D .sep t.print.toList t.toks from
    ⟨h.1, h.2.2.2⟩
  have hcl : Lexes D .any ")".toList [.symbol ")"] := Lexes.glue (by decide)
  have hcs : Starts .sep ")".toList := Starts.lit (by decide)
  have hop : Lexes D .any "(".toList [.symbol "("] := Lexes.glue (by decide)
  have hb : Lexes D .any "[".toList [.symbol "["] := Lexes.glue (by decide)
  have hfn : ∀ (ps : List FnParam) (r : TypeExpr),
      (∀ x ∈ ps, Lexes D .sep x.print.toList x.toks) → Lexes D .sep r.print.toList r.toks →
      Lexes D .sep (fnText (ps.map FnParam.print) r.print).toList
        ([.keyword "fn", .symbol "("] ++ argToks (ps.map FnParam.toks) ++
          [.symbol ")", .symbol "->"] ++ r.toks) := by
    intro ps r hps hr
    have g1 : Lexes D .any "fn (".toList [.keyword "fn", .symbol "("] := Lexes.glue (by decide)
    have g2 : Lexes D .any ") -> ".toList [.symbol ")", .symbol "->"] := Lexes.glue (by decide)
    have ha := Lexes.args (D := D) FnParam.print FnParam.toks ps hps
    have := g1.append (ha.append (g2.append hr (Starts.any _)) (Starts.glue ") -> " (by decide) _))
      (Starts.any _)
    simpa [fnText] using this
  apply Expr.erase.mutual_induct
  case case19 =>
    intro p s arms ihs ih h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true, Arm.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print, Expr.toks]
    have g1 : Lexes D .any "match (".toList [.keyword "match", .symbol "("] :=
      Lexes.glue (by decide)
    have g2 : Lexes D .any ") {".toList [.symbol ")", .symbol "{"] := Lexes.glue (by decide)
    have g3 : Lexes D .any " }".toList [.symbol "}"] := Lexes.glue (by decide)
    have ha := Lexes.arms (D := D) arms fun x hx => ih x hx (h.2 x hx)
    have := g1.append ((ihs h.1 0).append (g2.append (ha.append g3 (Starts.any _))
      (Starts.any _)) (Starts.glue ") {" (by decide) _)) (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case20 =>
    intro q v ih h
    simp only [Arm.printable, Bool.and_eq_true] at h
    rw [Arm.print, Arm.toks]
    have sp : Lexes D .any " ".toList [] := Lexes.glue (by decide)
    have ga : Lexes D .any " => ".toList [.symbol "=>"] := Lexes.glue (by decide)
    have gc : Lexes D .any ",".toList [.symbol ","] := Lexes.glue (by decide)
    have := sp.append ((Pattern.lexes q h.1).append (ga.append ((ih h.2 0).append gc
      (Starts.glue "," (by decide) _)) (Starts.any _)) (Starts.glue " => " (by decide) _))
      (Starts.any _)
    simpa using this
  case case17 =>
    intro p ps r ih ihr h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true, FnParam.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print, Expr.toks]
    simpa using hfn ps r (fun x hx => ih x hx (h.1 x hx)) (ihr h.2)
  case case21 =>
    intro m t iht h
    simp only [FnParam.printable] at h
    rw [FnParam.print, FnParam.toks]
    cases m
    · simpa using iht h
    · have g : Lexes D .any "mut ".toList [.keyword "mut"] := Lexes.glue (by decide)
      simpa using g.append (iht h) (Starts.any _)
  case case27 =>
    intro p ps r ih ihr h
    simp only [TypeExpr.printable, Bool.and_eq_true, FnParam.printableAll_eq,
      List.all_eq_true] at h
    rw [TypeExpr.print, TypeExpr.toks]
    exact hfn ps r (fun x hx => ih x hx (h.1 x hx)) (ihr h.2)
  case case16 =>
    intro p r m xs ihr ihx h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print, Expr.toks]
    have hd : Lexes D (.sym '.') ".".toList [.symbol "."] := Lexes.glue (by decide)
    have ha := Lexes.argsClose (D := D) xs (fun x hx => ihx x hx (h.2 x hx) 0) hcl hcs
    have hm := (Lexes.name h.1.2).append (hop.append ha (Starts.any _))
      (Starts.glue "(" (by decide) _)
    have := (ihr h.1.1 postfixLevel).append (hd.append hm
      ((starts_of_exprStart (by decide) (name_exprStart h.1.2)).append _))
      (Starts.glue "." (by decide) _)
    simpa using Lexes.any (f := .sep) this
  case case15 =>
    intro p t n iht ihn h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true] at h
    rw [Expr.print, Expr.toks]
    have hs : Lexes D .any "; ".toList [.symbol ";"] := Lexes.glue (by decide)
    have hc : Lexes D .any "]".toList [.symbol "]"] := Lexes.glue (by decide)
    have := hb.append ((iht h.1).append (hs.append ((ihn h.2 0).append hc
      (Starts.lit (by decide))) (Starts.any _)) (Starts.glue "; " (by decide) _)) (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case11 =>
    intro p _; apply Lexes.wrap
    rw [Expr.print, Expr.toks]
    simpa using Lexes.any (f := .sep) (Lexes.glue (D := D) (cs := "()".toList)
      (ks := [.symbol "(", .symbol ")"]) (by decide))
  case case12 =>
    intro p xs ihx h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print, Expr.toks]
    have hx : ∀ x ∈ xs, Lexes D .sep (x.print 0).toList (x.toks 0) :=
      fun x hx => ihx x hx (h.2 x hx) 0
    have ha : Lexes D .any ((Print.args (xs.map (Expr.print 0))).toList ++
        (tupleEnd xs.length).toList)
        (argToks (xs.map (Expr.toks 0)) ++
          (if xs.length == 1 then [.symbol ",", .symbol ")"] else [.symbol ")"])) := by
      unfold tupleEnd
      by_cases h1 : xs.length = 1
      · simp only [h1, beq_self_eq_true, ite_true]
        exact Lexes.argsClose xs hx (Lexes.glue (by decide)) (Starts.lit (by decide))
      · have h1' : (xs.length == 1) = false := by simpa using h1
        simp only [h1', Bool.false_eq_true, ite_false]
        exact Lexes.argsClose xs hx hcl hcs
    have := hop.append ha (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case13 =>
    intro p xs ihx h; apply Lexes.wrap
    simp only [Expr.printable, Expr.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print, Expr.toks]
    have ha := Lexes.argsClose (D := D) xs (fun x hx => ihx x hx (h x hx) 0)
      (Lexes.glue (cs := "]".toList) (ks := [.symbol "]"]) (by decide)) (Starts.lit (by decide))
    have := hb.append ha (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case14 =>
    intro p b q i ihb h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true] at h
    unfold numberBound at h
    rw [Expr.print, Expr.toks]
    have hd : Lexes D (.sym '.') ".".toList [.symbol "."] := Lexes.glue (by decide)
    have hn := Lexes.number (D := D) (of_decide_eq_true h.2)
    have hs : Starts (.sym '.') (Nat.toDigits 10 i) := by
      cases hdg : Nat.toDigits 10 i with
      | nil => exact absurd hdg Nat.toDigits_ne_nil
      | cons x xs =>
        have hx : x.isDigit = true :=
          Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
            (by rw [hdg]; exact List.mem_cons_self)
        exact starts_of_exprStart (by decide) ⟨x, xs, rfl, by simp [exprStart, hx]⟩
    have := (ihb h.1 postfixLevel).append (hd.append hn hs) (Starts.glue "." (by decide) _)
    simpa using this
  case case1 =>
    intro p v h; apply Lexes.wrap
    simp only [Expr.printable] at h
    unfold numberBound at h
    rw [Expr.print, Expr.toks]
    simpa using Lexes.number (D := D) (of_decide_eq_true h)
  case case2 =>
    intro p v _; apply Lexes.wrap
    rw [Expr.print, Expr.toks]
    cases v
    · simpa [boolean] using Lexes.glue (D := D) (cs := "false".toList)
        (f := .sep) (ks := [.keyword "false"]) (by decide)
    · simpa [boolean] using Lexes.glue (D := D) (cs := "true".toList)
        (f := .sep) (ks := [.keyword "true"]) (by decide)
  case case3 =>
    intro p v h; apply Lexes.wrap
    simp only [Expr.printable] at h
    rw [Expr.print, Expr.toks]
    simpa using Lexes.any (Lexes.string (D := D) h)
  case case4 =>
    intro p n h; apply Lexes.wrap
    simp only [Expr.printable] at h
    rw [Expr.print, Expr.toks]
    simpa using Lexes.name (D := D) h
  case case5 =>
    intro p op a iha h; apply Lexes.wrap
    simp only [Expr.printable] at h
    rw [Expr.print, Expr.toks]
    obtain ⟨f, hf, hu⟩ := UnOp.lexes (D := D) op
    have := hu.append (iha h unaryLevel) (Expr.starts hf a h _)
    simpa using this
  case case6 =>
    intro p op l r ihl ihr h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true] at h
    rw [Expr.print, Expr.toks]
    obtain ⟨hb, hbs⟩ := BinOp.lexes (D := D) op
    have := (ihl h.1 (if op.associative then op.level else op.level + 1)).append
      (hb.append (ihr h.2 (op.level + 1)) (Starts.any _)) (hbs.append _)
    simpa using this
  case case7 =>
    intro p c y n ihc ihy ihn h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true] at h
    rw [Expr.print, Expr.toks]
    have g1 : Lexes D .any "if (".toList [.keyword "if", .symbol "("] := Lexes.glue (by decide)
    have g2 : Lexes D .any ") { ".toList [.symbol ")", .symbol "{"] := Lexes.glue (by decide)
    have g3 : Lexes D .any " } else { ".toList [.symbol "}", .keyword "else", .symbol "{"] :=
      Lexes.glue (by decide)
    have g4 : Lexes D .any " }".toList [.symbol "}"] := Lexes.glue (by decide)
    have := g1.append ((ihc h.1.1 0).append (g2.append ((ihy h.1.2 0).append
      (g3.append ((ihn h.2 0).append g4 (Starts.lit (by decide))) (Starts.any _))
      (Starts.glue " } else { " (by decide) _)) (Starts.any _)) (Starts.glue ") { " (by decide) _))
      (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case8 =>
    intro p f xs ihf ihx h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print.eq_def, Expr.toks.eq_def]
    simp only [Nat.not_lt_zero, ite_false, String.toList_append, List.append_assoc,
      List.cons_append]
    apply Lexes.any
    refine Lexes.append (Lexes.ite _ (fun _ => ?_) (fun _ => ihf h.1 _)) ?_
      (Starts.glue "(" (by decide) _)
    · simpa using Lexes.paren True (ihf h.1 0)
    · have ha := Lexes.argsClose (D := D) xs (fun x hx => ihx x hx (h.2 x hx) 0) hcl hcs
      simpa using hop.append ha (Starts.any _)
  case case9 =>
    intro p b xs ihb ihx h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true] at h
    rw [Expr.print, Expr.toks]
    have ho : Lexes D .any "[".toList [.symbol "["] := Lexes.glue (by decide)
    have ha := Lexes.argsClose (D := D) xs (fun x hx => ihx x hx (h.2 x hx) 0)
      (Lexes.glue (cs := "]".toList) (ks := [.symbol "]"]) (by decide)) (Starts.lit (by decide))
    have := (ihb h.1.1 postfixLevel).append (ho.append ha (Starts.any _))
      (Starts.glue "[" (by decide) _)
    simpa using Lexes.any (f := .sep) this
  case case10 =>
    intro p b f ihb h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true] at h
    rw [Expr.print, Expr.toks]
    have hd : Lexes D (.sym '.') ".".toList [.symbol "."] := Lexes.glue (by decide)
    have := (ihb h.1 postfixLevel).append (hd.append (Lexes.name h.2)
      (starts_of_exprStart (by decide) (name_exprStart h.2))) (Starts.glue "." (by decide) _)
    simpa using this
  case case18 =>
    intro p t v h; apply Lexes.wrap
    simp only [Expr.printable, Bool.and_eq_true] at h
    rw [Expr.print, Expr.toks]
    have hc : Lexes D .any "::".toList [.symbol "::"] := Lexes.glue (by decide)
    have := (Lexes.name h.1).append (hc.append (Lexes.name h.2) (Starts.any _))
      (Starts.glue "::" (by decide) _)
    simpa using this
  case case24 =>
    intro p _
    rw [TypeExpr.print, TypeExpr.toks]
    simpa using Lexes.any (f := .sep) (Lexes.glue (D := D) (cs := "()".toList)
      (ks := [.symbol "(", .symbol ")"]) (by decide))
  case case25 =>
    intro p ts ih h
    simp only [TypeExpr.printable, Bool.and_eq_true, TypeExpr.printableAll_eq,
      List.all_eq_true] at h
    rw [TypeExpr.print, TypeExpr.toks]
    have ha := Lexes.args (D := D) TypeExpr.print TypeExpr.toks ts fun x hx => ih x hx (h.2 x hx)
    have hc : Lexes D .any (tupleEnd ts.length).toList
        (if ts.length == 1 then [.symbol ",", .symbol ")"] else [.symbol ")"]) := by
      unfold tupleEnd
      split
      · exact Lexes.glue (by decide)
      · exact Lexes.glue (by decide)
    have hs : Starts .sep (tupleEnd ts.length).toList := by
      unfold tupleEnd
      split
      · exact Starts.lit (by decide)
      · exact Starts.lit (by decide)
    have := hop.append (ha.append hc hs) (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case26 =>
    intro p t n iht ihn h
    simp only [TypeExpr.printable, Bool.and_eq_true] at h
    rw [TypeExpr.print, TypeExpr.toks]
    have hs : Lexes D .any "; ".toList [.symbol ";"] := Lexes.glue (by decide)
    have hc : Lexes D .any "]".toList [.symbol "]"] := Lexes.glue (by decide)
    have := hb.append ((iht h.1).append (hs.append ((ihn h.2 0).append hc
      (Starts.lit (by decide))) (Starts.any _)) (Starts.glue "; " (by decide) _)) (Starts.any _)
    simpa using Lexes.any (f := .sep) this
  case case22 =>
    intro p n h
    simp only [TypeExpr.printable] at h
    rw [TypeExpr.print, TypeExpr.toks]
    exact Lexes.name h
  case case23 =>
    intro p b xs ih ihx h
    simp only [TypeExpr.printable, Bool.and_eq_true, Expr.printableAll_eq,
      List.all_eq_true] at h
    have ha := Lexes.argsClose (D := D) xs (fun x hx => ihx x hx (h.2 x hx) 0)
      (Lexes.glue (cs := "]".toList) (ks := [.symbol "]"]) (by decide)) (Starts.lit (by decide))
    rw [TypeExpr.print.eq_def, TypeExpr.toks.eq_def]
    cases b with
    | fn =>
      have hpar := Lexes.paren (D := D) True (ih h.1.1)
      simp only [ite_true] at hpar
      have := hpar.append (hb.append ha (Starts.any _)) (Starts.glue "[" (by decide) _)
      simpa using Lexes.any (f := .sep) this
    | _ =>
      have := (ih h.1.1).append (hb.append ha (Starts.any _)) (Starts.glue "[" (by decide) _)
      simpa using Lexes.any (f := .sep) this

theorem Expr.lexes {D : Nat} (e : Expr) :
    e.printable = true → ∀ ctx, Lexes D .sep (e.print ctx).toList (e.toks ctx) :=
  (lexes_all D).1 e

theorem TypeExpr.lexes {D : Nat} (t : TypeExpr) :
    t.printable = true → Lexes D .sep t.print.toList t.toks :=
  (lexes_all D).2 t

theorem Lexes.lines {D : Nat} (b : List Stmt)
    (h : ∀ s ∈ b, ∀ d, Lexes D .any (s.print d).toList s.toks) (d : Nat) :
    Lexes D .any (Stmt.lines d b).toList (Stmt.linesToks b) := by
  induction b with
  | nil => rw [Stmt.lines, Stmt.linesToks]; exact Lexes.nil
  | cons s ss ih =>
    rw [Stmt.lines, Stmt.linesToks, String.toList_append]
    exact (h s (by simp) d).append (ih fun x hx => h x (by simp [hx])) (Starts.any _)

theorem Lexes.body {D : Nat} (b : List Stmt)
    (h : ∀ s ∈ b, ∀ d, Lexes D .any (s.print d).toList s.toks) (d : Nat) :
    Lexes D .any (Stmt.body d b).toList (Stmt.bodyToks b) := by
  cases b with
  | nil =>
    rw [Stmt.body, Stmt.bodyToks, Stmt.linesToks]
    exact Lexes.glue (by decide)
  | cons s ss =>
    rw [Stmt.body.eq_def, Stmt.bodyToks]
    simp only [String.toList_append]
    have g1 : Lexes D .any "{\n".toList [.symbol "{"] := Lexes.glue (by decide)
    have g2 : Lexes D .any "}".toList [.symbol "}"] := Lexes.glue (by decide)
    have := g1.append ((Lexes.lines (s :: ss) h (d + 1)).append ((Lexes.indent d).append g2
      (Starts.any _)) (Starts.any _)) (Starts.any _)
    simpa using this

/-! The name and the type of a declaration: `name: type`. -/
theorem Lexes.decl {D : Nat} {n : String} {t : TypeExpr} (hn : validName n = true)
    (ht : t.printable = true) :
    Lexes D .sep (n.toList ++ (": ".toList ++ t.print.toList))
      (.ident n :: .symbol ":" :: t.toks) := by
  have g : Lexes D .any ": ".toList [.symbol ":"] := Lexes.glue (by decide)
  have := (Lexes.name (D := D) hn).append (g.append (TypeExpr.lexes t ht) (Starts.any _))
    (Starts.glue ": " (by decide) _)
  simpa using this

theorem Stmt.lexes {D : Nat} (plain : Bool) (s : Stmt) :
    s.printable plain = true → ∀ d, Lexes D .any (s.print d).toList s.toks := by
  have semi : Lexes D .any ";\n".toList [.symbol ";"] := Lexes.glue (by decide)
  have eq : Lexes D .any " = ".toList [.symbol "="] := Lexes.glue (by decide)
  have nl : Lexes D .any "\n".toList [] := Lexes.glue (by decide)
  induction s using Stmt.erase.induct with
  | case16 p n ty =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "type ".toList [.keyword "type"] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.name h.1).append (eq.append
      ((TypeExpr.lexes ty h.2).append semi (Starts.glue ";\n" (by decide) _)) (Starts.any _))
      (Starts.glue " = " (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case1 p m n ty v =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    obtain ⟨⟨hn, ht⟩, hv⟩ := h
    rw [Stmt.print, Stmt.toks]
    have hl : Lexes D .any "let ".toList [.keyword "let"] := Lexes.glue (by decide)
    have hm : Lexes D .any (if m then "mut " else "").toList
        (if m then [.keyword "mut"] else []) :=
      Lexes.ite _ (fun _ => Lexes.glue (by decide)) (fun _ => Lexes.nil)
    have tail := eq.append ((Expr.lexes v hv 0).append semi (Starts.glue ";\n" (by decide) _))
      (Starts.any _)
    cases ty with
    | none =>
      have := (Lexes.indent (D := D) d).append (hl.append (hm.append ((Lexes.name hn).append
        tail (Starts.glue " = " (by decide) _)) (Starts.any _)) (Starts.any _)) (Starts.any _)
      simpa using this
    | some t =>
      simp only [Option.all_some] at ht
      have := (Lexes.indent (D := D) d).append (hl.append (hm.append ((Lexes.decl hn ht).append
        tail (Starts.glue " = " (by decide) _)) (Starts.any _)) (Starts.any _)) (Starts.any _)
      simpa using this
  | case2 p t v =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have := (Lexes.indent (D := D) d).append ((Expr.lexes t h.1.2 0).append (eq.append
      ((Expr.lexes v h.2 0).append semi (Starts.glue ";\n" (by decide) _)) (Starts.any _))
      (Starts.glue " = " (by decide) _)) (Starts.any _)
    simpa using this
  | case3 p t v =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any " := ".toList [.symbol ":="] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append ((Expr.lexes t h.1.2 0).append (g.append
      ((Expr.lexes v h.2 0).append semi (Starts.glue ";\n" (by decide) _)) (Starts.any _))
      (Starts.glue " := " (by decide) _)) (Starts.any _)
    simpa using this
  | case4 p n ty i =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "reg ".toList [.keyword "reg"] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.decl h.1.1.2 h.1.2).append
      (eq.append ((Expr.lexes i h.2 0).append semi (Starts.glue ";\n" (by decide) _))
      (Starts.any _)) (Starts.glue " = " (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case5 p n ty =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "wire ".toList [.keyword "wire"] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.decl h.1.2 h.2).append
      semi (Starts.glue ";\n" (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case6 p n ty v =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "mem ".toList [.keyword "mem"] := Lexes.glue (by decide)
    have ho : Lexes D .any ": [".toList [.symbol ":", .symbol "["] := Lexes.glue (by decide)
    have hs : Lexes D .any "; ".toList [.symbol ";"] := Lexes.glue (by decide)
    have hc : Lexes D .any "];\n".toList [.symbol "]", .symbol ";"] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.name h.1.1.2).append
      (ho.append ((TypeExpr.lexes ty h.1.2).append (hs.append ((Expr.lexes v h.2 0).append hc
      (Starts.lit (by decide))) (Starts.any _)) (Starts.glue "; " (by decide) _))
      (Starts.any _)) (Starts.glue ": [" (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case7 p n ty =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "input ".toList [.keyword "input"] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.decl h.1.2 h.2).append
      semi (Starts.glue ";\n" (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case8 p n ty =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "output ".toList [.keyword "output"] := Lexes.glue (by decide)
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.decl h.1.2 h.2).append
      semi (Starts.glue ";\n" (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case9 p n m xs =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true, Expr.printableAll_eq,
      List.all_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "instance ".toList [.keyword "instance"] := Lexes.glue (by decide)
    have ho : Lexes D .any "(".toList [.symbol "("] := Lexes.glue (by decide)
    have ha := Lexes.argsClose (D := D) xs (fun x hx => Expr.lexes x (h.2 x hx) 0)
      (Lexes.glue (cs := ");\n".toList) (ks := [.symbol ")", .symbol ";"])
        (by decide)) (Starts.lit (by decide))
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.name h.1.1.2).append
      (eq.append ((Lexes.name h.1.2).append (ho.append ha (Starts.any _))
      (Starts.glue "(" (by decide) _)) (Starts.any _)) (Starts.glue " = " (by decide) _))
      (Starts.any _)) (Starts.any _)
    simpa using this
  | case10 p v =>
    intro h d
    cases v with
    | none =>
      rw [Stmt.print, Stmt.toks]
      have g : Lexes D .any "return;\n".toList [.keyword "return", .symbol ";"] :=
        Lexes.glue (by decide)
      simpa using (Lexes.indent (D := D) d).append g (Starts.any _)
    | some v =>
      simp only [Stmt.printable, Option.all_some] at h
      rw [Stmt.print, Stmt.toks]
      have g : Lexes D .any "return ".toList [.keyword "return"] := Lexes.glue (by decide)
      have := (Lexes.indent (D := D) d).append (g.append ((Expr.lexes v h 0).append semi
        (Starts.glue ";\n" (by decide) _)) (Starts.any _)) (Starts.any _)
      simpa using this
  | case11 p c y ih =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true, Stmt.printableAll_eq,
      List.all_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "comptime if (".toList
        [.keyword "comptime", .keyword "if", .symbol "("] := Lexes.glue (by decide)
    have g2 : Lexes D .any ") ".toList [.symbol ")"] := Lexes.glue (by decide)
    have hb := Lexes.body (D := D) y (fun x hx => ih x hx (h.2 x hx)) d
    have := (Lexes.indent (D := D) d).append (g.append ((Expr.lexes c h.1 0).append
      (g2.append (hb.append nl (Starts.any _)) (Starts.any _)) (Starts.glue ") " (by decide) _))
      (Starts.any _)) (Starts.any _)
    simpa using this
  | case12 p c y n ihy ihn =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true, Stmt.printableAll_eq,
      List.all_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "comptime if (".toList
        [.keyword "comptime", .keyword "if", .symbol "("] := Lexes.glue (by decide)
    have g2 : Lexes D .any ") ".toList [.symbol ")"] := Lexes.glue (by decide)
    have g3 : Lexes D .any " else ".toList [.keyword "else"] := Lexes.glue (by decide)
    have hy := Lexes.body (D := D) y (fun x hx => ihy x hx (h.1.2 x hx)) d
    have hn := Lexes.body (D := D) n (fun x hx => ihn x hx (h.2 x hx)) d
    have := (Lexes.indent (D := D) d).append (g.append ((Expr.lexes c h.1.1 0).append
      (g2.append (hy.append (g3.append (hn.append nl (Starts.any _)) (Starts.any _))
      (Starts.any _)) (Starts.any _)) (Starts.glue ") " (by decide) _)) (Starts.any _))
      (Starts.any _)
    simpa using this
  | case13 p i lo hi b ih =>
    intro h d
    simp only [Stmt.printable, Bool.and_eq_true, Stmt.printableAll_eq,
      List.all_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have g : Lexes D .any "comptime for ".toList [.keyword "comptime", .keyword "for"] :=
      Lexes.glue (by decide)
    have gi : Lexes D .any " in ".toList [.keyword "in"] := Lexes.glue (by decide)
    have gr : Lexes D .any " .. ".toList [.symbol ".."] := Lexes.glue (by decide)
    have gs : Lexes D .any " ".toList [] := Lexes.glue (by decide)
    have hb := Lexes.body (D := D) b (fun x hx => ih x hx (h.2 x hx)) d
    have := (Lexes.indent (D := D) d).append (g.append ((Lexes.name h.1.1.1).append
      (gi.append ((Expr.lexes lo h.1.1.2 0).append (gr.append ((Expr.lexes hi h.1.2 0).append
      (gs.append (hb.append nl (Starts.any _)) (Starts.any _)) (Starts.glue " " (by decide) _))
      (Starts.any _)) (Starts.glue " .. " (by decide) _)) (Starts.any _))
      (Starts.glue " in " (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | case14 p b ih =>
    intro h d
    simp only [Stmt.printable, Stmt.printableAll_eq, List.all_eq_true] at h
    rw [Stmt.print, Stmt.toks]
    have hb := Lexes.body (D := D) b (fun x hx => ih x hx (h x hx)) d
    have := (Lexes.indent (D := D) d).append (hb.append nl (Starts.any _)) (Starts.any _)
    simpa using this
  | case15 p v =>
    intro h d
    simp only [Stmt.printable] at h
    rw [Stmt.print, Stmt.toks]
    have := (Lexes.indent (D := D) d).append ((Expr.lexes v h 0).append semi
      (Starts.glue ";\n" (by decide) _)) (Starts.any _)
    simpa using this

theorem Param.lexes {D : Nat} {static : Bool} (p : Param) (h : p.printable static = true) :
    Lexes D .sep p.print.toList p.toks := by
  simp only [Param.printable, Bool.and_eq_true] at h
  unfold Param.print Param.toks
  have hc : Lexes D .any p.mode.mark.toList p.mode.toks := by
    cases p.mode
    · exact Lexes.nil
    · exact Lexes.glue (by decide)
    · exact Lexes.glue (by decide)
  have := hc.append (Lexes.decl (D := D) h.1.2 h.2) (Starts.any _)
  simpa using this

/-! The fields of a struct, each on its own line and with a `,` at its end. -/
theorem Lexes.fields {D : Nat} (fs : List StructField)
    (h : fs.all (fun f => validName f.name.name && f.ty.printable) = true) :
    Lexes D .any (String.join (fs.map fun f => Print.indent 1 ++ f.print ++ ",\n")).toList
      (fs.flatMap StructField.toks) := by
  have g : Lexes D .any ",\n".toList [.symbol ","] := Lexes.glue (by decide)
  induction fs with
  | nil => exact Lexes.nil
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hx := (Lexes.indent (D := D) 1).append ((Lexes.decl (D := D) h.1.1 h.1.2).append g
      (Starts.glue ",\n" (by decide) _)) (Starts.any _)
    have := hx.append (ih h.2) (Starts.any _)
    simpa [StructField.print, StructField.toks] using this

/-! A variant of an enum on its own line, with a `,` at its end. -/
theorem Lexes.variant {D : Nat} (v : Variant) (h : v.printable = true) :
    Lexes D .any (Print.indent 1 ++ v.print ++ ",\n").toList v.toks := by
  obtain ⟨n, ps, tag⟩ := v
  simp only [Variant.printable, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hn, hps⟩, htag⟩ := h
  have g : Lexes D .any ",\n".toList [.symbol ","] := Lexes.glue (by decide)
  have eq : Lexes D .any " = ".toList [.symbol "="] := Lexes.glue (by decide)
  have tail := eq.append ((Expr.lexes tag htag 0).append g (Starts.glue ",\n" (by decide) _))
    (Starts.any _)
  cases ps with
  | nil =>
    have := (Lexes.indent (D := D) 1).append ((Lexes.name hn).append tail
      (Starts.glue " = " (by decide) _)) (Starts.any _)
    simpa [Variant.print, Variant.toks, Variant.payloadToks] using this
  | cons q qs =>
    have ho : Lexes D .any "(".toList [.symbol "("] := Lexes.glue (by decide)
    have hc : Lexes D .any ")".toList [.symbol ")"] := Lexes.glue (by decide)
    have ha := Lexes.args (D := D) TypeExpr.print TypeExpr.toks (q :: qs)
      fun x hx => TypeExpr.lexes x (hps x hx)
    have hpar := ho.append (ha.append hc (Starts.lit (by decide))) (Starts.any _)
    have := (Lexes.indent (D := D) 1).append ((Lexes.name hn).append (hpar.append tail
      (Starts.any _)) (Starts.glue "(" (by decide) _)) (Starts.any _)
    simpa [Variant.print, Variant.toks, Variant.payloadToks] using this

theorem Lexes.variants {D : Nat} (vs : List Variant) (h : vs.all Variant.printable = true) :
    Lexes D .any (String.join (vs.map fun v => Print.indent 1 ++ v.print ++ ",\n")).toList
      (vs.flatMap Variant.toks) := by
  induction vs with
  | nil => exact Lexes.nil
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have := (Lexes.variant (D := D) x h.1).append (ih h.2) (Starts.any _)
    simpa using this

theorem Item.lexes {D : Nat} (i : Item) (h : i.printable = true) :
    Lexes D .any i.print.toList i.toks := by
  have semi : Lexes D .any ";\n".toList [.symbol ";"] := Lexes.glue (by decide)
  have eq : Lexes D .any " = ".toList [.symbol "="] := Lexes.glue (by decide)
  have nl : Lexes D .any "\n".toList [] := Lexes.glue (by decide)
  have ho : Lexes D .any "(".toList [.symbol "("] := Lexes.glue (by decide)
  have sp : Lexes D .any " ".toList [] := Lexes.glue (by decide)
  have body (plain : Bool) (b : List Stmt) (hb : Stmt.printableAll plain b = true) :
      Lexes D .any (Stmt.body 0 b).toList (Stmt.bodyToks b) := by
    simp only [Stmt.printableAll_eq, List.all_eq_true] at hb
    exact Lexes.body b (fun x hx => Stmt.lexes plain x (hb x hx)) 0
  have params (static : Bool) (ps : List Param)
      (hp : ps.all (Param.printable static) = true) :
      Lexes D .sep (Print.args (ps.map Param.print)).toList (argToks (ps.map Param.toks)) := by
    simp only [List.all_eq_true] at hp
    exact Lexes.args _ _ ps fun x hx => Param.lexes x (hp x hx)
  cases i with
  | enum p n ty vs =>
    simp only [Item.printable, Bool.and_eq_true] at h
    obtain ⟨⟨hn, hty⟩, hvs⟩ := h
    rw [Item.print, Item.toks]
    have g : Lexes D .any "enum ".toList [.keyword "enum"] := Lexes.glue (by decide)
    have hb : Lexes D .any (if vs.isEmpty then "{}"
        else "{\n" ++ String.join (vs.map fun v => Print.indent 1 ++ v.print ++ ",\n") ++
          "}").toList
        (.symbol "{" :: vs.flatMap Variant.toks ++ [.symbol "}"]) := by
      cases vs with
      | nil => exact Lexes.glue (by decide)
      | cons x xs =>
        have g1 : Lexes D .any "{\n".toList [.symbol "{"] := Lexes.glue (by decide)
        have g2 : Lexes D .any "}".toList [.symbol "}"] := Lexes.glue (by decide)
        have := g1.append ((Lexes.variants (x :: xs) hvs).append g2 (Starts.any _))
          (Starts.any _)
        simpa using this
    have tail := sp.append (hb.append nl (Starts.any _)) (Starts.any _)
    have := g.append ((Lexes.decl hn hty).append tail (Starts.glue " " (by decide) _))
      (Starts.any _)
    simpa using this
  | alias p n ty =>
    simp only [Item.printable, Bool.and_eq_true] at h
    rw [Item.print, Item.toks]
    have g : Lexes D .any "type ".toList [.keyword "type"] := Lexes.glue (by decide)
    have := g.append ((Lexes.name h.1).append (eq.append ((TypeExpr.lexes ty h.2).append
      semi (Starts.glue ";\n" (by decide) _)) (Starts.any _)) (Starts.glue " = " (by decide) _))
      (Starts.any _)
    simpa using this
  | struct p n ps fs =>
    simp only [Item.printable, Bool.and_eq_true] at h
    obtain ⟨⟨hn, hp⟩, hfs⟩ := h
    rw [Item.print, Item.toks]
    have g : Lexes D .any "struct ".toList [.keyword "struct"] := Lexes.glue (by decide)
    have hb : Lexes D .any (if fs.isEmpty then "{}"
        else "{\n" ++ String.join (fs.map fun f => Print.indent 1 ++ f.print ++ ",\n") ++
          "}").toList
        (.symbol "{" :: fs.flatMap StructField.toks ++ [.symbol "}"]) := by
      cases fs with
      | nil => exact Lexes.glue (by decide)
      | cons x xs =>
        have g1 : Lexes D .any "{\n".toList [.symbol "{"] := Lexes.glue (by decide)
        have g2 : Lexes D .any "}".toList [.symbol "}"] := Lexes.glue (by decide)
        have := g1.append ((Lexes.fields (x :: xs) hfs).append g2 (Starts.any _)) (Starts.any _)
        simpa using this
    have tail := sp.append (hb.append nl (Starts.any _)) (Starts.any _)
    cases ps with
    | nil =>
      have := g.append ((Lexes.name hn).append tail (Starts.glue " " (by decide) _))
        (Starts.any _)
      simpa using this
    | cons q qs =>
      have gc : Lexes D .any ")".toList [.symbol ")"] := Lexes.glue (by decide)
      have := g.append ((Lexes.name hn).append (ho.append ((params true _ hp).append
        (gc.append tail (Starts.any _)) (Starts.glue ")" (by decide) _)) (Starts.any _))
        (Starts.glue "(" (by decide) _)) (Starts.any _)
      simpa using this
  | const p n ty v =>
    simp only [Item.printable, Bool.and_eq_true] at h
    rw [Item.print, Item.toks]
    have g : Lexes D .any "const ".toList [.keyword "const"] := Lexes.glue (by decide)
    have := g.append ((Lexes.decl h.1.1 h.1.2).append (eq.append ((Expr.lexes v h.2 0).append
      semi (Starts.glue ";\n" (by decide) _)) (Starts.any _)) (Starts.glue " = " (by decide) _))
      (Starts.any _)
    simpa using this
  | fn p c n ps r b =>
    simp only [Item.printable, Bool.and_eq_true] at h
    rw [Item.print, Item.toks]
    have hc : Lexes D .any (if c then "comptime " else "").toList
        (if c then [.keyword "comptime"] else []) :=
      Lexes.ite _ (fun _ => Lexes.glue (by decide)) (fun _ => Lexes.nil)
    have g : Lexes D .any "fn ".toList [.keyword "fn"] := Lexes.glue (by decide)
    have ga : Lexes D .any ") -> ".toList [.symbol ")", .symbol "->"] := Lexes.glue (by decide)
    have := hc.append (g.append ((Lexes.name h.1.1.1).append (ho.append
      ((params false ps h.1.1.2).append (ga.append ((TypeExpr.lexes r h.1.2).append
      (sp.append ((body _ b h.2).append nl (Starts.any _)) (Starts.any _))
      (Starts.glue " " (by decide) _)) (Starts.any _)) (Starts.glue ") -> " (by decide) _))
      (Starts.any _)) (Starts.glue "(" (by decide) _)) (Starts.any _)) (Starts.any _)
    simpa using this
  | module p n ps ds b =>
    simp only [Item.printable, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hn, hp⟩, hd⟩, hb⟩ := h
    rw [Item.print.eq_def, Item.toks.eq_def]
    have g : Lexes D .any "module ".toList [.keyword "module"] := Lexes.glue (by decide)
    have gc : Lexes D .any ")".toList [.symbol ")"] := Lexes.glue (by decide)
    have tail := sp.append ((body _ b hb).append nl (Starts.any _)) (Starts.any _)
    cases ds with
    | none =>
      have := g.append ((Lexes.name hn).append (ho.append ((params true ps hp).append
        (gc.append tail (Starts.any _)) (Starts.glue ")" (by decide) _)) (Starts.any _))
        (Starts.glue "(" (by decide) _)) (Starts.any _)
      simpa using this
    | some ds =>
      simp only [Option.all_some, Bool.and_eq_true, List.all_eq_true] at hd
      have gd : Lexes D .any " domains(".toList [.keyword "domains", .symbol "("] :=
        Lexes.glue (by decide)
      have hds := Lexes.args (D := D) (·.name) (fun d : Ident => [.ident d.name]) ds
        fun x hx => Lexes.name (hd.2 x hx)
      have := g.append ((Lexes.name hn).append (ho.append ((params true ps hp).append
        (gc.append (gd.append (hds.append (gc.append tail (Starts.any _))
        (Starts.glue ")" (by decide) _)) (Starts.any _)) (Starts.any _))
        (Starts.glue ")" (by decide) _)) (Starts.any _)) (Starts.glue "(" (by decide) _))
        (Starts.any _)
      simpa using this

theorem Lexes.print {D : Nat} (items : List Item) (h : Printable items) :
    Lexes D .any (Print.print items).toList (Print.toks items) := by
  have nl : Lexes D .any "\n".toList [] := Lexes.glue (by decide)
  unfold Printable at h
  induction items with
  | nil => exact Lexes.nil
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hi := Item.lexes (D := D) i h.1
    cases is with
    | nil => simpa [Print.print, Print.toks] using hi
    | cons j js =>
      have := hi.append (nl.append (ih h.2) (Starts.any _)) (Starts.any _)
      simpa [Print.print, Print.toks, String.intercalate_cons_cons] using this

theorem run_top_nil {D d : Nat} {p : Pos} {ts : List Token} :
    run D d .top p ts [] = ⟨p, .eof⟩ :: ts := rfl

/-! The lexer lemma: the lexer gives the kinds `Print.toks items`, then `eof`. -/
theorem lex_print (items : List Item) (h : Printable items) (N : Nat)
    (hN : (Print.print items).length ≤ N) :
    (Lex.lex N (Print.print items)).map Token.kind = Print.toks items ++ [.eof] := by
  obtain ⟨d', p', ts, -, hk, he⟩ :=
    Lexes.print (D := N) items h 0 ⟨1, 1⟩ [] [] rfl (by rw [String.length_toList]; omega)
  unfold Lex.lex
  rw [← List.append_nil (Print.print items).toList, he, List.append_nil, run_top_nil]
  simp [hk]

end Silicon.Source.ParsePrint
