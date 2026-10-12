-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Parse.Runs

/-!
The parser lemma of `parse_print` for expressions and types.

`Runs.expr_print` gives `EGoal e` for each expression `e`:

```lean
e.printable = true → Win ctx.input i (e.toks 0 ++ t :: R) → After 0 t →
  4 * (e.toks 0).length + 1 ≤ f →
  Runs (expr f) ctx i (i + (e.toks 0).length) (Res e (e.toks 0).length)
```

The parser reads exactly the kinds of `e`. The result is `e` up to positions. Its height is
at most the number of these kinds. The fuel is at most four times that number, plus one. The
fuel of `parse` for `n` tokens is `32 * (n + 1)`, so it is sufficient.

The proof is an induction on the number of kinds. These parts of the parser need a lemma:

- `climb` and `infixOps`: `spine` gives the operators on the left spine of an expression in the
  order of their levels. `Runs.levels` reads them one level after the other.
- `unary`: the prefix operators, in `wrap`.
- `postfixExpr` and `suffixes`: `Runs.postfix` takes a continuation for the next suffix.
- `tupleAhead`: the window gives a false comma flag at each `(` of an expression in
  parentheses, and a true comma flag at the `(` of a tuple. At `()`, a `)` follows the `(`.
- `arrayTypeAhead`: the window gives a false semicolon flag at the `[` of an array, and a true
  semicolon flag at the `[` of an array type. `Runs.type_of` reads the element type of the
  array type with the hypothesis of the induction for expressions.
- `args`: a tuple of one element ends with `,)`, and `Runs.args_trail` reads it.
- `checkHeight` in `value` and `typeTop`: each height is at most the syntax depth.
- `typeExpr` at `(`: the window gives a true comma flag at the `(` of a tuple type. At `()`, a
  `)` follows the `(`. `Runs.typeElems` reads the element types, with a `,` before the `)` if
  the tuple has one element.
- `typeExpr` at `[`: the parser reads an array type `[T; N]` without the semicolon flag.

`Runs.value`, `Runs.args`, `Runs.type_end`, `Runs.typeTop`, `Runs.postfix_end`, and
`Runs.postfix_climb` are the interfaces for the lemma of the statements.
-/
namespace Silicon.Source.ParsePrint

open Lex Parse Print

/-! ## Results and goals -/

/-! The node `n` is `e` up to positions, and its height is at most `T`. -/
def Res (e : Expr) (T : Nat) (n : Node) : Prop := n.expr.erase = e.erase ∧ n.height ≤ T

/-! `expr` reads the kinds of `e` in the context 0 back to `e`. -/
def EGoal (e : Expr) : Prop :=
  e.printable = true → ∀ ctx i t R f, Win ctx.input i (e.toks 0 ++ t :: R) → After 0 t →
    4 * (e.toks 0).length + 1 ≤ f →
    Runs (expr f) ctx i (i + (e.toks 0).length) (Res e (e.toks 0).length)

/-! `checkHeight` changes nothing for a height of at most the syntax depth. -/
theorem Runs.checkHeight {ctx : Ctx} {i h : Nat} {start : Pos} (hd : h ≤ ctx.depth) :
    Runs (checkHeight start h) ctx i i (fun _ => True) := by
  unfold Parse.checkHeight
  refine Runs.bind (Q := (· = ctx)) (fun _ => ⟨ctx, rfl, rfl⟩) fun c hc => ?_
  subst hc
  intro hh
  refine ⟨(), ?_, trivial⟩
  have : ¬ c.depth < h := by omega
  show Except.ok ((), if _ then _ else _) = _
  simp [this]

theorem Runs.argument {x : Expr} (hE : EGoal x) (hp : x.printable = true) {ctx : Ctx}
    {i : Nat} {t : Kind} {R : List Kind} {f : Nat} {top : Bool}
    (hw : Win ctx.input i (x.toks 0 ++ t :: R)) (ht : After 0 t)
    (hf : 4 * (x.toks 0).length + 2 ≤ f) (htop : top = true → (x.toks 0).length ≤ ctx.depth) :
    Runs (Parse.argument f top) ctx i (i + (x.toks 0).length) (Res x (x.toks 0).length) := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.argument]
  refine Runs.peek_bind ?_
  refine Runs.bind (hE hp ctx i t R f hw ht (by omega)) fun n hn => ?_
  cases top
  · exact Runs.pure hn
  · refine Runs.bind (Runs.checkHeight (Nat.le_trans hn.2 (htop rfl))) fun _ _ => Runs.pure hn


/-! ## Arguments -/

/-! The kinds of the arguments after the first, each after its `,`. -/
def commaToks (xs : List Expr) : List Kind := xs.flatMap fun x => .symbol "," :: x.toks 0

theorem argToks_cons (x : Expr) (xs : List Expr) :
    argToks ((x :: xs).map (Expr.toks 0)) = x.toks 0 ++ commaToks xs := by
  induction xs generalizing x with
  | nil => simp [Print.argToks, commaToks]
  | cons y ys ih =>
    have := ih y
    simp only [List.map_cons] at this
    simp [Print.argToks, List.intercalate_cons_cons, commaToks] at this ⊢
    rw [this]

theorem After.comma {c : Nat} : After c (.symbol ",") :=
  After.sym (fun op => by cases op <;> decide) (by decide)

theorem After.close {c : Nat} {close : String} (hc : close = ")" ∨ close = "]") :
    After c (.symbol close) := by
  rcases hc with rfl | rfl
  · exact After.sym (fun op => by cases op <;> decide) (by decide)
  · exact After.sym (fun op => by cases op <;> decide) (by decide)

theorem commaToks_next (xs : List Expr) (close : String) (R : List Kind) :
    ∃ t R', commaToks xs ++ .symbol close :: R = t :: R' ∧
      (t = .symbol "," ∨ t = .symbol close) := by
  cases xs with
  | nil => exact ⟨_, _, rfl, Or.inr rfl⟩
  | cons x xs => exact ⟨_, _, rfl, Or.inl rfl⟩

theorem Runs.argsRest {close : String} (hc : close = ")" ∨ close = "]") {top : Bool}
    {xs : List Expr} (hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true) :
    ∀ (ctx : Ctx) (i f : Nat) (R : List Kind) (acc : List Node),
    Win ctx.input i (commaToks xs ++ .symbol close :: R) →
    4 * (commaToks xs).length + 2 ≤ f →
    (top = true → (commaToks xs).length ≤ ctx.depth) →
    Runs (Parse.argsRest f close top acc) ctx i (i + (commaToks xs).length + 1)
      (fun ns => ∃ ms, ns = acc.reverse ++ ms ∧ ms.map (·.expr.erase) = xs.map Expr.erase ∧
        ∀ n ∈ ms, n.height ≤ (commaToks xs).length) := by
  induction xs with
  | nil =>
    intro ctx i f R acc hw hf _
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.argsRest]
    refine Runs.bind (Runs.acceptSym_true hw.head) fun b hb => ?_
    subst hb
    exact Runs.pure ⟨[], by simp, by simp, by simp⟩
  | cons x xs ih =>
    intro ctx i f R acc hw hf htop
    obtain ⟨hEx, hpx⟩ := hE x (by simp)
    specialize ih fun y hy => hE y (by simp [hy])
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hlen : (commaToks (x :: xs)).length = 1 + (x.toks 0).length + (commaToks xs).length := by
      simp [commaToks]; omega
    have hw1 : Win ctx.input i
        (.symbol "," :: (x.toks 0 ++ (commaToks xs ++ .symbol close :: R))) := by
      simpa [commaToks] using hw
    have hw2 := hw1.tail
    obtain ⟨t, R', hR, ht⟩ := commaToks_next xs close R
    rw [hR] at hw2
    obtain ⟨k, hk, hkc⟩ := Expr.toks_head x 0
    obtain ⟨ks, hks⟩ : ∃ ks, x.toks 0 = k :: ks := List.head?_eq_some_iff.1 hk
    have hk1 : (tokenAt ctx.input (i + 1)).kind = k := by
      rw [hks] at hw2; exact hw2.head
    rw [Parse.argsRest]
    refine Runs.bind (Runs.acceptSym_false (by rw [hw1.head]; rcases hc with rfl | rfl <;> simp))
      fun b hb => ?_
    subst hb
    simp only [Bool.false_eq_true, ite_false]
    refine Runs.peek_bind ?_
    simp only [isSym, hw1.head, beq_self_eq_true, ite_true]
    refine Runs.bump_bind ?_
    refine Runs.bind (Runs.acceptSym_false (by
      rw [hk1]; rcases hc with rfl | rfl
      · exact hkc.1
      · exact hkc.2)) fun b hb => ?_
    subst hb
    simp only [Bool.false_eq_true, ite_false]
    have hat : After 0 t := by
      rcases ht with rfl | rfl
      · exact After.comma
      · exact After.close hc
    refine Runs.bind (Runs.argument hEx hpx (R := R') hw2 hat (by omega)
      (fun h => by have := htop h; omega)) fun n hn => ?_
    have hw3 := (hR ▸ hw2).drop
    refine Runs.idx (by omega) (Runs.mono (ih _ _ _ _ (n :: acc) hw3 (by omega)
      (fun h => by have := htop h; omega)) ?_)
    rintro ns ⟨ms, rfl, hm, hh⟩
    refine ⟨n :: ms, by simp, by simp [hm, hn.1], ?_⟩
    intro n' hn'
    simp only [List.mem_cons] at hn'
    rcases hn' with rfl | hn'
    · have := hn.2; omega
    · have := hh n' hn'; omega


theorem Runs.args {close : String} (hc : close = ")" ∨ close = "]") {allowEmpty top : Bool}
    {xs : List Expr} (hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true)
    (hne : xs = [] → allowEmpty = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (hw : Win ctx.input i (argToks (xs.map (Expr.toks 0)) ++ .symbol close :: R))
    (hf : 4 * (argToks (xs.map (Expr.toks 0))).length + 3 ≤ f)
    (htop : top = true → (argToks (xs.map (Expr.toks 0))).length ≤ ctx.depth) :
    Runs (Parse.args f close allowEmpty top) ctx i (i + (argToks (xs.map (Expr.toks 0))).length + 1)
      (fun ns => ns.map (·.expr.erase) = xs.map Expr.erase ∧
        ∀ n ∈ ns, n.height ≤ (argToks (xs.map (Expr.toks 0))).length) := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.args]
  cases xs with
  | nil =>
    simp only [hne rfl, ite_true]
    refine Runs.bind (Runs.acceptSym_true (by simpa [Print.argToks] using hw.head))
      fun b hb => ?_
    subst hb
    exact Runs.pure ⟨rfl, by simp⟩
  | cons x xs =>
    obtain ⟨hEx, hpx⟩ := hE x (by simp)
    have hrest : ∀ y ∈ xs, EGoal y ∧ y.printable = true := fun y hy => hE y (by simp [hy])
    rw [argToks_cons] at hw hf htop ⊢
    rw [List.append_assoc] at hw
    obtain ⟨t, R', hR, ht⟩ := commaToks_next xs close R
    have hw2 := hw
    rw [hR] at hw2
    obtain ⟨k, hk, hkc⟩ := Expr.toks_head x 0
    obtain ⟨ks, hks⟩ : ∃ ks, x.toks 0 = k :: ks := List.head?_eq_some_iff.1 hk
    have hk1 : (tokenAt ctx.input i).kind = k := by
      have := hw2; rw [hks] at this; exact this.head
    have hat : After 0 t := by
      rcases ht with rfl | rfl
      · exact After.comma
      · exact After.close hc
    have main : Runs (do let e ← Parse.argument f top; Parse.argsRest f close top [e]) ctx i
        (i + (x.toks 0 ++ commaToks xs).length + 1)
        (fun ns => ns.map (·.expr.erase) = (x :: xs).map Expr.erase ∧
          ∀ n ∈ ns, n.height ≤ (x.toks 0 ++ commaToks xs).length) := by
      simp only [List.length_append] at hf htop ⊢
      refine Runs.bind (Runs.argument hEx hpx (R := R') hw2 hat (by omega)
        (fun h => by have := htop h; omega)) fun n hn => ?_
      refine Runs.idx (by omega) (Runs.mono (Runs.argsRest hc hrest _ _ _ _ [n] hw.drop
        (by omega) (fun h => by have := htop h; omega)) ?_)
      rintro ns ⟨ms, rfl, hm, hh⟩
      refine ⟨by simp [hm, hn.1], ?_⟩
      intro n' hn'
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.mem_cons] at hn'
      rcases hn' with rfl | hn'
      · have := hn.2; omega
      · have := hh n' hn'; omega
    cases allowEmpty
    · exact main
    · simp only [ite_true]
      refine Runs.bind (Runs.acceptSym_false (by
        rw [hk1]; rcases hc with rfl | rfl
        · exact hkc.1
        · exact hkc.2)) fun b hb => ?_
      subst hb
      exact main


/-! ## Primary forms -/

theorem Runs.ident {ctx : Ctx} {i : Nat} {n : String}
    (h : (tokenAt ctx.input i).kind = .ident n) :
    Runs Parse.ident ctx i (i + 1) (fun id => id.name = n) := by
  unfold Parse.ident
  refine Runs.peek_bind ?_
  simp only [h]
  exact Runs.bump_bind (Runs.pure rfl)

theorem Runs.path {ctx : Ctx} {i : Nat} {n : String}
    (h : (tokenAt ctx.input i).kind = .ident n)
    (h2 : (tokenAt ctx.input (i + 1)).kind ≠ .symbol "::") :
    Runs Parse.path ctx i (i + 1) (fun id => id.name = n) := by
  unfold Parse.path
  refine Runs.bind (Runs.ident h) fun id hid => ?_
  refine Runs.peek_bind ?_
  simp only [isSym, beq_iff_eq, h2, ite_false]
  exact Runs.pure hid

theorem Runs.tupleAhead {ctx : Ctx} {i : Nat}
    (h1 : (tokenAt ctx.input (i + 1)).kind ≠ .symbol ")")
    (h2 : ctx.input.comma.getD i false = false) :
    Runs Parse.tupleAhead ctx i i (· = false) := by
  intro hh
  refine ⟨false, ?_, rfl⟩
  have h1' : isSym ")" (tokenAt ctx.input (i + 1)) = false := by simpa [isSym] using h1
  show Except.ok ((isSym ")" (tokenAt ctx.input (i + 1)) || ctx.input.comma.getD i false), _) = _
  rw [h1', h2]
  rfl

theorem Runs.primary_paren {x : Expr} (hE : EGoal x) (hp : x.printable = true) (ctx : Ctx)
    (i f : Nat) (R : List Kind)
    (hw : Win ctx.input i (.symbol "(" :: (x.toks 0 ++ .symbol ")" :: R)))
    (hf : 4 * (x.toks 0).length + 2 ≤ f) :
    Runs (primary (f + 1)) ctx i (i + (x.toks 0).length + 2)
      (fun r => Res x ((x.toks 0).length + 2) r.1 ∧ r.2 = false) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hw.head]
  have hc := hw.comma [] (x.toks 0) R (by simp) (Expr.trans .comma x 0).seg
  obtain ⟨k, hk, hkc⟩ := Expr.toks_head x 0
  obtain ⟨ks, hks⟩ : ∃ ks, x.toks 0 = k :: ks := List.head?_eq_some_iff.1 hk
  have hw1 := hw.tail
  have hk1 : (tokenAt ctx.input (i + 1)).kind = k := by
    have := hw1; rw [hks] at this; exact this.head
  refine Runs.bind (Runs.tupleAhead (by rw [hk1]; exact hkc.1) (by simpa using hc))
    fun b hb => ?_
  subst hb
  simp only [Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind (hE hp ctx (i + 1) _ R f hw1 (After.close (Or.inl rfl)) (by omega))
    fun n hn => ?_
  have hw2 := hw1.drop
  refine Runs.sym_bind hw2.head ?_
  refine Runs.idx (by omega) (Runs.pure ⟨⟨hn.1, by have := hn.2; simp only; omega⟩, rfl⟩)


theorem Runs.primary_num {ctx : Ctx} {i f v : Nat}
    (hk : (tokenAt ctx.input i).kind = .number v) :
    Runs (primary (f + 1)) ctx i (i + 1)
      (fun r => r.2 = false ∧ r.1.height = 1 ∧ r.1.expr.erase = .num Pos.zero v) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hk]
  exact Runs.bump_bind (Runs.pure ⟨rfl, rfl, by simp [leaf, Expr.erase]⟩)

theorem Runs.primary_str {ctx : Ctx} {i f : Nat} {v : String}
    (hk : (tokenAt ctx.input i).kind = .string v) :
    Runs (primary (f + 1)) ctx i (i + 1)
      (fun r => r.2 = false ∧ r.1.height = 1 ∧ r.1.expr.erase = .str Pos.zero v) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hk]
  exact Runs.bump_bind (Runs.pure ⟨rfl, rfl, by simp [leaf, Expr.erase]⟩)

theorem Runs.primary_bool {ctx : Ctx} {i f : Nat} {v : Bool}
    (hk : (tokenAt ctx.input i).kind = .keyword (boolean v)) :
    Runs (primary (f + 1)) ctx i (i + 1)
      (fun r => r.2 = false ∧ r.1.height = 1 ∧ r.1.expr.erase = .bool Pos.zero v) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  cases v <;> simp only [hk, boolean] <;>
    exact Runs.bump_bind (Runs.pure ⟨rfl, rfl, by simp [leaf, Expr.erase]⟩)

theorem Runs.primary_name {ctx : Ctx} {i f : Nat} {n : String}
    (hk : (tokenAt ctx.input i).kind = .ident n)
    (h2 : (tokenAt ctx.input (i + 1)).kind ≠ .symbol "::") :
    Runs (primary (f + 1)) ctx i (i + 1)
      (fun r => r.2 = true ∧ r.1.height = 1 ∧ r.1.expr.erase = .name Pos.zero n) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hk]
  exact Runs.bind (Runs.path hk h2) fun _ _ =>
    Runs.pure ⟨rfl, rfl, by simp [leaf, Expr.erase]⟩

/-! ## Suffixes -/

theorem Runs.suffixes_stop {ctx : Ctx} {i f : Nat} {start : Pos} {n : Node} {pl : Bool}
    (h : suffixStart (tokenAt ctx.input i).kind = false) :
    Runs (suffixes (f + 1) start n pl) ctx i i (· = (n, pl)) := by
  rw [Parse.suffixes]
  refine Runs.peek_bind ?_
  simp only [suffixStart, Bool.or_eq_false_iff] at h
  simp only [isSym, h.1.1, h.1.2, h.2, Bool.false_eq_true, ite_false]
  exact Runs.pure rfl

theorem Runs.suffixes_call {ctx : Ctx} {i f : Nat} {start : Pos} {n : Node} {pl : Bool}
    {xs : List Expr} (hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true) {R : List Kind}
    (hw : Win ctx.input i (.symbol "(" :: (argToks (xs.map (Expr.toks 0)) ++ .symbol ")" :: R)))
    (hf : 4 * (argToks (xs.map (Expr.toks 0))).length + 3 ≤ f) {l : Nat}
    {Q : Node × Bool → Prop}
    (hk : ∀ ns : List Node, ns.map (·.expr.erase) = xs.map Expr.erase →
      (∀ m ∈ ns, m.height ≤ (argToks (xs.map (Expr.toks 0))).length) →
      Runs (suffixes f start ⟨.call start n.expr (ns.map (·.expr)),
        height (n.height :: ns.map (·.height))⟩ false) ctx
        (i + (argToks (xs.map (Expr.toks 0))).length + 2) l Q) :
    Runs (suffixes (f + 1) start n pl) ctx i l Q := by
  rw [Parse.suffixes]
  refine Runs.peek_bind ?_
  simp only [isSym, hw.head, beq_self_eq_true, ite_true]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.args (Or.inl rfl) (allowEmpty := true) (top := false) hE (fun _ => rfl)
    ctx (i + 1) f R hw.tail hf (by simp)) fun ns hns => ?_
  exact Runs.start (by omega) (hk ns hns.1 hns.2)

theorem Runs.suffixes_index {ctx : Ctx} {i f : Nat} {start : Pos} {n : Node} {pl : Bool}
    {xs : List Expr} (hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true) (hne : xs ≠ [])
    {R : List Kind}
    (hw : Win ctx.input i (.symbol "[" :: (argToks (xs.map (Expr.toks 0)) ++ .symbol "]" :: R)))
    (hf : 4 * (argToks (xs.map (Expr.toks 0))).length + 3 ≤ f) {l : Nat}
    {Q : Node × Bool → Prop}
    (hk : ∀ ns : List Node, ns.map (·.expr.erase) = xs.map Expr.erase →
      (∀ m ∈ ns, m.height ≤ (argToks (xs.map (Expr.toks 0))).length) →
      Runs (suffixes f start ⟨.index start n.expr (ns.map (·.expr)),
        height (n.height :: ns.map (·.height))⟩ pl) ctx
        (i + (argToks (xs.map (Expr.toks 0))).length + 2) l Q) :
    Runs (suffixes (f + 1) start n pl) ctx i l Q := by
  rw [Parse.suffixes]
  refine Runs.peek_bind ?_
  simp only [isSym, hw.head, beq_iff_eq, Kind.symbol.injEq, beq_self_eq_true, ite_true]
  simp only [show ("[" : String) ≠ "(" by decide, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.args (Or.inr rfl) (allowEmpty := false) (top := false) hE
    (fun h => absurd h hne) ctx (i + 1) f R hw.tail hf (by simp)) fun ns hns => ?_
  exact Runs.start (by omega) (hk ns hns.1 hns.2)

theorem Runs.suffixes_field {ctx : Ctx} {i f : Nat} {start : Pos} {n : Node} {pl : Bool}
    {m : String} {t : Kind} {R : List Kind}
    (hw : Win ctx.input i (.symbol "." :: .ident m :: t :: R)) (ht : t ≠ .symbol "(")
    {l : Nat} {Q : Node × Bool → Prop}
    (hk : ∀ p, Runs (suffixes f start ⟨.field start n.expr ⟨p, m⟩, n.height + 1⟩ pl) ctx
        (i + 2) l Q) :
    Runs (suffixes (f + 1) start n pl) ctx i l Q := by
  rw [Parse.suffixes]
  refine Runs.peek_bind ?_
  simp only [isSym, hw.head, beq_iff_eq, Kind.symbol.injEq]
  simp only [show ("." : String) ≠ "(" by decide, show ("." : String) ≠ "[" by decide,
    ite_false, ite_true]
  refine Runs.bump_bind ?_
  refine Runs.peek_bind ?_
  simp only [hw.tail.head]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.acceptSym_false (by rw [hw.tail.tail.head]; exact ht)) fun b hb => ?_
  subst hb
  simp only [Bool.false_eq_true, ite_false]
  exact hk _

theorem Runs.suffixes_method {ctx : Ctx} {i f : Nat} {start : Pos} {n : Node} {pl : Bool}
    {m : String} {xs : List Expr} (hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true) {R : List Kind}
    (hw : Win ctx.input i (.symbol "." :: .ident m :: .symbol "(" ::
      (argToks (xs.map (Expr.toks 0)) ++ .symbol ")" :: R)))
    (hf : 4 * (argToks (xs.map (Expr.toks 0))).length + 3 ≤ f) {l : Nat}
    {Q : Node × Bool → Prop}
    (hk : ∀ p (ns : List Node), ns.map (·.expr.erase) = xs.map Expr.erase →
      (∀ m' ∈ ns, m'.height ≤ (argToks (xs.map (Expr.toks 0))).length) →
      Runs (suffixes f start ⟨.method start n.expr ⟨p, m⟩ (ns.map (·.expr)),
        height (n.height :: ns.map (·.height))⟩ false) ctx
        (i + (argToks (xs.map (Expr.toks 0))).length + 4) l Q) :
    Runs (suffixes (f + 1) start n pl) ctx i l Q := by
  rw [Parse.suffixes]
  refine Runs.peek_bind ?_
  simp only [isSym, hw.head, beq_iff_eq, Kind.symbol.injEq]
  simp only [show ("." : String) ≠ "(" by decide, show ("." : String) ≠ "[" by decide,
    ite_false, ite_true]
  refine Runs.bump_bind ?_
  refine Runs.peek_bind ?_
  simp only [hw.tail.head]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.acceptSym_true hw.tail.tail.head) fun b hb => ?_
  subst hb
  simp only [ite_true]
  refine Runs.bind (Runs.args (Or.inl rfl) (allowEmpty := true) (top := false) hE (fun _ => rfl)
    ctx (i + 1 + 1 + 1) f R hw.tail.tail.tail hf (by simp)) fun ns hns => ?_
  exact Runs.start (by omega) (hk _ ns hns.1 hns.2)


/-! ## Postfix forms -/

theorem height_le {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x ≤ B) : height l ≤ B + 1 := by
  unfold height
  suffices ∀ a, a ≤ B → l.foldl max a ≤ B by have := this 0 (Nat.zero_le _); omega
  induction l with
  | nil => intro a ha; exact ha
  | cons x xs ih =>
    intro a ha
    exact ih (fun y hy => h y (by simp [hy])) _ (Nat.max_le.2 ⟨ha, h x (by simp)⟩)

theorem commaToks_mem {xs : List Expr} {y : Expr} (hy : y ∈ xs) :
    (y.toks 0).length ≤ (commaToks xs).length := by
  induction xs with
  | nil => cases hy
  | cons z zs ih =>
    simp only [List.mem_cons] at hy
    simp only [commaToks, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rcases hy with rfl | hy
    · omega
    · have := ih hy; omega

theorem argToks_mem {xs : List Expr} {y : Expr} (hy : y ∈ xs) :
    (y.toks 0).length ≤ (argToks (xs.map (Expr.toks 0))).length := by
  cases xs with
  | nil => cases hy
  | cons z zs =>
    rw [argToks_cons, List.length_append]
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · omega
    · have := commaToks_mem hy; omega

theorem Expr.toks11_paren (u : Expr) (hl : u.level < 11) :
    u.toks 11 = .symbol "(" :: (u.toks 0 ++ [.symbol ")"]) := by
  rw [Expr.toks_paren]; simp [hl]

theorem Expr.toks11_call_field (p q : Pos) (b : Expr) (m : Ident) (xs : List Expr) :
    (Expr.call p (.field q b m) xs).toks 11 = .symbol "(" :: ((Expr.field q b m).toks 0 ++
      .symbol ")" :: .symbol "(" :: (argToks (xs.map (Expr.toks 0)) ++ [.symbol ")"])) := by
  rw [Expr.toks.eq_def]
  simp [Expr.level, postfixLevel]

theorem Expr.toks11_call (p : Pos) (g : Expr) (xs : List Expr)
    (hg : ∀ q b m, g ≠ .field q b m) :
    (Expr.call p g xs).toks 11 =
      g.toks 11 ++ .symbol "(" :: (argToks (xs.map (Expr.toks 0)) ++ [.symbol ")"]) := by
  rw [Expr.toks.eq_def]
  simp only [Expr.level, postfixLevel, Nat.lt_irrefl, ite_false]
  split
  · rename_i h; obtain ⟨q, b, m, rfl⟩ : ∃ q b m, g = .field q b m := by
      cases g <;> simp_all
    exact absurd rfl (hg q b m)
  · simp

theorem Expr.toks11_index (p : Pos) (b : Expr) (xs : List Expr) :
    (Expr.index p b xs).toks 11 =
      b.toks 11 ++ .symbol "[" :: (argToks (xs.map (Expr.toks 0)) ++ [.symbol "]"]) := by
  simp [Expr.toks, Expr.level, postfixLevel]

theorem Expr.toks11_method (p : Pos) (r : Expr) (m : Ident) (xs : List Expr) :
    (Expr.method p r m xs).toks 11 = r.toks 11 ++ .symbol "." :: .ident m.name :: .symbol "(" ::
      (argToks (xs.map (Expr.toks 0)) ++ [.symbol ")"]) := by
  simp [Expr.toks, Expr.level, postfixLevel]

theorem Expr.toks11_field (p : Pos) (b : Expr) (m : Ident) :
    (Expr.field p b m).toks 11 = b.toks 11 ++ [.symbol ".", .ident m.name] := by
  simp [Expr.toks, Expr.level, postfixLevel]

/-! ## Containers -/

theorem Runs.tupleAhead_true {ctx : Ctx} {i : Nat}
    (h : (tokenAt ctx.input (i + 1)).kind = .symbol ")" ∨ ctx.input.comma.getD i false = true) :
    Runs Parse.tupleAhead ctx i i (· = true) := by
  intro hh
  refine ⟨true, ?_, rfl⟩
  show Except.ok ((isSym ")" (tokenAt ctx.input (i + 1)) || ctx.input.comma.getD i false), _) = _
  rcases h with h | h
  · have h1 : isSym ")" (tokenAt ctx.input (i + 1)) = true := by simp [isSym, h]
    rw [h1, Bool.true_or]
  · rw [h, Bool.or_true]

theorem Runs.arrayTypeAhead {ctx : Ctx} {i : Nat} (h : ctx.input.semi.getD i false = false) :
    Runs Parse.arrayTypeAhead ctx i i (· = false) := by
  intro hh
  refine ⟨false, ?_, rfl⟩
  show Except.ok (ctx.input.semi.getD i false, _) = _
  rw [h]

/-! The elements of a tuple of one element: the element, `,`, and `)`. -/
theorem Runs.args_trail {x : Expr} (hE : EGoal x) (hp : x.printable = true) (ctx : Ctx)
    (i f : Nat) (R : List Kind)
    (hw : Win ctx.input i (x.toks 0 ++ .symbol "," :: .symbol ")" :: R))
    (hf : 4 * (x.toks 0).length + 4 ≤ f) :
    Runs (Parse.args f ")" true false) ctx i (i + (x.toks 0).length + 2)
      (fun ns => ns.map (·.expr.erase) = [x.erase] ∧
        ∀ n ∈ ns, n.height ≤ (x.toks 0).length) := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.args]
  obtain ⟨k, hk, hkc⟩ := Expr.toks_head x 0
  obtain ⟨ks, hks⟩ : ∃ ks, x.toks 0 = k :: ks := List.head?_eq_some_iff.1 hk
  have hk1 : (tokenAt ctx.input i).kind = k := by
    have := hw; rw [hks] at this; exact this.head
  simp only [ite_true]
  refine Runs.bind (Runs.acceptSym_false (by rw [hk1]; exact hkc.1)) fun b hb => ?_
  subst hb
  simp only [Bool.false_eq_true, ite_false]
  refine Runs.bind (Runs.argument hE hp (top := false) hw After.comma (by omega)
    (fun h => by cases h)) fun n hn => ?_
  have hw2 := hw.drop
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.argsRest]
  refine Runs.bind (Runs.acceptSym_false (by rw [hw2.head]; decide)) fun b hb => ?_
  subst hb
  simp only [Bool.false_eq_true, ite_false]
  refine Runs.peek_bind ?_
  simp only [isSym, hw2.head, beq_self_eq_true, ite_true]
  refine Runs.bump_bind ?_
  refine Runs.bind (Runs.acceptSym_true hw2.tail.head) fun b hb => ?_
  subst hb
  simp only [ite_true]
  refine Runs.idx (by omega) (Runs.pure ⟨by simp [hn.1], ?_⟩)
  simpa using hn.2

/-! `()` or a tuple: `tupleAhead` holds, then the elements up to `)`. -/
theorem Runs.primary_tuple {xs : List Expr} {ctx : Ctx} {i f T B : Nat}
    (hk : (tokenAt ctx.input i).kind = .symbol "(")
    (hta : (tokenAt ctx.input (i + 1)).kind = .symbol ")" ∨ ctx.input.comma.getD i false = true)
    (hargs : Runs (Parse.args f ")" true false) ctx (i + 1) (i + T)
      (fun ns => ns.map (·.expr.erase) = xs.map Expr.erase ∧ ∀ n ∈ ns, n.height ≤ B)) :
    Runs (primary (f + 1)) ctx i (i + T) (fun r => r.2 = false ∧
      (xs = [] → r.1.expr.erase = .unit Pos.zero) ∧
      (xs ≠ [] → r.1.expr.erase = .tuple Pos.zero (xs.map Expr.erase)) ∧
      r.1.height ≤ B + 1) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hk]
  refine Runs.bind (Runs.tupleAhead_true hta) fun b hb => ?_
  subst hb
  simp only [ite_true]
  refine Runs.bump_bind ?_
  refine Runs.bind hargs fun ns hns => Runs.pure ?_
  cases ns with
  | nil =>
    have hx : xs = [] := by simpa using hns.1.symm
    subst hx
    exact ⟨rfl, fun _ => by simp [leaf, Expr.erase], fun h => absurd rfl h, by simp [leaf]⟩
  | cons n ns =>
    refine ⟨rfl, fun h => by subst h; simp at hns, fun _ => ?_, ?_⟩
    · simp only [Expr.erase, List.map_map, Function.comp_def]
      rw [← hns.1]
    · refine height_le fun x hx => ?_
      simp only [List.map_cons, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨m, hm, rfl⟩
      · exact hns.2 n (by simp)
      · exact hns.2 m (by simp [hm])

/-! An array: no `;` in its brackets, then the elements up to `]`. -/
theorem Runs.primary_array {xs : List Expr} {ctx : Ctx} {i f T B : Nat}
    (hk : (tokenAt ctx.input i).kind = .symbol "[")
    (hs : ctx.input.semi.getD i false = false)
    (hargs : Runs (Parse.args f "]" true false) ctx (i + 1) (i + T)
      (fun ns => ns.map (·.expr.erase) = xs.map Expr.erase ∧ ∀ n ∈ ns, n.height ≤ B)) :
    Runs (primary (f + 1)) ctx i (i + T) (fun r => r.2 = false ∧
      r.1.expr.erase = .array Pos.zero (xs.map Expr.erase) ∧ r.1.height ≤ B + 1) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hk]
  refine Runs.bind (Runs.arrayTypeAhead hs) fun b hb => ?_
  subst hb
  simp only [Bool.false_eq_true, ite_false]
  refine Runs.bump_bind ?_
  refine Runs.bind hargs fun ns hns => Runs.pure ⟨rfl, ?_, ?_⟩
  · simp only [Expr.erase, List.map_map, Function.comp_def]
    rw [← hns.1]
  · refine height_le fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact hns.2 m hm

theorem Runs.suffixes_select {ctx : Ctx} {i f : Nat} {start : Pos} {n : Node} {pl : Bool}
    {v : Nat} {R : List Kind} (hw : Win ctx.input i (.symbol "." :: .number v :: R))
    {l : Nat} {Q : Node × Bool → Prop}
    (hk : ∀ p, Runs (suffixes f start ⟨.select start n.expr p v, n.height + 1⟩ pl) ctx
        (i + 2) l Q) :
    Runs (suffixes (f + 1) start n pl) ctx i l Q := by
  rw [Parse.suffixes]
  refine Runs.peek_bind ?_
  simp only [isSym, hw.head, beq_iff_eq, Kind.symbol.injEq]
  simp only [show ("." : String) ≠ "(" by decide, show ("." : String) ≠ "[" by decide,
    ite_false, ite_true]
  refine Runs.bump_bind ?_
  refine Runs.peek_bind ?_
  simp only [hw.tail.head]
  refine Runs.bump_bind ?_
  exact hk _

/-- The precondition of `Runs.type` on `ty`. -/
def TGoal (ty : TypeExpr) : Prop :=
  ty.printable = true → ∀ (ctx : Ctx) (i f : Nat) (u : Kind) (R : List Kind),
    Win ctx.input i (ty.toks ++ u :: R) → u ≠ .symbol "::" → 4 * ty.toks.length ≤ f + 2 →
    ∀ (l : Nat) (Q : TypeExpr × Nat → Prop),
    (∀ ty' h f', ty'.erase = ty.erase → h ≤ ty.toks.length →
      2 * f ≤ 2 * f' + ty.toks.length + 1 →
      Runs (typeSuffix f' (tokenAt ctx.input i).pos (ty', h)) ctx (i + ty.toks.length) l Q) →
    Runs (typeExpr f) ctx i l Q

/-! The first kind of a type is no closing bracket. -/
theorem TypeExpr.toks_head (ty : TypeExpr) : ∃ k ks, ty.toks = k :: ks ∧ NotClose k := by
  induction ty using TypeExpr.ind with
  | case2 p b xs ihb =>
    obtain ⟨k, ks, h, hk⟩ := ihb
    exact ⟨k, ks ++ .symbol "[" :: argToks (xs.map (Expr.toks 0)) ++ [.symbol "]"],
      by simp [TypeExpr.toks, h], hk⟩
  | case1 => exact ⟨_, [], by rw [TypeExpr.toks], by simp [NotClose]⟩
  | case3 => exact ⟨.symbol "(", _, by rw [TypeExpr.toks], by simp [NotClose]⟩
  | case4 => exact ⟨.symbol "(", _, by rw [TypeExpr.toks, List.cons_append], by simp [NotClose]⟩
  | case5 =>
    exact ⟨.symbol "[", _, by rw [TypeExpr.toks, List.cons_append, List.cons_append],
      by simp [NotClose]⟩

/-! A type, then a kind that is no `[`, no `(`, and no `::`. -/
theorem TGoal.type_end {ty : TypeExpr} (hT : TGoal ty) (hp : ty.printable = true) (ctx : Ctx)
    (i f : Nat) (u : Kind) (R : List Kind) (hw : Win ctx.input i (ty.toks ++ u :: R))
    (hu : u ≠ .symbol "[" ∧ u ≠ .symbol "(" ∧ u ≠ .symbol "::") (hf : 4 * ty.toks.length ≤ f) :
    Runs (typeExpr f) ctx i (i + ty.toks.length)
      (fun r => r.1.erase = ty.erase ∧ r.2 ≤ ty.toks.length) := by
  have h1 : 1 ≤ ty.toks.length := by
    obtain ⟨k, ks, h, -⟩ := TypeExpr.toks_head ty; rw [h]; simp
  refine hT hp ctx i f u R hw hu.2.2 (by omega) _ _ ?_
  intro ty' h f' hty hh hf'
  obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
  rw [Parse.typeSuffix]
  refine Runs.peek_bind ?_
  have hw2 := hw.drop
  simp only [isSym, hw2.head, beq_iff_eq, hu.1, hu.2.1, ite_false]
  exact Runs.pure ⟨hty, hh⟩

/-! The end of a tuple type: a `)`, after a `,` if `trail`. -/
def tupleTail (trail : Bool) (R : List Kind) : List Kind :=
  (if trail then [.symbol ","] else []) ++ .symbol ")" :: R

theorem argToks_single (a : List Kind) : argToks [a] = a := by simp [Print.argToks]

theorem argToks_cons_cons (a b : List Kind) (l : List (List Kind)) :
    argToks (a :: b :: l) = a ++ .symbol "," :: argToks (b :: l) := by
  simp [Print.argToks, List.intercalate_cons_cons]

theorem argToks_length_le {l : List (List Kind)} {x : List Kind} (hx : x ∈ l) :
    x.length ≤ (argToks l).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    cases ys with
    | nil =>
      rcases hx with rfl | hx
      · simp [Print.argToks]
      · cases hx
    | cons z zs =>
      rw [argToks_cons_cons, List.length_append, List.length_cons]
      rcases hx with rfl | hx
      · omega
      · have := ih hx; omega

theorem argToks_head (a : List Kind) (l : List (List Kind)) :
    ∃ r, argToks (a :: l) = a ++ r := by
  cases l with
  | nil => exact ⟨[], by simp [Print.argToks]⟩
  | cons b l => exact ⟨_, argToks_cons_cons a b l⟩

/-! `typeElems` reads the element types of a tuple type up to its `)`. -/
theorem Runs.typeElems (trail : Bool) (ts : List TypeExpr) (hne : ts ≠ [])
    (hT : ∀ t ∈ ts, TGoal t ∧ t.printable = true) :
    ∀ (ctx : Ctx) (i f : Nat) (R : List Kind) (acc : List (TypeExpr × Nat)),
    Win ctx.input i (argToks (ts.map TypeExpr.toks) ++ tupleTail trail R) →
    4 * (argToks (ts.map TypeExpr.toks)).length + 4 ≤ f →
    Runs (typeElems f acc) ctx i
      (i + (argToks (ts.map TypeExpr.toks)).length + (if trail then 2 else 1))
      (fun rs => ∃ ms, rs = acc.reverse ++ ms ∧ ms.map (·.1.erase) = ts.map TypeExpr.erase ∧
        ∀ r ∈ ms, r.2 ≤ (argToks (ts.map TypeExpr.toks)).length) := by
  induction ts with
  | nil => exact absurd rfl hne
  | cons t ts ih =>
    intro ctx i f R acc hw hf
    obtain ⟨hTt, hpt⟩ := hT t (by simp)
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.typeElems]
    cases ts with
    | nil =>
      simp only [List.map_cons, List.map_nil, Print.argToks, List.intercalate_singleton] at hw hf ⊢
      cases trail
      · simp only [tupleTail, Bool.false_eq_true, ite_false, List.nil_append] at hw ⊢
        refine Runs.bind (TGoal.type_end hTt hpt ctx i f _ R hw (by decide) (by omega))
          fun r hr => ?_
        refine Runs.bind (Runs.acceptSym_true hw.drop.head) fun b hb => ?_
        subst hb
        exact Runs.pure ⟨[r], by simp, by simp [hr.1], by simpa using hr.2⟩
      · simp only [tupleTail, ite_true, List.singleton_append] at hw ⊢
        refine Runs.bind (TGoal.type_end hTt hpt ctx i f _ _ hw (by decide) (by omega))
          fun r hr => ?_
        have hw2 := hw.drop
        refine Runs.bind (Runs.acceptSym_false (by rw [hw2.head]; decide)) fun b hb => ?_
        subst hb
        simp only [Bool.false_eq_true, ite_false]
        refine Runs.peek_bind ?_
        simp only [isSym, hw2.head, beq_self_eq_true, ite_true]
        refine Runs.bump_bind ?_
        refine Runs.bind (Runs.acceptSym_true hw2.tail.head) fun b hb => ?_
        subst hb
        refine Runs.idx (by omega) (Runs.pure ⟨[r], by simp, by simp [hr.1], ?_⟩)
        simpa using hr.2
    | cons t2 ts =>
      have hrest : ∀ y ∈ t2 :: ts, TGoal y ∧ y.printable = true := fun y hy =>
        hT y (by simp [hy])
      simp only [List.map_cons] at hw hf ih ⊢
      rw [argToks_cons_cons] at hw hf ⊢
      simp only [List.length_append, List.length_cons] at hf ⊢
      rw [List.append_assoc] at hw
      refine Runs.bind (TGoal.type_end hTt hpt ctx i f _ _ hw (by decide) (by omega))
        fun r hr => ?_
      have hw2 := hw.drop
      refine Runs.bind (Runs.acceptSym_false (by rw [hw2.head]; decide)) fun b hb => ?_
      subst hb
      simp only [Bool.false_eq_true, ite_false]
      refine Runs.peek_bind ?_
      simp only [isSym, hw2.head, beq_self_eq_true, ite_true]
      refine Runs.bump_bind ?_
      obtain ⟨k, ks, hks, hk⟩ := TypeExpr.toks_head t2
      have hw3 := hw2.tail
      have hk1 : (tokenAt ctx.input (i + t.toks.length + 1)).kind = k := by
        obtain ⟨r', hr'⟩ := argToks_head t2.toks (ts.map TypeExpr.toks)
        have := hw3; rw [hr', hks] at this; simp only [List.cons_append] at this
        exact this.head
      refine Runs.bind (Runs.acceptSym_false (by rw [hk1]; exact hk.1)) fun b hb => ?_
      subst hb
      simp only [Bool.false_eq_true, ite_false]
      refine Runs.idx (by split <;> omega) (Runs.mono (ih (by simp) hrest ctx _ f R (r :: acc)
        hw3 (by omega)) ?_)
      rintro rs ⟨ms, rfl, hm, hh⟩
      refine ⟨r :: ms, by simp, by simp [hm, hr.1], ?_⟩
      intro r' hr'
      simp only [List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · have := hr.2; omega
      · have := hh r' hr'; omega

/-!
`typeExpr` reads a type back to it, if `expr` reads each expression with fewer kinds than the
bound `B`. An array type in an expression needs this form: its element is a type.
-/
theorem Runs.type_of (B : Nat) (hE : ∀ x, (x.toks 0).length < B → EGoal x) (ty : TypeExpr) :
    ty.toks.length ≤ B → TGoal ty := by
  induction ty using TypeExpr.ind with
  | case3 p =>
    intro _ _ ctx i f u R hw hu hf l Q hk
    simp only [TypeExpr.toks, List.length_cons, List.length_nil, List.cons_append,
      List.nil_append] at hw hf hk
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.typeExpr]
    refine Runs.peek_bind ?_
    simp only [hw.head]
    refine Runs.bind (Runs.tupleAhead_true (Or.inl hw.tail.head)) fun b hb => ?_
    subst hb
    simp only [ite_true]
    refine Runs.bump_bind ?_
    refine Runs.bind (Runs.acceptSym_true hw.tail.head) fun b hb => ?_
    subst hb
    simp only [ite_true]
    exact Runs.idx (by omega) (hk _ 1 f (by simp [TypeExpr.erase]) (by omega) (by omega))
  | case4 p ts ih =>
    intro hB hp ctx i f u R hw hu hf l Q hk
    simp only [TypeExpr.printable, Bool.and_eq_true, TypeExpr.printableAll_eq,
      List.all_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨hne, hpts⟩ := hp
    have hlt : (argToks (ts.map TypeExpr.toks)).length < (TypeExpr.tuple p ts).toks.length := by
      simp only [TypeExpr.toks]; split <;> simp <;> omega
    have hT : ∀ t ∈ ts, TGoal t ∧ t.printable = true := fun t ht =>
      ⟨ih t ht (by have := argToks_length_le (List.mem_map_of_mem (f := TypeExpr.toks) ht); omega),
        hpts t ht⟩
    have htoks : (TypeExpr.tuple p ts).toks =
        .symbol "(" :: (argToks (ts.map TypeExpr.toks) ++ tupleTail (ts.length == 1) []) := by
      simp only [TypeExpr.toks, tupleTail]
      split <;> simp_all
    have hlen : (TypeExpr.tuple p ts).toks.length =
        (argToks (ts.map TypeExpr.toks)).length + (if ts.length == 1 then 2 else 1) + 1 := by
      rw [htoks]; simp only [tupleTail]; split <;> simp
    have hw' : Win ctx.input i (.symbol "(" :: (argToks (ts.map TypeExpr.toks) ++
        tupleTail (ts.length == 1) (u :: R))) := by
      rw [htoks] at hw; simpa [tupleTail] using hw
    rw [hlen] at hf hk
    obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := List.exists_cons_of_ne_nil hne
    obtain ⟨k, ks, hks, hkc⟩ := TypeExpr.toks_head t
    have hta : ctx.input.comma.getD i false = true := by
      have e : ∃ b, Kind.symbol "(" :: (argToks ((t :: ts').map TypeExpr.toks) ++
          tupleTail ((t :: ts').length == 1) (u :: R)) =
          [] ++ .symbol "(" :: (t.toks ++ .symbol "," :: b) := by
        cases ts' with
        | nil => exact ⟨.symbol ")" :: u :: R, by simp [Print.argToks, tupleTail]⟩
        | cons t2 ts' =>
          exact ⟨argToks ((t2 :: ts').map TypeExpr.toks) ++ tupleTail false (u :: R),
            by simp [argToks_cons_cons, tupleTail]⟩
      obtain ⟨b, e⟩ := e
      simpa using hw'.tuple _ _ _ e (TypeExpr.trans .none t).bal
    have hk1 : (tokenAt ctx.input (i + 1)).kind = k := by
      obtain ⟨r', hr'⟩ := argToks_head t.toks (ts'.map TypeExpr.toks)
      have := hw'.tail; simp only [List.map_cons] at this; rw [hr', hks] at this
      simp only [List.cons_append] at this
      exact this.head
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by split at hf <;> omega⟩
    rw [Parse.typeExpr]
    refine Runs.peek_bind ?_
    simp only [hw'.head]
    refine Runs.bind (Runs.tupleAhead_true (Or.inr hta)) fun b hb => ?_
    subst hb
    simp only [ite_true]
    refine Runs.bump_bind ?_
    refine Runs.bind (Runs.acceptSym_false (by rw [hk1]; exact hkc.1)) fun b hb => ?_
    subst hb
    simp only [Bool.false_eq_true, ite_false]
    refine Runs.bind (Runs.typeElems _ _ hne hT ctx (i + 1) f (u :: R) [] hw'.tail
      (by split at hf <;> omega)) fun rs hrs => ?_
    obtain ⟨ms, rfl, hm, hh⟩ := hrs
    refine Runs.start ?_ (hk _ _ f ?_ ?_ ?_)
    · split <;> omega
    · simp only [TypeExpr.erase, List.map_map, Function.comp_def]
      rw [← hm]
    · refine Nat.le_trans (height_le (B := (argToks ((t :: ts').map TypeExpr.toks)).length)
        ?_) (by omega)
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨m, hm', rfl⟩ := hx
      exact hh m hm'
    · split <;> omega
  | case5 p t n iht =>
    intro hB hp ctx i f u R hw hu hf l Q hk
    simp only [TypeExpr.printable, Bool.and_eq_true] at hp
    simp only [TypeExpr.toks, List.length_cons, List.length_append, List.length_nil,
      List.cons_append, List.append_assoc, List.nil_append] at hw hf hk hB
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.typeExpr]
    refine Runs.peek_bind ?_
    simp only [hw.head]
    refine Runs.bump_bind ?_
    refine Runs.bind (TGoal.type_end (iht (by omega)) hp.1 ctx (i + 1) f _ _ hw.tail (by decide)
      (by omega))
      ?_
    rintro ⟨ty', h⟩ ⟨hty, hh⟩
    have hw2 := hw.tail.drop
    refine Runs.sym_bind hw2.head ?_
    refine Runs.bind (hE n (by omega) hp.2 ctx _ _ (u :: R) f hw2.tail
      (After.close (Or.inr rfl)) (by omega)) fun m hm => ?_
    have hw3 := hw2.tail.drop
    refine Runs.sym_bind hw3.head ?_
    refine Runs.start (by omega) (hk _ _ f ?_ ?_ (by omega))
    · simp [TypeExpr.erase, hty, hm.1]
    · refine Nat.le_trans (height_le (B := t.toks.length + (n.toks 0).length) ?_) (by omega)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · omega
      · have := hm.2; omega
  | case1 p n =>
    intro _ _ ctx i f u R hw hu hf l Q hk
    simp only [TypeExpr.toks, List.length_singleton, List.singleton_append] at hw hf hk
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.typeExpr]
    refine Runs.peek_bind ?_
    simp only [hw.head]
    refine Runs.bind (Runs.path hw.head (by rw [hw.tail.head]; exact hu)) fun _ _ => ?_
    exact hk _ 1 f (by simp [TypeExpr.erase]) (Nat.le_refl _) (by omega)
  | case2 p b xs ihb =>
    intro hB hp ctx i f u R hw hu hf l Q hk
    simp only [TypeExpr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨⟨hpb, hne⟩, hpxs⟩ := hp
    simp only [TypeExpr.toks, List.length_append, List.length_cons, List.length_nil] at hw hf hk hB
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
      ⟨hE x (by have := argToks_mem hx; omega), hpxs x hx⟩
    refine ihb (by omega) hpb ctx i f (.symbol "[") _ hw (by decide) (by omega) l Q ?_
    intro ty' h f' hty hh hf'
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [Parse.typeSuffix]
    refine Runs.peek_bind ?_
    have hw2 := hw.drop
    simp only [isSym, hw2.head, beq_self_eq_true, ite_true]
    refine Runs.bump_bind ?_
    refine Runs.bind (Runs.args (Or.inr rfl) (allowEmpty := false) (top := false) hE
      (fun h => absurd h hne) ctx _ f'' _ hw2.tail (by omega) (by simp)) fun ns hns => ?_
    refine Runs.start (by omega) (hk _ _ f'' ?_ ?_ (by omega))
    · simp only [TypeExpr.erase, hty, List.map_map, Function.comp_def]
      rw [← hns.1]
    · refine Nat.le_trans (height_le (B := b.toks.length +
        (argToks (List.map (Expr.toks 0) xs)).length + 1) ?_) (by omega)
      intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨m', hm', rfl⟩
      · omega
      · have := hns.2 m' hm'; omega

theorem Runs.arrayTypeAhead_true {ctx : Ctx} {i : Nat}
    (h : ctx.input.semi.getD i false = true) : Runs Parse.arrayTypeAhead ctx i i (· = true) := by
  intro hh
  refine ⟨true, ?_, rfl⟩
  show Except.ok (ctx.input.semi.getD i false, _) = _
  rw [h]

/-! An array type in an expression: a `;` in its brackets, the element type, `;`, the length. -/
theorem Runs.primary_arrayType {t : TypeExpr} {n : Expr} (hT : TGoal t) (hpt : t.printable = true)
    (hE : EGoal n) (hpn : n.printable = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (hw : Win ctx.input i (.symbol "[" :: (t.toks ++ .symbol ";" :: (n.toks 0 ++
      .symbol "]" :: R))))
    (hs : ctx.input.semi.getD i false = true)
    (hf : 4 * (t.toks.length + (n.toks 0).length) + 2 ≤ f) :
    Runs (primary (f + 1)) ctx i (i + (t.toks.length + (n.toks 0).length + 3)) (fun r =>
      r.2 = false ∧ r.1.expr.erase = .arrayType Pos.zero t.erase n.erase ∧
        r.1.height ≤ t.toks.length + (n.toks 0).length + 1) := by
  rw [Parse.primary]
  refine Runs.peek_bind ?_
  simp only [hw.head]
  refine Runs.bind (Runs.arrayTypeAhead_true hs) fun b hb => ?_
  subst hb
  simp only [ite_true]
  refine Runs.bump_bind ?_
  refine Runs.bind (TGoal.type_end hT hpt ctx (i + 1) f _ _ hw.tail (by decide) (by omega)) ?_
  rintro ⟨ty', h⟩ ⟨hty, hh⟩
  have hw2 := hw.tail.drop
  refine Runs.sym_bind hw2.head ?_
  refine Runs.bind (hE hpn ctx _ _ R f hw2.tail (After.close (Or.inr rfl)) (by omega))
    fun m hm => ?_
  refine Runs.sym_bind hw2.tail.drop.head (Runs.idx (by omega) (Runs.pure ⟨rfl, ?_, ?_⟩))
  · simp [Expr.erase, hty, hm.1]
  · refine Nat.le_trans (height_le (B := t.toks.length + (n.toks 0).length) ?_) (by omega)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · omega
    · have := hm.2; omega

theorem Runs.postfix_base {ctx : Ctx} {i f T l : Nat} {u : Expr} {pl : Bool}
    {Q : Node × Bool → Prop}
    (hpr : Runs (primary f) ctx i (i + T) (fun r => Res u T r.1 ∧ r.2 = pl))
    (hk : ∀ n f', Res u T n → f = f' →
      Runs (suffixes f' (tokenAt ctx.input i).pos n pl) ctx (i + T) l Q) :
    Runs (postfixExpr (f + 1)) ctx i l Q := by
  rw [Parse.postfixExpr]
  refine Runs.peek_bind ?_
  refine Runs.bind hpr ?_
  rintro ⟨n, pl'⟩ ⟨hres, rfl⟩
  exact hk n f hres rfl


/-- The suffix continuation of `Runs.postfix`. -/
def SufK (u : Expr) (ctx : Ctx) (i f l : Nat) (Q : Node × Bool → Prop) : Prop :=
  ∀ n f', Res u (u.toks 11).length n → 2 * f ≤ 2 * f' + (u.toks 11).length + 1 →
    Runs (suffixes f' (tokenAt ctx.input i).pos n u.place) ctx (i + (u.toks 11).length) l Q

/-- The precondition of `Runs.postfix` on `u`. -/
def PGoal (u : Expr) : Prop :=
  u.printable = true → (∀ x, (x.toks 0).length < (u.toks 11).length → EGoal x) →
    ∀ (ctx : Ctx) (i f : Nat) (t : Kind) (R : List Kind),
    Win ctx.input i (u.toks 11 ++ t :: R) → t ≠ .symbol "::" →
    (∀ p b m, u = .field p b m → t ≠ .symbol "(") →
    4 * (u.toks 11).length ≤ f + 2 →
    ∀ (l : Nat) (Q : Node × Bool → Prop), SufK u ctx i f l Q → Runs (postfixExpr f) ctx i l Q

theorem Runs.postfix_paren (u : Expr) (hl : u.level < 11) (hpl : u.place = false) : PGoal u := by
  intro hp hIH ctx i f t R hw _ _ hf l Q hk
  unfold SufK at hk
  rw [Expr.toks11_paren u hl] at hw hf hk hIH
  simp only [List.length_cons, List.length_append] at hf hk hIH
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp only [List.cons_append, List.append_assoc] at hw
  obtain ⟨g, rfl⟩ : ∃ g', f = g' + 1 := ⟨f - 1, by omega⟩
  refine Runs.postfix_base (T := (u.toks 0).length + 2) (pl := false)
    (Runs.idx (by omega) (Runs.primary_paren (hIH u (by omega)) hp ctx i g _ hw (by omega))) ?_
  intro n f' hn hf'
  rw [hpl] at hk
  exact Runs.idx (by omega) (hk n f' hn (by omega))

theorem Runs.postfix (u : Expr) : PGoal u := by
  induction u using Expr.ind with
  | case16 p r m xs ihr _ =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true] at hp
    obtain ⟨⟨hpr, -⟩, hpxs⟩ := hp
    rw [Expr.toks11_method] at hw hf hk hIH
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
      ⟨hIH x (by have := argToks_mem hx; omega), hpxs x hx⟩
    refine ihr hpr (fun x hx => hIH x (by omega)) ctx i f (.symbol ".") _ hw (by decide)
      (fun q b m _ => by decide) (by omega) l Q ?_
    intro n f' hn hf'
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    refine Runs.suffixes_method hE hw.drop (by omega) ?_
    intro pos ns hns hh
    have hres : (Expr.method (tokenAt ctx.input i).pos n.expr ⟨pos, m.name⟩
        (ns.map (·.expr))).erase = (Expr.method p r m xs).erase := by
      simp only [Expr.erase, hn.1, List.map_map, Function.comp_def, Ident.erase]
      rw [← hns]
    refine Runs.start (by omega) (hk _ f'' ⟨hres, ?_⟩ (by omega))
    refine Nat.le_trans (height_le (B := (Expr.toks 11 r).length +
      (argToks (List.map (Expr.toks 0) xs)).length + 3) ?_) (by omega)
    intro x hx
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨m', hm', rfl⟩
    · have := hn.2; omega
    · have := hh m' hm'; omega
  | case15 p t n _ =>
    intro hp hIH ctx i f u R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true] at hp
    have hT : (Expr.arrayType p t n).toks 11 =
        .symbol "[" :: (t.toks ++ .symbol ";" :: (n.toks 0 ++ [.symbol "]"])) := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk hIH
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have hTt : TGoal t := Runs.type_of _ hIH t (by omega)
    have hs : ctx.input.semi.getD i false = true := by
      simpa using hw.arrayType [] t.toks (n.toks 0 ++ .symbol "]" :: u :: R) (by simp)
        (TypeExpr.trans .none t).bal
    refine Runs.postfix_base (T := t.toks.length + (n.toks 0).length + 3)
      (u := .arrayType p t n) (pl := false)
      (Runs.mono (Runs.primary_arrayType hTt hp.1 (hIH n (by omega)) hp.2 ctx i f _ hw hs
        (by omega)) ?_) ?_
    · rintro r ⟨h1, h2, h3⟩
      exact ⟨⟨by simp [h2, Expr.erase], by omega⟩, h1⟩
    · intro n' f' hn hf'; exact hk n' f' hn (by omega)
  | case11 p =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    have hT : (Expr.unit p).toks 11 = [.symbol "(", .symbol ")"] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk
    simp only [List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have hargs := Runs.args (xs := []) (Or.inl rfl) (allowEmpty := true) (top := false)
      (fun _ h => by cases h) (fun _ => rfl) ctx (i + 1) f (t :: R)
      (by simpa [Print.argToks] using hw.tail) (by simp [Print.argToks]; omega) (by simp)
    refine Runs.postfix_base (T := 2) (u := .unit p) (pl := false)
      (Runs.mono (Runs.primary_tuple (xs := []) hw.head (Or.inl hw.tail.head)
        (Runs.idx (by simp [Print.argToks]) hargs)) ?_) ?_
    · rintro r ⟨h1, h2, -, h4⟩
      exact ⟨⟨by simp [h2 rfl, Expr.erase], by simp [Print.argToks] at h4; omega⟩, h1⟩
    · intro n f' hn hf'; exact hk n f' hn (by simp; omega)
  | case12 p xs _ =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨hne, hpxs⟩ := hp
    have hres : ∀ r : Node × Bool, r.1.expr.erase = .tuple Pos.zero (xs.map Expr.erase) →
        r.1.expr.erase = (Expr.tuple p xs).erase := fun r h => by
      simp [h, Expr.erase]
    by_cases h1 : xs.length = 1
    · obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
        match xs, h1 with
        | [x], _ => exact ⟨x, rfl⟩
      have hT : (Expr.tuple p [x]).toks 11 =
          .symbol "(" :: (x.toks 0 ++ [.symbol ",", .symbol ")"]) := by
        simp [Expr.toks, Expr.level, postfixLevel, Print.argToks]
      rw [hT] at hw hf hk hIH
      simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
      have hEx : EGoal x := hIH x (by omega)
      have hpx := hpxs x (by simp)
      have hta : ctx.input.comma.getD i false = true := by
        simpa using hw.tuple [] (x.toks 0) (.symbol ")" :: t :: R) (by simp)
          (Expr.trans .none x 0).bal
      have hargs := Runs.args_trail hEx hpx ctx (i + 1) f (t :: R) hw.tail (by omega)
      refine Runs.postfix_base (T := (x.toks 0).length + 3) (u := .tuple p [x]) (pl := false)
        (Runs.mono (Runs.primary_tuple (xs := [x]) hw.head (Or.inr hta)
          (Runs.idx (by omega) hargs)) ?_) ?_
      · rintro r ⟨h1, -, h3, h4⟩
        exact ⟨⟨hres r (h3 (by simp)), by omega⟩, h1⟩
      · intro n f' hn hf'; exact hk n f' hn (by omega)
    · have hT : (Expr.tuple p xs).toks 11 =
          .symbol "(" :: (argToks (xs.map (Expr.toks 0)) ++ [.symbol ")"]) := by
        have : (xs.length == 1) = false := by simpa using h1
        simp [Expr.toks, Expr.level, postfixLevel, this]
      rw [hT] at hw hf hk hIH
      simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
      have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
        ⟨hIH x (by have := argToks_mem hx; omega), hpxs x hx⟩
      obtain ⟨x, y, ys, rfl⟩ : ∃ x y ys, xs = x :: y :: ys := by
        match xs, hne, h1 with
        | x :: y :: ys, _, _ => exact ⟨x, y, ys, rfl⟩
        | [_], _, h => exact absurd rfl h
      have hta : ctx.input.comma.getD i false = true := by
        have e : Kind.symbol "(" :: (argToks ((x :: y :: ys).map (Expr.toks 0)) ++
            .symbol ")" :: t :: R) = [] ++ .symbol "(" :: (x.toks 0 ++ .symbol "," ::
              (y.toks 0 ++ commaToks ys ++ .symbol ")" :: t :: R)) := by
          rw [argToks_cons]; simp [commaToks]
        simpa using hw.tuple _ _ _ e (Expr.trans .none x 0).bal
      have hargs := Runs.args (Or.inl rfl) (allowEmpty := true) (top := false) hE
        (fun _ => rfl) ctx (i + 1) f (t :: R) hw.tail (by omega) (by simp)
      refine Runs.postfix_base (T := (argToks ((x :: y :: ys).map (Expr.toks 0))).length + 2)
        (u := .tuple p (x :: y :: ys)) (pl := false)
        (Runs.mono (Runs.primary_tuple (xs := x :: y :: ys) hw.head (Or.inr hta)
          (Runs.idx (by omega) hargs)) ?_) ?_
      · rintro r ⟨h1, -, h3, h4⟩
        exact ⟨⟨hres r (h3 (by simp)), by omega⟩, h1⟩
      · intro n f' hn hf'; exact hk n f' hn (by omega)
  | case13 p xs _ =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Expr.printableAll_eq, List.all_eq_true] at hp
    have hT : (Expr.array p xs).toks 11 =
        .symbol "[" :: (argToks (xs.map (Expr.toks 0)) ++ [.symbol "]"]) := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk hIH
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
      ⟨hIH x (by have := argToks_mem hx; omega), hp x hx⟩
    have hs : ctx.input.semi.getD i false = false := by
      simpa using hw.semi [] _ (t :: R) (by simp) (SemiSeg.args xs)
    have hargs := Runs.args (Or.inr rfl) (allowEmpty := true) (top := false) hE
      (fun _ => rfl) ctx (i + 1) f (t :: R) hw.tail (by omega) (by simp)
    refine Runs.postfix_base (T := (argToks (xs.map (Expr.toks 0))).length + 2)
      (u := .array p xs) (pl := false)
      (Runs.mono (Runs.primary_array (xs := xs) hw.head hs (Runs.idx (by omega) hargs)) ?_) ?_
    · rintro r ⟨h1, h2, h4⟩
      exact ⟨⟨by simp [h2, Expr.erase], by omega⟩, h1⟩
    · intro n f' hn hf'; exact hk n f' hn (by omega)
  | case14 p b q k ihb =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true] at hp
    have hT : (Expr.select p b q k).toks 11 = b.toks 11 ++ [.symbol ".", .number k] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk hIH
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    refine ihb hp.1 (fun x hx => hIH x (by omega)) ctx i f (.symbol ".") _ hw (by decide)
      (fun q b m _ => by decide) (by omega) l Q ?_
    intro n f' hn hf'
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    refine Runs.suffixes_select hw.drop fun pos => ?_
    have hres : (Expr.select (tokenAt ctx.input i).pos n.expr pos k).erase =
        (Expr.select p b q k).erase := by
      simp [Expr.erase, hn.1]
    exact Runs.start (by omega) (hk _ f'' ⟨hres, by have := hn.2; simp only; omega⟩ (by omega))
  | case1 p v =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    have hT : (Expr.num p v).toks 11 = [.number v] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by simp at hf; omega⟩
    refine Runs.postfix_base (T := 1) (u := .num p v) (pl := false)
      (Runs.mono (Runs.primary_num hw.head) ?_) ?_
    · rintro r ⟨h1, h2, h3⟩; exact ⟨⟨by simp [h3, Expr.erase], by omega⟩, h1⟩
    · intro n f' hn hf'; exact hk n f' hn (by simp; omega)
  | case2 p v =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    have hT : (Expr.bool p v).toks 11 = [.keyword (boolean v)] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by simp at hf; omega⟩
    refine Runs.postfix_base (T := 1) (u := .bool p v) (pl := false)
      (Runs.mono (Runs.primary_bool hw.head) ?_) ?_
    · rintro r ⟨h1, h2, h3⟩; exact ⟨⟨by simp [h3, Expr.erase], by omega⟩, h1⟩
    · intro n f' hn hf'; exact hk n f' hn (by simp; omega)
  | case3 p v =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    have hT : (Expr.str p v).toks 11 = [.string v] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by simp at hf; omega⟩
    refine Runs.postfix_base (T := 1) (u := .str p v) (pl := false)
      (Runs.mono (Runs.primary_str hw.head) ?_) ?_
    · rintro r ⟨h1, h2, h3⟩; exact ⟨⟨by simp [h3, Expr.erase], by omega⟩, h1⟩
    · intro n f' hn hf'; exact hk n f' hn (by simp; omega)
  | case4 p v =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    have hT : (Expr.name p v).toks 11 = [.ident v] := by
      simp [Expr.toks, Expr.level, postfixLevel]
    rw [hT] at hw hf hk
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by simp at hf; omega⟩
    refine Runs.postfix_base (T := 1) (u := .name p v) (pl := true)
      (Runs.mono (Runs.primary_name hw.head (by rw [hw.tail.head]; exact ht)) ?_) ?_
    · rintro r ⟨h1, h2, h3⟩; exact ⟨⟨by simp [h3, Expr.erase], by omega⟩, h1⟩
    · intro n f' hn hf'; exact hk n f' hn (by simp; omega)
  | case5 p op a _ => exact Runs.postfix_paren _ (by simp [Expr.level, unaryLevel]) rfl
  | case6 p op l r _ _ =>
    exact Runs.postfix_paren _ (by simp [Expr.level]; have := BinOp.level_lt op; omega) rfl
  | case7 => exact Runs.postfix_paren _ (by simp [Expr.level]) rfl
  | case8 p g xs ihg _ =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true] at hp
    obtain ⟨hpg, hpxs⟩ := hp
    have hres : ∀ (n : Node) (ns : List Node) start, n.expr.erase = g.erase →
        ns.map (·.expr.erase) = xs.map Expr.erase →
        (Expr.call start n.expr (ns.map (·.expr))).erase = (Expr.call p g xs).erase := by
      intro n ns start h1 h2
      simp only [Expr.erase, h1, List.map_map, Function.comp_def]
      rw [← h2]
    by_cases hg : ∃ q b m, g = .field q b m
    · obtain ⟨q, b, m, rfl⟩ := hg
      rw [Expr.toks11_call_field] at hw hf hk hIH
      simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
      have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
        ⟨hIH x (by have := argToks_mem hx; omega), hpxs x hx⟩
      obtain ⟨f, rfl⟩ : ∃ g', f = g' + 2 := ⟨f - 2, by omega⟩
      refine Runs.postfix_base (T := ((Expr.field q b m).toks 0).length + 2) (pl := false)
        (Runs.idx (by omega) (Runs.primary_paren (hIH _ (by omega)) hpg ctx i f _ hw
          (by omega))) ?_
      intro n f' hn hf'
      subst hf'
      have hw2 := hw.tail.drop.tail
      refine Runs.start (by omega) (Runs.suffixes_call hE hw2 (by omega) ?_)
      intro ns hns hh
      refine Runs.start (by omega) (hk _ f ⟨hres n ns _ hn.1 hns, ?_⟩ (by omega))
      refine Nat.le_trans (height_le (B := (Expr.toks 0 (Expr.field q b m)).length +
        (argToks (List.map (Expr.toks 0) xs)).length + 3) ?_) (by omega)
      intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨m', hm', rfl⟩
      · have := hn.2; omega
      · have := hh m' hm'; omega
    · have hg' : ∀ q b m, g ≠ .field q b m := fun q b m h => hg ⟨q, b, m, h⟩
      rw [Expr.toks11_call p g xs hg'] at hw hf hk hIH
      simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
      have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
        ⟨hIH x (by have := argToks_mem hx; omega), hpxs x hx⟩
      refine ihg hpg (fun x hx => hIH x (by omega)) ctx i f (.symbol "(") _ hw (by decide)
        (fun q b m h => absurd h (hg' q b m)) (by omega) l Q ?_
      intro n f' hn hf'
      obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
      refine Runs.suffixes_call hE hw.drop (by omega) ?_
      intro ns hns hh
      refine Runs.start (by omega) (hk _ f'' ⟨hres n ns _ hn.1 hns, ?_⟩ (by omega))
      refine Nat.le_trans (height_le (B := (Expr.toks 11 g).length +
        (argToks (List.map (Expr.toks 0) xs)).length + 1) ?_) (by omega)
      intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨m', hm', rfl⟩
      · have := hn.2; omega
      · have := hh m' hm'; omega
  | case9 p b xs ihb _ =>
    intro hp hIH ctx i f t R hw ht _ hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true, Expr.printableAll_eq, List.all_eq_true,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨⟨hpb, hne⟩, hpxs⟩ := hp
    rw [Expr.toks11_index] at hw hf hk hIH
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    have hE : ∀ x ∈ xs, EGoal x ∧ x.printable = true := fun x hx =>
      ⟨hIH x (by have := argToks_mem hx; omega), hpxs x hx⟩
    refine ihb hpb (fun x hx => hIH x (by omega)) ctx i f (.symbol "[") _ hw (by decide)
      (fun q b m _ => by decide) (by omega) l Q ?_
    intro n f' hn hf'
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    refine Runs.suffixes_index hE hne hw.drop (by omega) ?_
    intro ns hns hh
    have hres : (Expr.index (tokenAt ctx.input i).pos n.expr (ns.map (·.expr))).erase =
        (Expr.index p b xs).erase := by
      simp only [Expr.erase, hn.1, List.map_map, Function.comp_def]
      rw [← hns]
    refine Runs.start (by omega) (hk _ f'' ⟨hres, ?_⟩ (by omega))
    refine Nat.le_trans (height_le (B := (Expr.toks 11 b).length +
      (argToks (List.map (Expr.toks 0) xs)).length + 1) ?_) (by omega)
    intro x hx
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨m', hm', rfl⟩
    · have := hn.2; omega
    · have := hh m' hm'; omega
  | case10 p b m ihb =>
    intro hp hIH ctx i f t R hw ht hfield hf l Q hk
    unfold SufK at hk
    simp only [Expr.printable, Bool.and_eq_true] at hp
    rw [Expr.toks11_field] at hw hf hk hIH
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hk hIH
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    refine ihb hp.1 (fun x hx => hIH x (by omega)) ctx i f (.symbol ".") _ hw (by decide)
      (fun q b m _ => by decide) (by omega) l Q ?_
    intro n f' hn hf'
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    refine Runs.suffixes_field hw.drop (hfield p b m rfl) fun pos => ?_
    have hres : (Expr.field (tokenAt ctx.input i).pos n.expr ⟨pos, m.name⟩).erase =
        (Expr.field p b m).erase := by
      simp [Expr.erase, hn.1, Ident.erase]
    exact Runs.start (by omega) (hk _ f'' ⟨hres, by have := hn.2; simp only; omega⟩ (by omega))


theorem Expr.toks11_length (u : Expr) : 1 ≤ (u.toks 11).length := by
  obtain ⟨k, hk, -⟩ := Expr.toks_head11 u
  obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk
  simp [hks]

/-! A postfix form, then a kind that starts no suffix. -/
theorem Runs.postfix_end (u : Expr) (hp : u.printable = true)
    (hIH : ∀ x, (x.toks 0).length < (u.toks 11).length → EGoal x) (ctx : Ctx) (i f : Nat)
    (t : Kind) (R : List Kind) (hw : Win ctx.input i (u.toks 11 ++ t :: R))
    (ht : suffixStart t = false) (ht2 : t ≠ .symbol "::") (hf : 4 * (u.toks 11).length ≤ f + 2) :
    Runs (postfixExpr f) ctx i (i + (u.toks 11).length)
      (fun r => Res u (u.toks 11).length r.1 ∧ r.2 = u.place) := by
  have h1 := Expr.toks11_length u
  refine Runs.postfix u hp hIH ctx i f t R hw ht2 (fun _ _ _ _ h => ?_) hf _ _ ?_
  · subst h; simp [suffixStart] at ht
  · intro n f' hn hf'
    obtain ⟨f'', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    have hw2 := hw.drop
    exact Runs.mono (Runs.suffixes_stop (by rw [hw2.head]; exact ht)) fun r hr => by
      subst hr; exact ⟨hn, rfl⟩

/-! ## Prefix operators -/

/-! The prefix operators `ops`, in reverse order, around `u`. -/
def wrap (ops : List (Pos × UnOp)) (u : Expr) : Expr := ops.foldl (fun a x => .unary x.1 x.2 a) u

theorem wrap_erase (ops : List (Pos × UnOp)) :
    ∀ (n : Node) (u : Expr), n.expr.erase = u.erase →
      (ops.foldl (fun (a : Node) (x : Pos × UnOp) => match x with
        | (p, op) => (⟨.unary p op a.expr, a.height + 1⟩ : Node)) n).expr.erase =
        (wrap ops u).erase ∧
      (ops.foldl (fun (a : Node) (x : Pos × UnOp) => match x with
        | (p, op) => (⟨.unary p op a.expr, a.height + 1⟩ : Node)) n).height =
        n.height + ops.length := by
  induction ops with
  | nil => intro n u h; exact ⟨h, by simp⟩
  | cons x ops ih =>
    intro n u h
    obtain ⟨p, op⟩ := x
    have := ih ⟨.unary p op n.expr, n.height + 1⟩ (.unary p op u) (by simp [Expr.erase, h])
    simp only [List.foldl_cons, wrap] at this ⊢
    exact ⟨this.1, by rw [this.2]; simp; omega⟩

theorem wrap_congr (ops : List (Pos × UnOp)) :
    ∀ (x y : Expr), x.erase = y.erase → (wrap ops x).erase = (wrap ops y).erase := by
  induction ops with
  | nil => intro x y h; exact h
  | cons o ops ih =>
    intro x y h
    exact ih _ _ (by simp [Expr.erase, h])

/-! The precondition of `Runs.unary` on `u`. -/
def UGoal (u : Expr) : Prop :=
  ∀ cu, cu ≤ 10 → (u.level < cu ∨ 10 ≤ u.level) → u.printable = true →
    (∀ x, (x.toks 0).length < (u.toks cu).length → EGoal x) →
    ∀ (ctx : Ctx) (i f : Nat) (t : Kind) (R : List Kind) (ops : List (Pos × UnOp)),
    Win ctx.input i (u.toks cu ++ t :: R) → suffixStart t = false → t ≠ .symbol "::" →
    4 * (u.toks cu).length ≤ f + 1 →
    Runs (unary f ops) ctx i (i + (u.toks cu).length)
      (fun n => n.expr.erase = (wrap ops u).erase ∧ n.height ≤ (u.toks cu).length + ops.length)

theorem Runs.unary_post (u : Expr) (hl : u.level ≠ 10) : UGoal u := by
  intro cu hcu hseed hp hIH ctx i f t R ops hw ht ht2 hf
  have h11 : u.toks cu = u.toks 11 := by
    rw [Expr.toks_paren, Expr.toks_paren (ctx := 11)]
    by_cases h : u.level < cu
    · simp [h, (by omega : u.level < 11)]
    · have : ¬ u.level < 11 := by omega
      simp [h, this]
  rw [h11] at hw hf hIH ⊢
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := Expr.toks11_length u; omega⟩
  obtain ⟨k, hk, hpk⟩ := Expr.toks_head11 u
  obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk
  have hk0 : (tokenAt ctx.input i).kind = k := by
    have := hw; rw [hks] at this; exact this.head
  rw [Parse.unary]
  refine Runs.peek_bind ?_
  simp only [unOp_pstart (hk0 ▸ hpk), isKw_pstart (hk0 ▸ hpk), Bool.false_eq_true, ite_false]
  refine Runs.bind (Runs.postfix_end u hp hIH ctx i f t R hw ht ht2 (by omega)) ?_
  rintro ⟨n, pl⟩ ⟨hn, _⟩
  simp only at hn
  refine Runs.pure ?_
  have := wrap_erase ops n u hn.1
  exact ⟨this.1, by rw [this.2]; have := hn.2; omega⟩

theorem Runs.unary (u : Expr) : UGoal u := by
  induction u using Expr.ind with
  | case5 p op a iha =>
    intro cu hcu hseed hp hIH ctx i f t R ops hw ht ht2 hf
    have hT : (Expr.unary p op a).toks cu = .symbol op.text :: a.toks 10 := by
      rw [Expr.toks_paren, ite_eq_right (by simp [Expr.level, unaryLevel]; omega)]
      simp [Expr.toks, unaryLevel]
    rw [hT] at hw hf hIH ⊢
    simp only [List.length_cons] at hf hIH ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.unary]
    refine Runs.peek_bind ?_
    simp only [unOp_text hw.head]
    refine Runs.bump_bind ?_
    simp only [Expr.printable] at hp
    refine Runs.mono (Runs.idx (by omega) (iha 10 (Nat.le_refl _) (by omega) hp
      (fun x hx => hIH x (by omega)) ctx (i + 1) f t R _ hw.tail ht ht2 (by omega))) ?_
    intro n hn
    refine ⟨?_, by simp only [List.length_cons] at hn; omega⟩
    rw [hn.1]
    exact wrap_congr ops _ _ (by simp [Expr.erase])
  | case6 p op => exact Runs.unary_post _ (by simp [Expr.level]; have := BinOp.level_lt op; omega)
  | _ => exact Runs.unary_post _ (by simp [Expr.level, postfixLevel])


/-! ## Infix operators -/

/-! The context of the left operand of `op`. -/
def lhsLevel (op : BinOp) : Nat := if op.associative then op.level else op.level + 1

/-! An infix operator with its position and its right operand. -/
abbrev Pair := Pos × BinOp × Expr

/-! The left-nested binary nodes of `u` and the pairs `ps`. -/
def bfold (u : Expr) (ps : List Pair) : Expr := ps.foldl (fun a q => .binary q.1 q.2.1 a q.2.2) u

def pairToks (ps : List Pair) : List Kind :=
  ps.flatMap fun q => .symbol q.2.1.text :: q.2.2.toks (q.2.1.level + 1)

/-!
The left spine of `e` in the context `c`: the operand that the prefix parser reads, its context,
and the infix operators that follow it.
-/
def spine : Expr → Nat → Expr × Nat × List Pair
  | .binary p op l r, c =>
    if c ≤ op.level then
      let s := spine l (lhsLevel op)
      (s.1, s.2.1, s.2.2 ++ [(p, op, r)])
    else (.binary p op l r, c, [])
  | e, c => (e, c, [])

/-! Each pair binds at least as tight as each pair after it. -/
def Desc (ps : List Pair) : Prop := ps.Pairwise fun a b => lhsLevel b.2.1 ≤ a.2.1.level

theorem lhsLevel_ge (op : BinOp) : op.level ≤ lhsLevel op := by
  unfold lhsLevel; split <;> omega

theorem lhsLevel_le (op : BinOp) : lhsLevel op ≤ 10 := by
  have := BinOp.level_lt op; unfold lhsLevel; split <;> omega

theorem spine_spec (e : Expr) : ∀ c, 1 ≤ c → c ≤ 10 →
    bfold (spine e c).1 (spine e c).2.2 = e ∧
    e.toks c = (spine e c).1.toks (spine e c).2.1 ++ pairToks (spine e c).2.2 ∧
    (∀ q ∈ (spine e c).2.2, c ≤ q.2.1.level) ∧ Desc (spine e c).2.2 ∧
    ((spine e c).1.level < (spine e c).2.1 ∨ 10 ≤ (spine e c).1.level) ∧
    (spine e c).2.1 ≤ 10 ∧
    (e.printable = true → (spine e c).1.printable = true ∧
      ∀ q ∈ (spine e c).2.2, q.2.2.printable = true) := by
  induction e using Expr.ind with
  | case6 p op l r ihl _ =>
    intro c hc1 hc
    by_cases hle : c ≤ op.level
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ihl (lhsLevel op)
        (by have := BinOp.level_pos op; have := lhsLevel_ge op; omega) (lhsLevel_le op)
      simp only [spine, hle, ite_true]
      refine ⟨?_, ?_, ?_, ?_, h5, h6, ?_⟩
      · simp [bfold, List.foldl_append] at h1 ⊢; rw [h1]
      · rw [Expr.toks_paren, ite_eq_right (by simp [Expr.level]; omega)]
        simp only [Expr.toks, Nat.not_lt_zero, ite_false]
        rw [show (if op.associative = true then op.level else op.level + 1) = lhsLevel op
          from rfl, h2]
        simp [pairToks, List.flatMap_append]
      · intro q hq
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · have := h3 q hq; have := lhsLevel_ge op; omega
        · exact hle
      · unfold Desc
        rw [List.pairwise_append]
        refine ⟨h4, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact h3 a ha
      · intro hp
        simp only [Expr.printable, Bool.and_eq_true] at hp
        obtain ⟨hu, hq⟩ := h7 hp.1
        refine ⟨hu, fun q hq' => ?_⟩
        simp only [List.mem_append, List.mem_singleton] at hq'
        rcases hq' with hq' | rfl
        · exact hq q hq'
        · exact hp.2
    · simp only [spine, hle, ite_false]
      refine ⟨rfl, by simp [pairToks], by simp, List.Pairwise.nil,
        Or.inl (by simp [Expr.level]; omega), hc, fun hp => ⟨hp, by simp⟩⟩
  | case7 =>
    intro c hc1 hc
    refine ⟨rfl, by simp [pairToks, spine], by simp [spine], List.Pairwise.nil,
      Or.inl (by simp [spine, Expr.level]; omega), hc,
      fun hp => ⟨hp, by simp [spine]⟩⟩
  | _ =>
    intro c hc1 hc
    refine ⟨rfl, by simp [pairToks, spine], by simp [spine], List.Pairwise.nil,
      Or.inr (by simp [spine, Expr.level, unaryLevel, postfixLevel]), hc,
      fun hp => ⟨hp, by simp [spine]⟩⟩


/-! `operand` reads the kinds of `e` in the context `c` back to `e`. -/
def OGoal (e : Expr) (c : Nat) : Prop :=
  e.printable = true → ∀ ctx i t R f, Win ctx.input i (e.toks c ++ t :: R) → After c t →
    4 * (e.toks c).length ≤ f →
    Runs (operand f c) ctx i (i + (e.toks c).length) (Res e (e.toks c).length)

theorem pairToks_cons (q : Pair) (ps : List Pair) :
    pairToks (q :: ps) = .symbol q.2.1.text :: (q.2.2.toks (q.2.1.level + 1) ++ pairToks ps) := by
  simp [pairToks]

/-! The kind after the pairs `ps`: the next operator or `t`. -/
theorem pairToks_next (k : Nat) (ps : List Pair) (t : Kind) (R : List Kind)
    (hl : ∀ q ∈ ps, q.2.1.level < k) (ht : After k t) :
    ∃ t' R', pairToks ps ++ t :: R = t' :: R' ∧ After k t' := by
  cases ps with
  | nil => exact ⟨t, R, rfl, ht⟩
  | cons q ps =>
    refine ⟨_, _, by rw [pairToks_cons]; rfl, After.op (hl q (by simp))⟩

theorem Runs.infixOps (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 9) (ps : List Pair)
    (hl : ∀ q ∈ ps, q.2.1.level = k) (h6 : k = 6 → ps.length ≤ 1)
    (hO : ∀ q ∈ ps, OGoal q.2.2 (k + 1) ∧ q.2.2.printable = true) :
    ∀ (x : Node) (x0 : Expr) (ctx : Ctx) (i f : Nat) (start : Pos) (t : Kind) (R : List Kind),
    x.expr.erase = x0.erase → Win ctx.input i (pairToks ps ++ t :: R) → After k t →
    4 * (pairToks ps).length + 1 ≤ f →
    Runs (Parse.infixOps f k start x) ctx i (i + (pairToks ps).length)
      (fun n => n.expr.erase = (bfold x0 ps).erase ∧
        n.height ≤ x.height + (pairToks ps).length) := by
  induction ps with
  | nil =>
    intro x x0 ctx i f start t R hx hw ht hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.infixOps]
    refine Runs.peek_bind ?_
    rw [opAt_none (by rw [hw.head]; exact ht)]
    exact Runs.pure ⟨hx, by simp [pairToks]⟩
  | cons q ps ih =>
    intro x x0 ctx i f start t R hx hw ht hf
    obtain ⟨p, op, r⟩ := q
    have hop : op.level = k := hl (p, op, r) (by simp)
    obtain ⟨hOr, hpr⟩ := hO (p, op, r) (by simp)
    simp only at hOr hpr
    specialize ih (fun q hq => hl q (by simp [hq]))
      (fun h => by have := h6 h; simp only [List.length_cons] at this; omega)
      (fun q hq => hO q (by simp [hq]))
    subst hop
    rw [pairToks_cons] at hw hf ⊢
    simp only [List.length_cons, List.length_append] at hf ⊢
    simp only [List.cons_append, List.append_assoc] at hw
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.infixOps]
    refine Runs.peek_bind ?_
    rw [opAt_text hw.head]
    simp only
    refine Runs.bump_bind ?_
    obtain ⟨t', R', hR, ht'⟩ := pairToks_next (op.level + 1) ps t R
      (fun q hq => by have := hl q (by simp [hq]); omega) (ht.mono (by omega))
    have hw1 := hw.tail
    rw [hR] at hw1
    refine Runs.bind (hOr hpr ctx (i + 1) t' R' f hw1 ht' (by omega)) fun rhs hrhs => ?_
    have hres : (Expr.binary start op x.expr rhs.expr).erase = (Expr.binary p op x0 r).erase := by
      simp [Expr.erase, hx, hrhs.1]
    have hh : height [x.height, rhs.height] ≤ x.height + (r.toks (op.level + 1)).length + 1 := by
      have := hrhs.2
      refine Nat.le_trans (height_le (B := x.height + (r.toks (op.level + 1)).length) ?_) (by omega)
      intro y hy; simp at hy; omega
    by_cases ha : op.associative = true
    · simp only [ha, ite_true]
      have hw2 := (hR ▸ hw1).drop
      refine Runs.idx (by omega) (Runs.mono (ih _ (.binary p op x0 r) ctx _ f start t R hres hw2 ht
        (by omega)) ?_)
      intro n hn
      refine ⟨by simpa [bfold] using hn.1, ?_⟩
      have := hn.2; simp only at this
      omega
    · simp only [ha, Bool.false_eq_true, ite_false]
      have hk6 : op.level = 6 := by
        simp [BinOp.associative] at ha; exact ha
      have hps : ps = [] := by
        have := h6 hk6; simp only [List.length_cons] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hps
      simp only [pairToks, List.flatMap_nil, List.nil_append] at hR hw1 ⊢
      obtain ⟨rfl, rfl⟩ := List.cons.inj hR
      refine Runs.peek_bind ?_
      have hw2 := hw1.drop
      rw [opAt_none (by rw [hw2.head]; exact ht)]
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      refine Runs.idx (by simp; omega) (Runs.pure ⟨by simpa [bfold] using hres, ?_⟩)
      simp only [List.length_nil]; omega


/-! The levels from `j - 1` down to `c`, the order of `climb`. -/
def levels (j c : Nat) : List Nat := (List.range (j - c)).map (fun x => j - 1 - x)

theorem levels_succ (j c : Nat) (h : c ≤ j) : levels (j + 1) c = j :: levels j c := by
  unfold levels
  rw [show j + 1 - c = (j - c) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_sub_cancel, Nat.sub_zero, List.cons.injEq,
    true_and]
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx
  simp only [Function.comp_apply]
  omega

theorem climb_eq (f c : Nat) (start : Pos) (x : Node) :
    climb (f + 1) c start x = (levels 10 c).foldlM (fun e k => Parse.infixOps f k start e) x := by
  rw [Parse.climb]; rfl

theorem split_level (j : Nat) : ∀ ps : List Pair, (∀ q ∈ ps, q.2.1.level ≤ j) → Desc ps →
    ∃ ps1 ps2, ps = ps1 ++ ps2 ∧ (∀ q ∈ ps1, q.2.1.level = j) ∧ (∀ q ∈ ps2, q.2.1.level < j) := by
  intro ps
  induction ps with
  | nil => intro _ _; exact ⟨[], [], rfl, by simp, by simp⟩
  | cons q ps ih =>
    intro hl hd
    unfold Desc at hd
    rw [List.pairwise_cons] at hd
    by_cases hq : q.2.1.level = j
    · obtain ⟨ps1, ps2, rfl, h1, h2⟩ := ih (fun b hb => hl b (by simp [hb])) hd.2
      refine ⟨q :: ps1, ps2, rfl, ?_, h2⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hq
      · exact h1 b hb
    · have hq' : q.2.1.level < j := by have := hl q (by simp); omega
      refine ⟨[], q :: ps, rfl, by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hq'
      · have := hd.1 b hb; have := lhsLevel_ge b.2.1; omega

theorem Runs.levels (c : Nat) (hc : 1 ≤ c) (j : Nat) (hcj : c ≤ j) (hj : j ≤ 10) :
    ∀ (ps : List Pair) (x : Node) (x0 : Expr) (ctx : Ctx) (i f : Nat) (start : Pos) (t : Kind)
    (R : List Kind),
    (∀ q ∈ ps, c ≤ q.2.1.level ∧ q.2.1.level < j) → Desc ps →
    (∀ q ∈ ps, OGoal q.2.2 (q.2.1.level + 1) ∧ q.2.2.printable = true) →
    x.expr.erase = x0.erase → Win ctx.input i (pairToks ps ++ t :: R) → After c t →
    4 * (pairToks ps).length + 1 ≤ f →
    Runs ((levels j c).foldlM (fun e k => Parse.infixOps f k start e) x) ctx i
      (i + (pairToks ps).length)
      (fun n => n.expr.erase = (bfold x0 ps).erase ∧
        n.height ≤ x.height + (pairToks ps).length) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = c + d := ⟨j - c, by omega⟩
  clear hcj
  induction d with
  | zero =>
    intro ps x x0 ctx i f start t R hl _ _ hx _ _ _
    have : ps = [] := by
      cases ps with
      | nil => rfl
      | cons q _ => have := hl q (by simp); omega
    subst this
    simp only [ParsePrint.levels, Nat.add_zero, Nat.sub_self, List.range_zero, List.map_nil,
      List.foldlM_nil]
    exact Runs.pure ⟨hx, by simp [pairToks]⟩
  | succ d ih =>
    intro ps x x0 ctx i f start t R hl hd hO hx hw ht hf
    specialize ih (by omega)
    have hcj : c ≤ c + d := by omega
    generalize hj' : c + d = j at ih hcj
    rw [show c + (d + 1) = j + 1 by omega] at hl ⊢
    rw [levels_succ j c hcj, List.foldlM_cons]
    obtain ⟨ps1, ps2, rfl, h1, h2⟩ :=
      split_level j ps (fun q hq => by have := hl q hq; omega) hd
    unfold Desc at hd
    rw [List.pairwise_append] at hd
    have hp2 : pairToks (ps1 ++ ps2) = pairToks ps1 ++ pairToks ps2 := by
      simp [pairToks, List.flatMap_append]
    rw [hp2] at hw hf ⊢
    rw [List.append_assoc] at hw
    simp only [List.length_append] at hf ⊢
    obtain ⟨t', R', hR, ht'⟩ := pairToks_next j ps2 t R h2 (ht.mono (by omega))
    have hw1 := hw
    rw [hR] at hw1
    have h6 : j = 6 → ps1.length ≤ 1 := by
      intro h6
      match ps1, hd.1, h1 with
      | [], _, _ => simp
      | [_], _, _ => simp
      | a :: b :: _, hd1, h1' =>
        rw [List.pairwise_cons] at hd1
        have hab := hd1.1 b (by simp)
        have ha := h1' a (by simp)
        have hb := h1' b (by simp)
        have : b.2.1.associative = false := by
          simp [BinOp.associative, hb, h6]
        have : lhsLevel b.2.1 = j + 1 := by simp [lhsLevel, this, hb]
        omega
    refine Runs.bind (Runs.infixOps j (by omega) (by omega) ps1 h1 h6
      (fun q hq => by have := hO q (by simp [hq]); rw [h1 q hq] at this; exact this)
      x x0 ctx i f start t' R' hx hw1 ht' (by omega)) fun y hy => ?_
    refine Runs.idx (by omega) (Runs.mono (ih ps2 y (bfold x0 ps1) ctx _ f start t R
      (fun q hq => ⟨(hl q (by simp [hq])).1, h2 q hq⟩) hd.2.1
      (fun q hq => hO q (by simp [hq])) hy.1 hw.drop ht (by omega)) ?_)
    intro n hn
    refine ⟨by simpa [bfold, List.foldl_append] using hn.1, by have := hy.2; omega⟩


theorem pairToks_mem {ps : List Pair} {q : Pair} (hq : q ∈ ps) :
    (q.2.2.toks (q.2.1.level + 1)).length + 1 ≤ (pairToks ps).length := by
  induction ps with
  | nil => cases hq
  | cons a ps ih =>
    rw [pairToks_cons]
    simp only [List.mem_cons] at hq
    simp only [List.length_cons, List.length_append]
    rcases hq with rfl | hq
    · omega
    · have := ih hq; omega

/-! ## Expressions -/

theorem Runs.operand (e : Expr) (c : Nat) (hc1 : 1 ≤ c) (hc : c ≤ 10)
    (hIH : ∀ x, (x.toks 0).length < (e.toks c).length → EGoal x)
    (hO : ∀ x c', 1 ≤ c' → c' ≤ 10 → (x.toks c').length < (e.toks c).length → OGoal x c') :
    OGoal e c := by
  intro hp ctx i t R f hw ht hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := spine_spec e c hc1 hc
  generalize spine e c = s at h1 h2 h3 h4 h5 h6 h7
  obtain ⟨u, cu, ps⟩ := s
  simp only at h1 h2 h3 h4 h5 h6 h7
  obtain ⟨hpu, hpq⟩ := h7 hp
  subst h1
  rw [h2] at hw hf hIH hO ⊢
  simp only [List.length_append] at hf hIH hO ⊢
  rw [List.append_assoc] at hw
  obtain ⟨k, hk, -⟩ := Expr.toks_head u cu
  have hTu : 1 ≤ (u.toks cu).length := by
    obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk; simp [hks]
  obtain ⟨t', R', hR, ht'⟩ := pairToks_next 10 ps t R (fun q _ => BinOp.level_lt _)
    (ht.mono hc)
  have hw1 := hw
  rw [hR] at hw1
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.operand]
  refine Runs.peek_bind ?_
  refine Runs.bind (Runs.unary u cu h6 h5 hpu (fun x hx => hIH x (by omega)) ctx i f t' R' []
    hw1 ht'.1 ht'.2.1 (by omega)) fun n hn => ?_
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [climb_eq]
  have hO' : ∀ q ∈ ps, OGoal q.2.2 (q.2.1.level + 1) ∧ q.2.2.printable = true := by
    intro q hq
    refine ⟨hO _ _ (by omega) (by have := BinOp.level_lt q.2.1; omega) ?_, hpq q hq⟩
    have := pairToks_mem hq; omega
  refine Runs.idx (by omega) (Runs.mono (Runs.levels c hc1 10 hc (Nat.le_refl _) ps n u ctx _ f
    _ t R (fun q hq => ⟨h3 q hq, BinOp.level_lt _⟩) h4 hO' (by simpa [wrap] using hn.1) hw.drop
    ht (by omega)) ?_)
  intro m hm
  refine ⟨hm.1, ?_⟩
  have := hn.2; have := hm.2; simp only [List.length_nil] at *; omega

theorem Expr.head_post_ne_if (e : Expr) (hl : e.level = 11) (c : Nat) :
    (e.toks c).head? ≠ some (.keyword "if") := by
  obtain ⟨k, hk, hpk⟩ := Expr.toks_head11 e
  rw [Expr.toks_paren] at hk ⊢
  split
  · simp
  · simp only [hl, Nat.lt_irrefl, ite_false] at hk
    rw [hk]
    intro he
    simp only [Option.some.injEq] at he
    subst he
    rcases hpk with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h | h <;> simp at h

theorem Expr.toks_head_ne_if (e : Expr) : ∀ c, 1 ≤ c →
    (e.toks c).head? ≠ some (.keyword "if") := by
  induction e using Expr.ind with
  | case5 p op a _ =>
    intro c _; rw [Expr.toks_paren]; split
    · simp
    · simp [Expr.toks]
  | case6 p op l r ihl _ =>
    intro c hc; rw [Expr.toks_paren]; split
    · simp
    · have := ihl (lhsLevel op) (by have := BinOp.level_pos op; have := lhsLevel_ge op; omega)
      simp only [Expr.toks, Nat.not_lt_zero, ite_false]
      rw [show (if op.associative = true then op.level else op.level + 1) = lhsLevel op
        from rfl, List.head?_append]
      obtain ⟨k, hk, -⟩ := Expr.toks_head l (lhsLevel op)
      rw [hk] at this ⊢
      simpa using this
  | case7 =>
    intro c hc; rw [Expr.toks_paren, ite_eq_left (by simp [Expr.level]; omega)]; simp
  | _ => exact fun c _ => Expr.head_post_ne_if _ (by simp [Expr.level, postfixLevel]) c


theorem Expr.toks_one (e : Expr) (h : 1 ≤ e.level) : e.toks 1 = e.toks 0 := by
  rw [Expr.toks_paren, ite_eq_right (by omega)]

theorem Runs.expr (e : Expr) (hIH : ∀ x, (x.toks 0).length < (e.toks 0).length → EGoal x)
    (hO : 1 ≤ e.level → OGoal e 1) : EGoal e := by
  intro hp ctx i t R f hw ht hf
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Parse.expr]
  refine Runs.peek_bind ?_
  by_cases hc : ∃ p c y n, e = .cond p c y n
  · obtain ⟨p, c, y, n, rfl⟩ := hc
    simp only [Expr.printable, Bool.and_eq_true] at hp
    obtain ⟨⟨hpc, hpy⟩, hpn⟩ := hp
    have hT : (Expr.cond p c y n).toks 0 = .keyword "if" :: .symbol "(" :: (c.toks 0 ++
        .symbol ")" :: .symbol "{" :: (y.toks 0 ++ .symbol "}" :: .keyword "else" ::
        .symbol "{" :: (n.toks 0 ++ [.symbol "}"]))) := by
      simp [Expr.toks]
    rw [hT] at hw hf hIH ⊢
    simp only [List.length_cons, List.length_append, List.length_nil] at hf hIH ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hw
    simp only [isKw, hw.head, beq_self_eq_true, ite_true]
    have hEc := hIH c (by omega)
    have hEy := hIH y (by omega)
    have hEn := hIH n (by omega)
    have hcl : ∀ s : String, s = ")" ∨ s = "}" → After 0 (.symbol s) := by
      rintro s (rfl | rfl)
      · exact After.close (Or.inl rfl)
      · exact After.sym (fun op => by cases op <;> decide) (by decide)
    refine Runs.bump_bind (Runs.sym_bind hw.tail.head ?_)
    have w1 := hw.tail.tail
    refine Runs.bind (hEc hpc ctx _ _ _ f w1 (hcl _ (Or.inl rfl)) (by omega)) fun nc hnc => ?_
    have w2 := w1.drop
    refine Runs.sym_bind w2.head (Runs.sym_bind w2.tail.head ?_)
    have w3 := w2.tail.tail
    refine Runs.bind (hEy hpy ctx _ _ _ f w3 (hcl _ (Or.inr rfl)) (by omega)) fun ny hny => ?_
    have w4 := w3.drop
    refine Runs.sym_bind w4.head (Runs.kw_bind w4.tail.head (Runs.sym_bind w4.tail.tail.head ?_))
    have w5 := w4.tail.tail.tail
    refine Runs.bind (hEn hpn ctx _ _ _ f w5 (hcl _ (Or.inr rfl)) (by omega)) fun nn hnn => ?_
    have w6 := w5.drop
    refine Runs.sym_bind w6.head (Runs.idx (by omega) (Runs.pure ⟨?_, ?_⟩))
    · simp [Expr.erase, hnc.1, hny.1, hnn.1]
    · have := hnc.2; have := hny.2; have := hnn.2
      refine Nat.le_trans (height_le (B := (c.toks 0).length + (y.toks 0).length +
        (n.toks 0).length) ?_) (by omega)
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega
  · have hl : 1 ≤ e.level := by
      cases e <;> simp_all [Expr.level, unaryLevel, postfixLevel, BinOp.level_pos]
    have h1 := Expr.toks_one e hl
    obtain ⟨k, hk, -⟩ := Expr.toks_head e 0
    obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk
    have hk0 : (tokenAt ctx.input i).kind = k := by
      have := hw; rw [hks] at this; exact this.head
    have hne : k ≠ .keyword "if" := by
      have := Expr.toks_head_ne_if e 1 (Nat.le_refl _)
      rw [h1, hks] at this; simpa using this
    simp only [isKw, hk0, beq_iff_eq, hne, ite_false]
    have := hO hl hp ctx i t R f (by rw [h1]; exact hw) (ht.mono (by omega)) (by rw [h1]; omega)
    rw [h1] at this
    exact this

/-! Each expression satisfies `EGoal` and `OGoal`, by induction on the number of its kinds. -/
theorem goals (n : Nat) :
    (∀ x, (x.toks 0).length < n → EGoal x) ∧
    (∀ x c, 1 ≤ c → c ≤ 10 → (x.toks c).length < n → OGoal x c) := by
  induction n with
  | zero =>
    exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    have hO : ∀ x c, 1 ≤ c → c ≤ 10 → (x.toks c).length ≤ n → OGoal x c := by
      intro x c hc1 hc hn
      exact Runs.operand x c hc1 hc (fun y hy => ih.1 y (by omega))
        (fun y c' h1 h2 hy => ih.2 y c' h1 h2 (by omega))
    refine ⟨fun x hx => ?_, fun x c hc1 hc hx => hO x c hc1 hc (by omega)⟩
    refine Runs.expr x (fun y hy => ih.1 y (by omega)) fun hl => hO x 1 (Nat.le_refl _)
      (by decide) ?_
    rw [Expr.toks_one x hl]; omega

/-!
The expression lemma: `expr` reads the kinds of a printable expression back to it, up to
positions. It reads exactly its kinds. Its height is at most the number of its kinds.
-/
theorem Runs.expr_print (e : Expr) : EGoal e := (goals _).1 e (Nat.lt_succ_self _)

theorem Runs.operand_print (e : Expr) (c : Nat) (hc1 : 1 ≤ c) (hc : c ≤ 10) : OGoal e c :=
  (goals _).2 e c hc1 hc (Nat.lt_succ_self _)


/-! ## Outermost expressions and types -/

/-! `value` reads an outermost expression. Its height is at most the syntax depth. -/
theorem Runs.value (e : Expr) (hp : e.printable = true) (ctx : Ctx) (i f : Nat) (t : Kind)
    (R : List Kind) (hw : Win ctx.input i (e.toks 0 ++ t :: R)) (ht : After 0 t)
    (hf : 4 * (e.toks 0).length + 1 ≤ f) (hd : (e.toks 0).length ≤ ctx.depth) :
    Runs (Parse.value f) ctx i (i + (e.toks 0).length) (fun v => v.erase = e.erase) := by
  unfold Parse.value
  refine Runs.peek_bind ?_
  refine Runs.bind (Runs.expr_print e hp ctx i t R f hw ht hf) fun n hn => ?_
  exact Runs.bind (Runs.checkHeight (Nat.le_trans hn.2 hd)) fun _ _ => Runs.pure hn.1

theorem Runs.type (ty : TypeExpr) : TGoal ty :=
  Runs.type_of _ (fun x _ => Runs.expr_print x) ty (Nat.le_refl _)

/-! A type, then a kind that is no `[`, no `(`, and no `::`. -/
theorem Runs.type_end (ty : TypeExpr) (hp : ty.printable = true) (ctx : Ctx) (i f : Nat)
    (u : Kind) (R : List Kind) (hw : Win ctx.input i (ty.toks ++ u :: R))
    (hu : u ≠ .symbol "[" ∧ u ≠ .symbol "(" ∧ u ≠ .symbol "::") (hf : 4 * ty.toks.length ≤ f) :
    Runs (typeExpr f) ctx i (i + ty.toks.length)
      (fun r => r.1.erase = ty.erase ∧ r.2 ≤ ty.toks.length) :=
  TGoal.type_end (Runs.type ty) hp ctx i f u R hw hu hf

/-! `typeTop` reads an outermost type. Its height is at most the syntax depth. -/
theorem Runs.typeTop (ty : TypeExpr) (hp : ty.printable = true) (ctx : Ctx) (i f : Nat)
    (u : Kind) (R : List Kind) (hw : Win ctx.input i (ty.toks ++ u :: R))
    (hu : u ≠ .symbol "[" ∧ u ≠ .symbol "(" ∧ u ≠ .symbol "::") (hf : 4 * ty.toks.length ≤ f)
    (hd : ty.toks.length ≤ ctx.depth) :
    Runs (Parse.typeTop f) ctx i (i + ty.toks.length) (fun r => r.erase = ty.erase) := by
  unfold Parse.typeTop
  refine Runs.peek_bind ?_
  refine Runs.bind (Runs.type_end ty hp ctx i f u R hw hu hf) ?_
  rintro ⟨ty', h⟩ ⟨hty, hh⟩
  exact Runs.bind (Runs.checkHeight (Nat.le_trans hh hd)) fun _ _ => Runs.pure hty


/-! ## Expression statements -/

theorem Expr.level_le (e : Expr) : e.level ≤ 11 := by
  cases e with
  | binary _ op => have := BinOp.level_lt op; simp [Expr.level]; omega
  | _ => simp [Expr.level, unaryLevel, postfixLevel]

/-!
An expression statement that starts with a name: the statement parser reads a postfix form,
then the infix operators with `climb`.
-/
theorem Runs.postfix_climb (e : Expr) (hp : e.printable = true)
    (hid : ∃ n, (e.toks 0).head? = some (.ident n)) (ctx : Ctx) (i f : Nat) (t : Kind)
    (R : List Kind) (hw : Win ctx.input i (e.toks 0 ++ t :: R)) (ht : After 1 t)
    (hf : 4 * (e.toks 0).length ≤ f) :
    ∃ T1, T1 ≤ (e.toks 0).length ∧
      ((tokenAt ctx.input (i + T1)).kind = t ∨
        ∃ op : BinOp, (tokenAt ctx.input (i + T1)).kind = .symbol op.text) ∧
      Runs (postfixExpr f) ctx i (i + T1) (fun r => r.1.height ≤ T1 ∧
        ∀ start, Runs (climb f 1 start r.1) ctx (i + T1) (i + (e.toks 0).length)
          (Res e (e.toks 0).length)) := by
  obtain ⟨nm, hnm⟩ := hid
  have hl : 1 ≤ e.level := by
    cases e with
    | cond => simp [Expr.toks] at hnm
    | binary _ op => exact BinOp.level_pos op
    | _ => simp [Expr.level, unaryLevel, postfixLevel]
  have h01 := Expr.toks_one e hl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := spine_spec e 1 (Nat.le_refl _) (by decide)
  rw [h01] at h2
  generalize spine e 1 = s at h1 h2 h3 h4 h5 h6 h7
  obtain ⟨u, cu, ps⟩ := s
  simp only at h1 h2 h3 h4 h5 h6 h7
  obtain ⟨hpu, hpq⟩ := h7 hp
  subst h1
  rw [h2] at hw hf hnm ⊢
  simp only [List.length_append] at hf ⊢
  rw [List.append_assoc] at hw
  obtain ⟨k, hk, -⟩ := Expr.toks_head u cu
  obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk
  rw [hks, List.cons_append, List.head?_cons] at hnm
  cases hnm
  have hu11 : u.toks cu = u.toks 11 := by
    have hlv := Expr.level_le u
    rw [Expr.toks_paren] at hks ⊢
    rw [Expr.toks_paren (ctx := 11)]
    by_cases hlt : u.level < cu
    · simp [hlt] at hks
    · have h10 : u.level ≠ 10 := by
        intro h10
        cases u with
        | unary => simp [hlt, Expr.toks] at hks
        | binary _ op => have := BinOp.level_lt op; simp [Expr.level] at h10; omega
        | _ => simp [Expr.level, postfixLevel] at h10
      rw [ite_eq_right hlt, ite_eq_right (by omega)]
  rw [hu11] at hw hf ⊢
  obtain ⟨t', R', hR, ht'⟩ := pairToks_next 10 ps t R (fun q _ => BinOp.level_lt _)
    (ht.mono (by decide))
  have hw1 := hw
  rw [hR] at hw1
  refine ⟨(u.toks 11).length, by omega, ?_, ?_⟩
  · have := hw1.drop.head
    cases ps with
    | nil => left; simp only [pairToks, List.flatMap_nil, List.nil_append] at hR
             obtain ⟨rfl, -⟩ := List.cons.inj hR; exact this
    | cons q ps => right; rw [pairToks_cons] at hR; obtain ⟨rfl, -⟩ := List.cons.inj hR
                   exact ⟨q.2.1, this⟩
  · refine Runs.mono (Runs.postfix_end u hpu (fun x _ => Runs.expr_print x) ctx i f t' R' hw1
      ht'.1 ht'.2.1 (by omega)) ?_
    rintro ⟨n, pl⟩ ⟨hn, -⟩
    refine ⟨hn.2, fun start => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by
      have := Expr.toks11_length u; omega⟩
    rw [climb_eq]
    have hO' : ∀ q ∈ ps, OGoal q.2.2 (q.2.1.level + 1) ∧ q.2.2.printable = true := fun q hq =>
      ⟨Runs.operand_print _ _ (by omega) (by have := BinOp.level_lt q.2.1; omega), hpq q hq⟩
    refine Runs.idx (by omega) (Runs.mono (Runs.levels 1 (Nat.le_refl _) 10 (by decide)
      (Nat.le_refl _) ps n u ctx _ f start t R (fun q hq => ⟨h3 q hq, BinOp.level_lt _⟩) h4 hO'
      hn.1 hw.drop ht (by have := Expr.toks11_length u; omega)) ?_)
    intro m hm
    refine ⟨hm.1, ?_⟩
    have := hn.2; have := hm.2; simp only at *; omega

end Silicon.Source.ParsePrint
