-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Parse.Stmt

/-!
The parser lemma of `parse_print` for items and files.

`Runs.items` reads the kinds `Print.toks items` of a printable file back to its items, up to
positions. It stops at `eof`. The fuel is four times the number of kinds, plus six. The
fuel of `parse` is 32 times the number of tokens, plus 32, so it is sufficient.
-/
namespace Silicon.Source.ParsePrint

open Lex Parse Print

/-! ## Monad steps -/

theorem Runs.seqRight {α β : Type} {a : P α} {b : P β} {ctx : Ctx} {i j l : Nat}
    {Q : α → Prop} {R : β → Prop} (ha : Runs a ctx i j Q) (hb : Runs b ctx j l R) :
    Runs (a *> b) ctx i l R := by
  rw [seqRight_eq_bind]
  exact Runs.bind ha fun _ _ => hb

theorem Runs.withReader {α : Type} {m : P α} {g : Ctx → Ctx} {ctx : Ctx} {i j : Nat}
    {Q : α → Prop} (h : Runs m (g ctx) i j Q) : Runs (withReader g m) ctx i j Q := fun s => h s

theorem Runs.kw {ctx : Ctx} {i : Nat} {s : String}
    (hs : (tokenAt ctx.input i).kind = .keyword s) : Runs (Parse.kw s) ctx i (i + 1)
      (fun _ => True) := by
  have := Runs.kw_bind (k := fun _ => (Pure.pure () : P Unit)) (R := fun _ => True) hs
    (Runs.pure trivial)
  simpa using this

theorem Runs.sym {ctx : Ctx} {i : Nat} {s : String}
    (hs : (tokenAt ctx.input i).kind = .symbol s) : Runs (Parse.sym s) ctx i (i + 1)
      (fun _ => True) := by
  unfold Parse.sym
  refine Runs.peek_bind ?_
  simp only [isSym, hs, beq_self_eq_true, ite_true]
  exact Runs.bump

theorem Runs.map {α β : Type} {m : P α} {g : α → β} {ctx : Ctx} {i j : Nat} {Q : α → Prop}
    (hm : Runs m ctx i j Q) : Runs (g <$> m) ctx i j (fun b => ∃ a, Q a ∧ b = g a) := by
  have := Runs.map_bind (k := fun b => (Pure.pure b : P β)) (g := g)
    (R := fun b => ∃ a, Q a ∧ b = g a) hm fun a ha => Runs.pure ⟨a, ha, rfl⟩
  simpa using this

/-! ## Parameters -/

theorem Runs.param (q : Param) (static : Bool) (hp : q.printable static = true) (ctx : Ctx)
    (i f : Nat) (u : Kind) (R : List Kind) (hw : Win ctx.input i (q.toks ++ u :: R))
    (hu : u ≠ .symbol "[" ∧ u ≠ .symbol "(" ∧ u ≠ .symbol "::") (hf : 4 * q.ty.toks.length ≤ f)
    (hd : q.ty.toks.length ≤ ctx.depth) :
    Runs (param f static) ctx i (i + q.toks.length) (fun r => r.erase = q.erase) := by
  obtain ⟨pos, c, n, ty⟩ := q
  simp only [Param.printable, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hc, hn⟩, hty⟩ := hp
  simp only at hf hd
  unfold Parse.param
  cases c with
  | true =>
    have e : (Param.toks ⟨pos, true, n, ty⟩) ++ u :: R =
        .keyword "comptime" :: .ident n.name :: .symbol ":" :: (ty.toks ++ u :: R) := by
      simp [Param.toks]
    have hT : (Param.toks ⟨pos, true, n, ty⟩).length = ty.toks.length + 3 := by
      simp [Param.toks]
    rw [e] at hw
    rw [hT]
    refine Runs.peek_bind ?_
    simp only [isKw_of hw.head]
    reduce_checks
    cases static with
    | true =>
      simp only [ite_true]
      refine Runs.bind (Runs.seqRight (Runs.kw hw.head) (Runs.pure (Q := (· = true)) rfl))
        fun b hb => ?_
      subst b
      refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
      refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ hw.tail.tail hu hf hd)
        fun ty' hty' => Runs.idx (by omega) (Runs.pure ?_)
      simp [Param.erase, Ident.erase_of_name (b := n) hid, hty']
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine Runs.bind (Runs.acceptKw_true hw.head) fun b hb => ?_
      subst b
      refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
      refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ hw.tail.tail hu hf hd)
        fun ty' hty' => Runs.idx (by omega) (Runs.pure ?_)
      simp [Param.erase, Ident.erase_of_name (b := n) hid, hty']
  | false =>
    have e : (Param.toks ⟨pos, false, n, ty⟩) ++ u :: R =
        .ident n.name :: .symbol ":" :: (ty.toks ++ u :: R) := by
      simp [Param.toks]
    have hT : (Param.toks ⟨pos, false, n, ty⟩).length = ty.toks.length + 2 := by
      simp [Param.toks]
    rw [e] at hw
    rw [hT]
    cases static with
    | true => simp at hc
    | false =>
      refine Runs.peek_bind ?_
      simp only [isKw_of hw.head]
      reduce_checks
      refine Runs.bind (Runs.acceptKw_false (by rw [hw.head]; simp)) fun b hb => ?_
      subst b
      refine Runs.bind (Runs.ident hw.head) fun id hid => ?_
      refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ hw.tail hu hf hd)
        fun ty' hty' => Runs.idx (by omega) (Runs.pure ?_)
      simp [Param.erase, Ident.erase_of_name (b := n) hid, hty']

theorem Param.headKind (q : Param) : ∃ k ks, q.toks = k :: ks ∧ k ≠ .symbol ")" ∧
    k ≠ .symbol "," := by
  obtain ⟨pos, c, n, ty⟩ := q
  cases c
  · exact ⟨.ident n.name, .symbol ":" :: ty.toks, by simp [Param.toks], by simp, by simp⟩
  · exact ⟨.keyword "comptime", .ident n.name :: .symbol ":" :: ty.toks, by simp [Param.toks],
      by decide, by decide⟩

theorem Runs.params (static : Bool) (ps : List Param) : ∀ (ctx : Ctx) (i f : Nat)
    (R : List Kind) (acc : List Param), ps.all (Param.printable static) = true →
    Win ctx.input i (argToks (ps.map Param.toks) ++ .symbol ")" :: R) →
    4 * (argToks (ps.map Param.toks)).length + 5 ≤ f →
    (argToks (ps.map Param.toks)).length ≤ ctx.depth →
    Runs (params f static acc) ctx i (i + (argToks (ps.map Param.toks)).length + 1)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧ ms.map Param.erase = ps.map Param.erase) := by
  induction ps with
  | nil =>
    intro ctx i f R acc _ hw hf _
    simp only [List.map_nil, Print.argToks, List.intercalate_nil, List.nil_append,
      List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.params]
    refine Runs.bind (Runs.acceptSym_true hw.head) fun b hb => ?_
    subst b
    exact Runs.pure ⟨[], by simp, rfl⟩
  | cons q qs ih =>
    intro ctx i f R acc hp hw hf hd
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨k, ks, hks, hk1, hk2⟩ := Param.headKind q
    have hty : q.ty.toks.length + 2 ≤ q.toks.length := by
      obtain ⟨pos, c, n, ty⟩ := q
      cases c <;> simp [Param.toks]
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.params]
    cases qs with
    | nil =>
      simp only [List.map_cons, List.map_nil, argToks_single] at hw hf hd ⊢
      refine Runs.bind (Runs.acceptSym_false (by rw [hw.head' (k := k) (by simp [hks])]; exact hk1))
        fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.bind (Runs.param q static hp.1 ctx i f _ R hw (by decide) (by omega)
        (by omega)) fun q' hq' => ?_
      refine Runs.bind (Runs.acceptSym_true hw.drop.head) fun b hb => ?_
      subst b
      reduce_checks
      exact Runs.pure ⟨[q'], by simp, by simp [hq']⟩
    | cons q2 qs2 =>
      simp only [List.map_cons, argToks_cons_cons, List.append_assoc, List.cons_append,
        List.length_append, List.length_cons] at hw hf hd ⊢
      have hw' : Win ctx.input i (q.toks ++ .symbol "," ::
          (argToks ((q2 :: qs2).map Param.toks) ++ .symbol ")" :: R)) := by
        simpa using hw
      refine Runs.bind (Runs.acceptSym_false (by
        rw [hw'.head' (k := k) (by simp [hks])]; exact hk1)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.bind (Runs.param q static hp.1 ctx i f _ _ hw' (by decide) (by omega)
        (by omega)) fun q' hq' => ?_
      have w := hw'.drop
      refine Runs.bind (Runs.acceptSym_false (by rw [w.head]; decide)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.sym_bind w.head ?_
      have := ih ctx _ f R (q' :: acc) hp.2 w.tail (by simp; omega) (by simp; omega)
      refine Runs.idx (by simp; omega) (Runs.mono this ?_)
      rintro r ⟨ms, rfl, hms⟩
      exact ⟨q' :: ms, by simp, by simp [hq', hms]⟩

/-! ## Items -/

theorem Runs.fnRest (p : Pos) (c : Bool) (n : Ident) (ps : List Param) (r : TypeExpr)
    (b : List Stmt) (hps : ps.all (Param.printable false) = true) (hr : r.printable = true)
    (hb : Stmt.printableAll (!c) b = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (start : Pos)
    (hw : Win ctx.input i (.keyword "fn" :: .ident n.name :: .symbol "(" ::
      (argToks (ps.map Param.toks) ++ .symbol ")" :: .symbol "->" ::
      (r.toks ++ (Stmt.bodyToks b ++ R)))))
    (hf : 4 * ((argToks (ps.map Param.toks)).length + r.toks.length +
      (Stmt.bodyToks b).length) + 5 ≤ f)
    (hd : (argToks (ps.map Param.toks)).length + r.toks.length + (Stmt.bodyToks b).length ≤
      ctx.depth) :
    Runs (fnRest f start c) ctx i (i + ((argToks (ps.map Param.toks)).length + r.toks.length +
      (Stmt.bodyToks b).length + 5)) (fun it => it.erase = (Item.fn p c n ps r b).erase) := by
  unfold Parse.fnRest
  refine Runs.kw_bind hw.head ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  refine Runs.sym_bind hw.tail.tail.head ?_
  have w := hw.tail.tail.tail
  refine Runs.bind (Runs.params false ps ctx _ f _ [] hps w (by omega) (by omega))
    fun ps' hps' => ?_
  obtain ⟨ms, rfl, hms⟩ := hps'
  have w2 := w.drop.tail
  refine Runs.sym_bind w2.head ?_
  have eb : Stmt.bodyToks b ++ R = .symbol "{" :: (Stmt.linesToks b ++ .symbol "}" :: R) := by
    simp [Stmt.bodyToks]
  have w3 := w2.tail
  rw [eb] at w3
  refine Runs.bind (Runs.typeTop r hr ctx _ f _ _ w3 (by decide) (by omega) (by omega))
    fun r' hr' => ?_
  have w4 := w3.drop
  rw [← eb] at w4
  refine Runs.bind (Runs.withReader (Runs.block_print b { ctx with plainFn := !c } _ f R hb w4
    (by omega) (by show (Stmt.bodyToks b).length ≤ ctx.depth; omega))) fun b' hb' => ?_
  refine Runs.idx (by omega) (Runs.pure ?_)
  simp [Item.erase, Ident.erase_of_name (b := n) hid, hms, hr', hb']

/-! The kinds of the `domains` clause of a module. -/
def domToks : Option (List Ident) → List Kind
  | none => []
  | some ds => [.keyword "domains", .symbol "("] ++ argToks (ds.map fun d => [.ident d.name]) ++
    [.symbol ")"]

theorem Item.toks_module (p : Pos) (n : Ident) (ps : List Param) (ds : Option (List Ident))
    (b : List Stmt) : (Item.module p n ps ds b).toks = .keyword "module" :: .ident n.name ::
      .symbol "(" :: (argToks (ps.map Param.toks) ++ .symbol ")" :: (domToks ds ++
      Stmt.bodyToks b)) := by
  cases ds <;> simp [Item.toks, domToks]

theorem Runs.moduleItem (p : Pos) (n : Ident) (ps : List Param) (ds : Option (List Ident))
    (b : List Stmt) (hp : (Item.module p n ps ds b).printable = true) (ctx : Ctx)
    (hpl : ctx.plainFn = false) (i f : Nat) (R : List Kind) (start : Pos)
    (hw : Win ctx.input i ((Item.module p n ps ds b).toks ++ R))
    (hf : 4 * (Item.module p n ps ds b).toks.length + 5 ≤ f)
    (hd : (Item.module p n ps ds b).toks.length ≤ ctx.depth) :
    Runs (moduleItem f start) ctx i (i + (Item.module p n ps ds b).toks.length)
      (fun it => it.erase = (Item.module p n ps ds b).erase) := by
  simp only [Item.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨hn, hps⟩, hds⟩, hb⟩ := hp
  rw [← hpl] at hb
  have eb : Stmt.bodyToks b ++ R = .symbol "{" :: (Stmt.linesToks b ++ .symbol "}" :: R) := by
    simp [Stmt.bodyToks]
  rw [Item.toks_module] at hw hf hd ⊢
  simp only [List.cons_append, List.append_assoc, List.length_cons, List.length_append]
    at hw hf hd ⊢
  unfold Parse.moduleItem
  refine Runs.kw_bind hw.head ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  refine Runs.sym_bind hw.tail.tail.head ?_
  have w := hw.tail.tail.tail
  refine Runs.bind (Runs.params true ps ctx _ f _ [] hps w (by omega) (by omega))
    fun ps' hps' => ?_
  obtain ⟨ms, rfl, hms⟩ := hps'
  have w2 := w.drop.tail
  cases ds with
  | none =>
    simp only [domToks, List.nil_append, List.length_nil] at w2 hf hd ⊢
    rw [eb] at w2
    refine Runs.bind (Runs.acceptKw_false (by rw [w2.head]; decide)) fun x hx => ?_
    subst x
    reduce_checks
    refine Runs.bind (Runs.pure (Q := (· = none)) rfl) fun o ho => ?_
    subst o
    refine Runs.peek_bind ?_
    simp only [isKw_of w2.head]
    reduce_checks
    rw [← eb] at w2
    refine Runs.bind (Runs.block_print b ctx _ f R hb w2 (by omega) (by omega)) fun b' hb' => ?_
    refine Runs.idx (by omega) (Runs.pure ?_)
    simp [Item.erase, Ident.erase_of_name (b := n) hid, hms, hb']
  | some ds =>
    simp only [Option.all, Bool.and_eq_true, decide_eq_true_eq] at hds
    obtain ⟨hlen, -⟩ := hds
    simp only [domToks, List.cons_append, List.append_assoc, List.nil_append, List.length_cons,
      List.length_append, List.length_nil] at w2 hf hd ⊢
    refine Runs.bind (Runs.acceptKw_true w2.head) fun x hx => ?_
    subst x
    reduce_checks
    have w3 := w2.tail
    have hdn : Runs domainNames ctx (i + 1 + 1 + 1 + (argToks (ps.map Param.toks)).length +
        1 + 1 + 1) (i + 1 + 1 + 1 + (argToks (ps.map Param.toks)).length + 1 + 1 + 1 +
        (argToks (ds.map fun d => [Kind.ident d.name])).length + 1)
        (fun r => r.map Ident.erase = ds.map Ident.erase) := by
      have w4 := w3.tail
      unfold Parse.domainNames
      match ds, hlen with
      | [], _ =>
        simp only [List.map_nil, Print.argToks, List.intercalate_nil, List.nil_append,
          List.length_nil] at w4 ⊢
        refine Runs.bind (Runs.acceptSym_true w4.head) fun x hx => ?_
        subst x
        exact Runs.idx (by omega) (Runs.pure rfl)
      | [d], _ =>
        simp only [List.map_cons, List.map_nil, argToks_single, List.length_singleton,
          List.cons_append, List.nil_append] at w4 ⊢
        refine Runs.bind (Runs.acceptSym_false (by rw [w4.head]; simp)) fun x hx => ?_
        subst x
        reduce_checks
        refine Runs.bind (Runs.ident w4.head) fun d' hd' => ?_
        refine Runs.bind (Runs.acceptSym_true w4.tail.head) fun x hx => ?_
        subst x
        reduce_checks
        exact Runs.idx (by omega) (Runs.pure (by simp [Ident.erase_of_name (b := d) hd']))
    have w5 := w3.tail.drop.tail
    refine Runs.bind (Runs.seqRight (Runs.sym w3.head) (Runs.map (g := some) hdn)) ?_
    rintro _ ⟨ds', hds', rfl⟩
    rw [eb] at w5
    refine Runs.peek_bind ?_
    simp only [isKw_of w5.head]
    reduce_checks
    rw [← eb] at w5
    refine Runs.bind (Runs.block_print b ctx _ f R hb w5 (by omega) (by omega)) fun b' hb' => ?_
    refine Runs.idx (by omega) (Runs.pure ?_)
    simp [Item.erase, Ident.erase_of_name (b := n) hid, hms, hb', hds']

/-! `item` reads the kinds of a printable item back to it, up to positions. -/
theorem Runs.item (it : Item) (hp : it.printable = true) (ctx : Ctx) (hpl : ctx.plainFn = false)
    (i f : Nat) (R : List Kind) (hw : Win ctx.input i (it.toks ++ R))
    (hf : 4 * it.toks.length + 5 ≤ f) (hd : it.toks.length ≤ ctx.depth) :
    Runs (item f) ctx i (i + it.toks.length) (fun r => r.erase = it.erase) := by
  unfold Parse.item
  cases it with
  | const p n ty v =>
    simp only [Item.printable, Bool.and_eq_true] at hp
    obtain ⟨⟨hn, hty⟩, hv⟩ := hp
    have e : (Item.const p n ty v).toks ++ R = .keyword "const" :: .ident n.name ::
        .symbol ":" :: (ty.toks ++ .symbol "=" :: (v.toks 0 ++ .symbol ";" :: R)) := by
      simp [Item.toks]
    have hT : (Item.const p n ty v).toks.length = ty.toks.length + (v.toks 0).length + 5 := by
      simp [Item.toks]; omega
    rw [e] at hw
    rw [hT] at hf hd ⊢
    refine Runs.peek_bind ?_
    simp only [hw.head]
    refine Runs.bump_bind ?_
    refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
    have w := hw.tail.tail
    refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ w (by decide) (by omega)
      (by omega)) fun ty' hty' => ?_
    have w2 := w.tail.drop
    refine Runs.sym_bind w2.head ?_
    refine Runs.bind (Runs.value v hv ctx _ f _ _ w2.tail After.semi (by omega) (by omega))
      fun v' hv' => ?_
    refine Runs.sym_bind w2.tail.drop.head (Runs.idx (by omega) (Runs.pure ?_))
    simp [Item.erase, Ident.erase_of_name (b := n) hid, hv', hty']
  | fn p c n ps r b =>
    simp only [Item.printable, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨hn, hps⟩, hr⟩, hb⟩ := hp
    have e : (Item.fn p c n ps r b).toks ++ R = (if c then [.keyword "comptime"] else []) ++
        .keyword "fn" :: .ident n.name :: .symbol "(" :: (argToks (ps.map Param.toks) ++
        .symbol ")" :: .symbol "->" :: (r.toks ++ (Stmt.bodyToks b ++ R))) := by
      simp [Item.toks]
    have hT : (Item.fn p c n ps r b).toks.length = (if c then 1 else 0) +
        ((argToks (ps.map Param.toks)).length + r.toks.length + (Stmt.bodyToks b).length + 5) := by
      cases c <;> simp [Item.toks] <;> omega
    rw [e] at hw
    rw [hT] at hf hd ⊢
    refine Runs.peek_bind ?_
    cases c with
    | true =>
      simp only [ite_true, List.cons_append, List.nil_append] at hw hf hd ⊢
      simp only [hw.head]
      refine Runs.bump_bind ?_
      exact Runs.idx (by omega) (Runs.fnRest p true n ps r b hps hr hb ctx _ f R _ hw.tail
        (by omega) (by omega))
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.nil_append] at hw hf hd ⊢
      simp only [hw.head]
      exact Runs.idx (by omega) (Runs.fnRest p false n ps r b hps hr hb ctx _ f R _ hw
        (by omega) (by omega))
  | module p n ps ds b =>
    have hk : (tokenAt ctx.input i).kind = .keyword "module" :=
      hw.head' (by simp [Item.toks_module])
    refine Runs.peek_bind ?_
    simp only [hk]
    exact Runs.moduleItem p n ps ds b hp ctx hpl i f R _ hw hf hd

theorem Item.headKind (it : Item) : ∃ k ks, it.toks = k :: ks ∧ k ≠ .eof := by
  have : ∃ k, it.toks.head? = some k ∧ k ≠ .eof := by
    cases it with
    | fn p c => cases c <;> simp [Item.toks]
    | module => simp [Item.toks_module]
    | const => simp [Item.toks]
  obtain ⟨k, hk, hne⟩ := this
  obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk
  exact ⟨k, ks, hks, hne⟩

theorem printToks_cons (it : Item) (L : List Item) :
    Print.toks (it :: L) = it.toks ++ Print.toks L := by
  simp [Print.toks]

/-! `items` reads the kinds of printable items back to them, up to positions, until `eof`. -/
theorem Runs.items (L : List Item) : ∀ (ctx : Ctx) (i f : Nat) (R : List Kind)
    (acc : List Item), ctx.plainFn = false → L.all Item.printable = true →
    Win ctx.input i (Print.toks L ++ .eof :: R) → 4 * (Print.toks L).length + 6 ≤ f →
    (Print.toks L).length ≤ ctx.depth →
    Runs (items f acc) ctx i (i + (Print.toks L).length)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧ ms.map Item.erase = L.map Item.erase) := by
  induction L with
  | nil =>
    intro ctx i f R acc _ _ hw hf _
    simp only [Print.toks, List.flatMap_nil, List.nil_append, List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.items]
    refine Runs.peek_bind ?_
    simp only [hw.head, beq_self_eq_true, ite_true]
    exact Runs.pure ⟨[], by simp, rfl⟩
  | cons it L ih =>
    intro ctx i f R acc hpl hp hw hf hd
    simp only [List.all_cons, Bool.and_eq_true] at hp
    rw [printToks_cons, List.append_assoc] at hw
    simp only [printToks_cons, List.length_append] at hf hd ⊢
    obtain ⟨k, ks, hks, hk⟩ := Item.headKind it
    have h1 : 1 ≤ it.toks.length := by simp [hks]
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.items]
    refine Runs.peek_bind ?_
    have hk0 := hw.head' (k := k) (by simp [hks])
    simp only [hk0, show (k == Kind.eof) = false from by rw [Kind.beq_eq]; exact decide_eq_false hk,
      Bool.false_eq_true, ite_false]
    refine Runs.bind (Runs.item it hp.1 ctx hpl i f _ hw (by omega) (by omega)) fun it' hit' => ?_
    refine Runs.idx (by omega) (Runs.mono (ih ctx _ f R (it' :: acc) hpl hp.2 hw.drop
      (by omega) (by omega)) ?_)
    rintro r ⟨ms, rfl, hms⟩
    exact ⟨it' :: ms, by simp, by simp [hit', hms]⟩

end Silicon.Source.ParsePrint
