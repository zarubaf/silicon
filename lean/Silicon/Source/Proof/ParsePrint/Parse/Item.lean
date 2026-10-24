-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Parse.Stmt

/-!
The parser lemma of `parse_print` for items and files.

`Runs.items` reads the kinds `Print.toks items` of a printable file back to its items, up to
positions. It stops at `eof`. The fuel is four times the number of kinds, plus six. The
fuel of `parse` is 32 times the number of tokens, plus 32, so it is sufficient.
`Runs.enumItem` reads an enum: `Runs.variant` reads each variant, and `Runs.payload` reads its
payload types.
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

theorem Runs.paramMode {static : Bool} {c : ParamMode} (hc : c.printable static = true)
    {ctx : Ctx} {i : Nat} {n : String} {R : List Kind}
    (hw : Win ctx.input i (c.toks ++ .ident n :: R)) :
    Runs (paramMode static) ctx i (i + c.toks.length) (· = c) := by
  cases c with
  | «mut» =>
    simp only [ParamMode.toks, List.cons_append, List.nil_append, List.length_singleton] at hw ⊢
    cases static with
    | true => simp [ParamMode.printable] at hc
    | false =>
      rw [Parse.paramMode]
      refine Runs.bind (Runs.acceptKw_false (by rw [hw.head]; simp)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.bind (Runs.acceptKw_true hw.head) fun b hb => ?_
      subst b
      reduce_checks
      exact Runs.pure rfl
  | comptime =>
    simp only [ParamMode.toks, List.cons_append, List.nil_append, List.length_singleton] at hw ⊢
    cases static with
    | true =>
      rw [Parse.paramMode]
      exact Runs.seqRight (Runs.kw hw.head) (Runs.pure rfl)
    | false =>
      rw [Parse.paramMode]
      refine Runs.bind (Runs.acceptKw_true hw.head) fun b hb => ?_
      subst b
      reduce_checks
      exact Runs.pure rfl
  | none =>
    simp only [ParamMode.toks, List.nil_append, List.length_nil, Nat.add_zero] at hw ⊢
    cases static with
    | true => simp [ParamMode.printable] at hc
    | false =>
      rw [Parse.paramMode]
      refine Runs.bind (Runs.acceptKw_false (by rw [hw.head]; simp)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.bind (Runs.acceptKw_false (by rw [hw.head]; simp)) fun b hb => ?_
      subst b
      reduce_checks
      exact Runs.pure rfl

theorem Runs.param (q : Param) (static : Bool) (hp : q.printable static = true) (ctx : Ctx)
    (i f : Nat) (u : Kind) (R : List Kind) (hw : Win ctx.input i (q.toks ++ u :: R))
    (hu : u ≠ .symbol "[" ∧ u ≠ .symbol "(" ∧ u ≠ .symbol "::") (hf : 4 * q.ty.toks.length ≤ f)
    (hd : q.ty.toks.length ≤ ctx.depth) :
    Runs (param f static) ctx i (i + q.toks.length) (fun r => r.erase = q.erase) := by
  obtain ⟨pos, c, n, ty⟩ := q
  simp only [Param.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hc, hn⟩, hty⟩ := hp
  simp only at hf hd
  have e : (Param.toks ⟨pos, c, n, ty⟩) ++ u :: R =
      c.toks ++ .ident n.name :: .symbol ":" :: (ty.toks ++ u :: R) := by
    simp [Param.toks]
  have hT : (Param.toks ⟨pos, c, n, ty⟩).length = c.toks.length + 2 + ty.toks.length := by
    simp [Param.toks]; omega
  rw [e] at hw
  rw [hT]
  unfold Parse.param
  refine Runs.peek_bind ?_
  refine Runs.bind (Runs.paramMode hc hw) fun m hm => ?_
  subst hm
  have w := hw.drop
  refine Runs.bind (Runs.ident w.head) fun id hid => ?_
  refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ w.tail hu hf hd)
    fun ty' hty' => Runs.idx (by omega) (Runs.pure ?_)
  simp [Param.erase, Ident.erase_of_name (b := n) hid, hty']

theorem Param.headKind (q : Param) : ∃ k ks, q.toks = k :: ks ∧ k ≠ .symbol ")" ∧
    k ≠ .symbol "," := by
  obtain ⟨pos, c, n, ty⟩ := q
  cases c
  · exact ⟨.ident n.name, .symbol ":" :: ty.toks, by simp [Param.toks, ParamMode.toks], by simp,
      by simp⟩
  · exact ⟨.keyword "comptime", .ident n.name :: .symbol ":" :: ty.toks,
      by simp [Param.toks, ParamMode.toks], by decide, by decide⟩
  · exact ⟨.keyword "mut", .ident n.name :: .symbol ":" :: ty.toks,
      by simp [Param.toks, ParamMode.toks], by decide, by decide⟩

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
      cases c <;> simp [Param.toks, ParamMode.toks]
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
    (hb : Stmt.printableAll b = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
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
  refine Runs.bind (Runs.block_print b ctx _ f R hb w4 (by omega) (by omega)) fun b' hb' => ?_
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
    (b : List Stmt) (hp : (Item.module p n ps ds b).printable = true) (ctx : Ctx) (i f : Nat)
    (R : List Kind) (start : Pos)
    (hw : Win ctx.input i ((Item.module p n ps ds b).toks ++ R))
    (hf : 4 * (Item.module p n ps ds b).toks.length + 5 ≤ f)
    (hd : (Item.module p n ps ds b).toks.length ≤ ctx.depth) :
    Runs (moduleItem f start) ctx i (i + (Item.module p n ps ds b).toks.length)
      (fun it => it.erase = (Item.module p n ps ds b).erase) := by
  simp only [Item.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨hn, hps⟩, hds⟩, hb⟩ := hp
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

/-! `fields` reads the fields of a struct after its `{`, up to its `}`. -/
theorem Runs.fields (fs : List StructField)
    (hp : fs.all (fun f => validName f.name.name && f.ty.printable) = true) :
    ∀ (ctx : Ctx) (i f : Nat) (R : List Kind) (acc : List StructField),
    Win ctx.input i (fs.flatMap StructField.toks ++ .symbol "}" :: R) →
    4 * (fs.flatMap StructField.toks).length + 1 ≤ f →
    (fs.flatMap StructField.toks).length ≤ ctx.depth →
    Runs (fields f acc) ctx i (i + (fs.flatMap StructField.toks).length + 1)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧
        ms.map StructField.erase = fs.map StructField.erase) := by
  induction fs with
  | nil =>
    intro ctx i f R acc hw hf _
    simp only [List.flatMap_nil, List.nil_append, List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.fields]
    refine Runs.bind (Runs.acceptSym_true hw.head) fun b hb => ?_
    subst b
    exact Runs.pure ⟨[], by simp, rfl⟩
  | cons x xs ih =>
    intro ctx i f R acc hw hf hd
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨⟨hn, hty⟩, hxs⟩ := hp
    have e : (x :: xs).flatMap StructField.toks ++ .symbol "}" :: R = .ident x.name.name ::
        .symbol ":" :: (x.ty.toks ++ .symbol "," ::
        (xs.flatMap StructField.toks ++ .symbol "}" :: R)) := by
      simp [StructField.toks]
    have hT : ((x :: xs).flatMap StructField.toks).length =
        x.ty.toks.length + (xs.flatMap StructField.toks).length + 3 := by
      simp [StructField.toks]; omega
    rw [e] at hw
    rw [hT] at hf hd ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.fields]
    refine Runs.bind (Runs.acceptSym_false (by rw [hw.head]; simp)) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.bind (Runs.ident hw.head) fun id hid => ?_
    refine Runs.bind (Runs.typeAnnotation x.ty hty ctx _ f _ _ hw.tail (by decide) (by omega)
      (by omega)) fun ty' hty' => ?_
    have w := hw.tail.tail.drop
    refine Runs.bind (Runs.acceptSym_false (by rw [w.head]; decide)) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.sym_bind w.head ?_
    refine Runs.idx (by omega) (Runs.mono (ih hxs ctx _ f R (⟨id, ty'⟩ :: acc) w.tail
      (by omega) (by omega)) ?_)
    rintro r ⟨ms, rfl, hms⟩
    refine ⟨⟨id, ty'⟩ :: ms, by simp, ?_⟩
    simp [hms, StructField.erase, Ident.erase_of_name (b := x.name) hid, hty']

theorem Runs.structItem (p : Pos) (n : Ident) (ps : List Param) (fs : List StructField)
    (hp : (Item.struct p n ps fs).printable = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (start : Pos) (hw : Win ctx.input i ((Item.struct p n ps fs).toks ++ R))
    (hf : 4 * (Item.struct p n ps fs).toks.length + 5 ≤ f)
    (hd : (Item.struct p n ps fs).toks.length ≤ ctx.depth) :
    Runs (structItem f start) ctx i (i + (Item.struct p n ps fs).toks.length)
      (fun it => it.erase = (Item.struct p n ps fs).erase) := by
  simp only [Item.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hn, hps⟩, hfs⟩ := hp
  unfold Parse.structItem
  have body : ∀ (j : Nat) (ms : List Param), ms.map Param.erase = ps.map Param.erase →
      Win ctx.input j (.symbol "{" :: (fs.flatMap StructField.toks ++ .symbol "}" :: R)) →
      i ≤ j →
      j + (fs.flatMap StructField.toks).length + 2 = i + (Item.struct p n ps fs).toks.length →
      ∀ id : Ident, id.name = n.name →
      Runs (Parse.sym "{" >>= fun _ => Parse.fields f [] >>= fun fs' =>
          (Pure.pure (Item.struct start id ms fs') : P Item)) ctx j
        (i + (Item.struct p n ps fs).toks.length)
        (fun it => it.erase = (Item.struct p n ps fs).erase) := by
    intro j ms hms w hij hj id hid
    refine Runs.sym_bind w.head ?_
    refine Runs.bind (Runs.fields fs hfs ctx _ f R [] w.tail (by omega) (by omega))
      fun fs' hfs' => ?_
    obtain ⟨ms', rfl, hms'⟩ := hfs'
    refine Runs.idx (by omega) (Runs.pure ?_)
    simp [Item.erase, Ident.erase_of_name (b := n) hid, hms, hms']
  cases ps with
  | nil =>
    have e : (Item.struct p n [] fs).toks ++ R = .keyword "struct" :: .ident n.name ::
        .symbol "{" :: (fs.flatMap StructField.toks ++ .symbol "}" :: R) := by
      simp [Item.toks]
    have hT : (Item.struct p n [] fs).toks.length = (fs.flatMap StructField.toks).length + 4 := by
      simp [Item.toks]
    rw [e] at hw
    refine Runs.kw_bind hw.head ?_
    refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
    have w := hw.tail.tail
    refine Runs.bind (Runs.acceptSym_false (by rw [w.head]; decide)) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.bind (Runs.pure (Q := (· = [])) rfl) fun ms hms => ?_
    subst ms
    exact body _ [] rfl w (by omega) (by rw [hT]; omega) id hid
  | cons q qs =>
    have e : (Item.struct p n (q :: qs) fs).toks ++ R = .keyword "struct" :: .ident n.name ::
        .symbol "(" :: (argToks ((q :: qs).map Param.toks) ++ .symbol ")" ::
        .symbol "{" :: (fs.flatMap StructField.toks ++ .symbol "}" :: R)) := by
      simp [Item.toks]
    have hT : (Item.struct p n (q :: qs) fs).toks.length =
        (argToks ((q :: qs).map Param.toks)).length + (fs.flatMap StructField.toks).length +
          6 := by
      simp [Item.toks]; omega
    rw [e] at hw
    rw [hT] at hf hd
    refine Runs.kw_bind hw.head ?_
    refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
    have w := hw.tail.tail
    refine Runs.bind (Runs.acceptSym_true w.head) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.bind (Runs.params true (q :: qs) ctx _ f _ [] hps w.tail (by omega) (by omega))
      fun ps' hps' => ?_
    obtain ⟨ms, rfl, hms⟩ := hps'
    exact body _ _ (by simpa using hms) w.tail.drop.tail (by omega) (by rw [hT]; omega) id hid

/-! `payload` reads the payload types of a variant after its `(`, up to its `)`. -/
theorem Runs.payload (ts : List TypeExpr) : ∀ (ctx : Ctx) (i f : Nat) (R : List Kind)
    (acc : List TypeExpr), ts.all TypeExpr.printable = true →
    Win ctx.input i (argToks (ts.map TypeExpr.toks) ++ .symbol ")" :: R) →
    4 * (argToks (ts.map TypeExpr.toks)).length + 2 ≤ f →
    (argToks (ts.map TypeExpr.toks)).length ≤ ctx.depth →
    Runs (payload f acc) ctx i (i + (argToks (ts.map TypeExpr.toks)).length + 1)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧ ms.map TypeExpr.erase = ts.map TypeExpr.erase) := by
  induction ts with
  | nil =>
    intro ctx i f R acc _ hw hf _
    simp only [List.map_nil, Print.argToks, List.intercalate_nil, List.nil_append,
      List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.payload]
    refine Runs.bind (Runs.acceptSym_true hw.head) fun b hb => ?_
    subst b
    exact Runs.pure ⟨[], by simp, rfl⟩
  | cons q qs ih =>
    intro ctx i f R acc hp hw hf hd
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨k, ks, hks, hk⟩ := TypeExpr.toks_head q
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.payload]
    cases qs with
    | nil =>
      simp only [List.map_cons, List.map_nil, argToks_single] at hw hf hd ⊢
      refine Runs.bind (Runs.acceptSym_false (by
        rw [hw.head' (k := k) (by simp [hks])]; exact hk.1)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.bind (Runs.typeTop q hp.1 ctx i f _ R hw (by decide) (by omega) (by omega))
        fun q' hq' => ?_
      refine Runs.bind (Runs.acceptSym_true hw.drop.head) fun b hb => ?_
      subst b
      reduce_checks
      exact Runs.pure ⟨[q'], by simp, by simp [hq']⟩
    | cons q2 qs2 =>
      simp only [List.map_cons, argToks_cons_cons, List.append_assoc, List.cons_append,
        List.length_append, List.length_cons] at hw hf hd ⊢
      have hw' : Win ctx.input i (q.toks ++ .symbol "," ::
          (argToks ((q2 :: qs2).map TypeExpr.toks) ++ .symbol ")" :: R)) := by
        simpa using hw
      refine Runs.bind (Runs.acceptSym_false (by
        rw [hw'.head' (k := k) (by simp [hks])]; exact hk.1)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.bind (Runs.typeTop q hp.1 ctx i f _ _ hw' (by decide) (by omega) (by omega))
        fun q' hq' => ?_
      have w := hw'.drop
      refine Runs.bind (Runs.acceptSym_false (by rw [w.head]; decide)) fun b hb => ?_
      subst b
      reduce_checks
      refine Runs.sym_bind w.head ?_
      have := ih ctx _ f R (q' :: acc) hp.2 w.tail (by simp; omega) (by simp; omega)
      refine Runs.idx (by simp; omega) (Runs.mono this ?_)
      rintro r ⟨ms, rfl, hms⟩
      exact ⟨q' :: ms, by simp, by simp [hq', hms]⟩

/-! The kinds of a variant: its name, its payload, `=`, its tag value, and `,`. -/
theorem Variant.toks_eq (v : Variant) : v.toks = .ident v.name.name ::
    (Variant.payloadToks v.payload ++ .symbol "=" :: (v.tag.toks 0 ++ [.symbol ","])) := by
  simp [Variant.toks]

/-! `variant` reads a variant up to its `,`. -/
theorem Runs.variant (n : Ident) (ps : List TypeExpr) (tag : Expr)
    (hp : (Variant.mk n ps tag).printable = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (hw : Win ctx.input i (.ident n.name :: (Variant.payloadToks ps ++
      .symbol "=" :: (tag.toks 0 ++ .symbol "," :: R))))
    (hf : 4 * ((Variant.payloadToks ps).length + (tag.toks 0).length) + 5 ≤ f)
    (hd : (Variant.payloadToks ps).length + (tag.toks 0).length ≤ ctx.depth) :
    Runs (variant f) ctx i (i + 1 + (Variant.payloadToks ps).length + 1 + (tag.toks 0).length)
      (fun v => v.erase = (Variant.mk n ps tag).erase) := by
  simp only [Variant.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hn, hps⟩, htag⟩ := hp
  unfold Parse.variant
  refine Runs.bind (Runs.ident hw.head) fun id hid => ?_
  cases ps with
  | nil =>
    have e : Variant.payloadToks [] = [] := rfl
    rw [e] at hw hf hd ⊢
    simp only [List.nil_append, List.length_nil] at hw hf hd ⊢
    refine Runs.bind (Runs.acceptSym_false (by rw [hw.tail.head]; decide)) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.bind (Runs.pure (Q := (· = [])) rfl) fun ps' hps' => ?_
    subst ps'
    refine Runs.sym_bind hw.tail.head ?_
    refine Runs.bind (Runs.value tag htag ctx _ f _ _ hw.tail.tail After.comma (by omega)
      (by omega)) fun v' hv' => Runs.idx (by omega) (Runs.pure ?_)
    simp [Variant.erase, Ident.erase_of_name (b := n) hid, hv']
  | cons q qs =>
    have e : Variant.payloadToks (q :: qs) =
        .symbol "(" :: (argToks ((q :: qs).map TypeExpr.toks) ++ [.symbol ")"]) := rfl
    rw [e] at hw hf hd ⊢
    simp only [List.cons_append, List.append_assoc, List.length_cons, List.length_append,
      List.length_nil] at hw hf hd ⊢
    refine Runs.bind (Runs.acceptSym_true hw.tail.head) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.bind (Runs.payload (q :: qs) ctx _ f _ [] hps hw.tail.tail (by omega)
      (by omega)) fun ps' hps' => ?_
    obtain ⟨ms, rfl, hms⟩ := hps'
    have w := hw.tail.tail.drop.tail
    refine Runs.sym_bind w.head ?_
    refine Runs.bind (Runs.value tag htag ctx _ f _ _ w.tail After.comma (by omega)
      (by omega)) fun v' hv' => Runs.idx (by omega) (Runs.pure ?_)
    simp [Variant.erase, Ident.erase_of_name (b := n) hid, hv', hms]

/-! `variants` reads the variants of an enum after its `{`, up to its `}`. -/
theorem Runs.variants (vs : List Variant) (hp : vs.all Variant.printable = true) :
    ∀ (ctx : Ctx) (i f : Nat) (R : List Kind) (acc : List Variant),
    Win ctx.input i (vs.flatMap Variant.toks ++ .symbol "}" :: R) →
    4 * (vs.flatMap Variant.toks).length + 1 ≤ f →
    (vs.flatMap Variant.toks).length ≤ ctx.depth →
    Runs (variants f acc) ctx i (i + (vs.flatMap Variant.toks).length + 1)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧ ms.map Variant.erase = vs.map Variant.erase) := by
  induction vs with
  | nil =>
    intro ctx i f R acc hw hf _
    simp only [List.flatMap_nil, List.nil_append, List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.variants]
    refine Runs.bind (Runs.acceptSym_true hw.head) fun b hb => ?_
    subst b
    exact Runs.pure ⟨[], by simp, rfl⟩
  | cons x xs ih =>
    intro ctx i f R acc hw hf hd
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨n, ps, tag⟩ := x
    simp only [List.flatMap_cons, List.length_append] at hw hf hd ⊢
    rw [List.append_assoc, Variant.toks_eq] at hw
    rw [Variant.toks_eq] at hf hd ⊢
    simp only [List.cons_append, List.append_assoc, List.length_cons, List.length_append,
      List.length_nil] at hw hf hd ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.variants]
    refine Runs.bind (Runs.acceptSym_false (by rw [hw.head]; simp)) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.bind (Runs.variant n ps tag hp.1 ctx i f _ hw (by omega) (by omega))
      fun v hv => ?_
    have w := hw.tail.drop.tail.drop
    refine Runs.bind (Runs.acceptSym_false (by rw [w.head]; decide)) fun b hb => ?_
    subst b
    reduce_checks
    refine Runs.sym_bind w.head ?_
    refine Runs.idx (by omega) (Runs.mono (ih hp.2 ctx _ f R (v :: acc) w.tail
      (by omega) (by omega)) ?_)
    rintro r ⟨ms, rfl, hms⟩
    exact ⟨v :: ms, by simp, by simp [hms, hv]⟩

theorem Runs.enumItem (p : Pos) (n : Ident) (ty : TypeExpr) (vs : List Variant)
    (hp : (Item.enum p n ty vs).printable = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (start : Pos) (hw : Win ctx.input i ((Item.enum p n ty vs).toks ++ R))
    (hf : 4 * (Item.enum p n ty vs).toks.length + 5 ≤ f)
    (hd : (Item.enum p n ty vs).toks.length ≤ ctx.depth) :
    Runs (enumItem f start) ctx i (i + (Item.enum p n ty vs).toks.length)
      (fun it => it.erase = (Item.enum p n ty vs).erase) := by
  simp only [Item.printable, Bool.and_eq_true] at hp
  obtain ⟨⟨hn, hty⟩, hvs⟩ := hp
  have e : (Item.enum p n ty vs).toks ++ R = .keyword "enum" :: .ident n.name ::
      .symbol ":" :: (ty.toks ++ .symbol "{" :: (vs.flatMap Variant.toks ++ .symbol "}" :: R)) := by
    simp [Item.toks]
  have hT : (Item.enum p n ty vs).toks.length =
      ty.toks.length + (vs.flatMap Variant.toks).length + 5 := by
    simp [Item.toks]; omega
  rw [e] at hw
  rw [hT] at hf hd ⊢
  unfold Parse.enumItem
  refine Runs.kw_bind hw.head ?_
  refine Runs.bind (Runs.ident hw.tail.head) fun id hid => ?_
  refine Runs.peek_bind ?_
  simp only [show isSym "(" (tokenAt ctx.input (i + 1 + 1)) = false by
    simp [isSym, hw.tail.tail.head], Bool.false_eq_true, ite_false]
  refine Runs.bind (Runs.typeAnnotation ty hty ctx _ f _ _ hw.tail.tail (by decide) (by omega)
    (by omega)) fun ty' hty' => ?_
  have w := hw.tail.tail.tail.drop
  refine Runs.sym_bind w.head ?_
  refine Runs.bind (Runs.variants vs hvs ctx _ f R [] w.tail (by omega) (by omega))
    fun vs' hvs' => ?_
  obtain ⟨ms, rfl, hms⟩ := hvs'
  refine Runs.idx (by omega) (Runs.pure ?_)
  simp [Item.erase, Ident.erase_of_name (b := n) hid, hty', hms]

/-! `item` reads the kinds of a printable item back to it, up to positions. -/
theorem Runs.item (it : Item) (hp : it.printable = true) (ctx : Ctx) (i f : Nat) (R : List Kind)
    (hw : Win ctx.input i (it.toks ++ R))
    (hf : 4 * it.toks.length + 5 ≤ f) (hd : it.toks.length ≤ ctx.depth) :
    Runs (item f) ctx i (i + it.toks.length) (fun r => r.erase = it.erase) := by
  unfold Parse.item
  cases it with
  | enum p n ty vs =>
    have hk : (tokenAt ctx.input i).kind = .keyword "enum" := hw.head' (by simp [Item.toks])
    refine Runs.peek_bind ?_
    simp only [hk]
    exact Runs.enumItem p n ty vs hp ctx i f R _ hw hf hd
  | struct p n ps fs =>
    have hk : (tokenAt ctx.input i).kind = .keyword "struct" := hw.head' (by simp [Item.toks])
    refine Runs.peek_bind ?_
    simp only [hk]
    exact Runs.structItem p n ps fs hp ctx i f R _ hw hf hd
  | alias p n ty =>
    simp only [Item.printable, Bool.and_eq_true] at hp
    have e : (Item.alias p n ty).toks ++ R = .keyword "type" :: .ident n.name ::
        .symbol "=" :: (ty.toks ++ .symbol ";" :: R) := by
      simp [Item.toks]
    have hT : (Item.alias p n ty).toks.length = ty.toks.length + 4 := by
      simp [Item.toks]
    rw [e] at hw
    rw [hT] at hf hd ⊢
    refine Runs.peek_bind ?_
    simp only [hw.head]
    refine Runs.mono (Runs.aliasDecl n ty hp.2 ctx i f _ _ R hw (by omega) (by omega)) ?_
    rintro _ ⟨id, ty', hid, hty', rfl⟩
    simp [Item.erase, Ident.erase_of_name (b := n) hid, hty']
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
    exact Runs.moduleItem p n ps ds b hp ctx i f R _ hw hf hd

theorem Item.headKind (it : Item) : ∃ k ks, it.toks = k :: ks ∧ k ≠ .eof := by
  have : ∃ k, it.toks.head? = some k ∧ k ≠ .eof := by
    cases it with
    | fn p c => cases c <;> simp [Item.toks]
    | module => simp [Item.toks_module]
    | const | struct | alias | enum => simp [Item.toks]
  obtain ⟨k, hk, hne⟩ := this
  obtain ⟨ks, hks⟩ := List.head?_eq_some_iff.1 hk
  exact ⟨k, ks, hks, hne⟩

theorem printToks_cons (it : Item) (L : List Item) :
    Print.toks (it :: L) = it.toks ++ Print.toks L := by
  simp [Print.toks]

/-! `items` reads the kinds of printable items back to them, up to positions, until `eof`. -/
theorem Runs.items (L : List Item) : ∀ (ctx : Ctx) (i f : Nat) (R : List Kind)
    (acc : List Item), L.all Item.printable = true →
    Win ctx.input i (Print.toks L ++ .eof :: R) → 4 * (Print.toks L).length + 6 ≤ f →
    (Print.toks L).length ≤ ctx.depth →
    Runs (items f acc) ctx i (i + (Print.toks L).length)
      (fun r => ∃ ms, r = acc.reverse ++ ms ∧ ms.map Item.erase = L.map Item.erase) := by
  induction L with
  | nil =>
    intro ctx i f R acc _ hw hf _
    simp only [Print.toks, List.flatMap_nil, List.nil_append, List.length_nil] at hw hf ⊢
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Parse.items]
    refine Runs.peek_bind ?_
    simp only [hw.head, beq_self_eq_true, ite_true]
    exact Runs.pure ⟨[], by simp, rfl⟩
  | cons it L ih =>
    intro ctx i f R acc hp hw hf hd
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
    refine Runs.bind (Runs.item it hp.1 ctx i f _ hw (by omega) (by omega)) fun it' hit' => ?_
    refine Runs.idx (by omega) (Runs.mono (ih ctx _ f R (it' :: acc) hp.2 hw.drop
      (by omega) (by omega)) ?_)
    rintro r ⟨ms, rfl, hms⟩
    exact ⟨it' :: ms, by simp, by simp [hit', hms]⟩

end Silicon.Source.ParsePrint
