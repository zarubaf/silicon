-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Names

/-!
The proofs of section 7.2 of the front-end spec. `decode` inverts `encode` on valid names, so
`encode` is injective on them. `encode` also makes only legal core names.
-/
namespace Silicon.Source.Names

open Silicon.Core

/-! Facts about characters and digits. -/

private theorem digit_fieldChar (c : Char) (h : c.isDigit = true) : fieldChar c = true := by
  simp [fieldChar, h]

private theorem fieldChar_ne_dollar (c : Char) (h : fieldChar c = true) : c ≠ '$' := by
  rintro rfl; simp [fieldChar, nameStart] at h

private theorem toDigits_digit (k : Nat) : ∀ c ∈ Nat.toDigits 10 k, c.isDigit = true :=
  fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

private theorem toList_toString (k : Nat) : (toString k).toList = Nat.toDigits 10 k := by
  simp

/-! A positive number has no leading zero. -/
private theorem toDigits_head (k : Nat) (hk : 0 < k) :
    ∃ c cs, Nat.toDigits 10 k = c :: cs ∧ c ≠ '0' := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · refine ⟨_, _, rfl, ?_⟩
      have : k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9] := by simp; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · obtain ⟨c, cs, hc, h0⟩ := ih (k / 10) (by omega) (by omega)
      exact ⟨c, _, by rw [hc]; rfl, h0⟩

private theorem decimal_toDigits (k : Nat) : decimal (Nat.toDigits 10 k) = some k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [decimal, Nat.toDigits_zero]
  obtain ⟨c, cs, hc, h0⟩ := toDigits_head k hk
  have all : (Nat.toDigits 10 k).all Char.isDigit = true := by
    simpa using toDigits_digit k
  unfold decimal
  split
  · simp_all
  · rename_i h
    have := Nat.ofDigitChars_ten_toDigits (n := k)
    rw [h] at this
    simp [Nat.ofDigitChars] at this
    omega
  · rename_i h
    rw [hc] at h
    exact (h0 (List.cons.inj h).1).elim
  · simp only [all, ↓reduceIte, ← Nat.repr_eq_ofList_toDigits, Nat.toNat?_repr]

/-! A digit run with a short suffix: the text of a number field. -/
private theorem takeWhile_digits (k : Nat) (tail : List Char)
    (ht : ∀ c ∈ tail.head?, c.isDigit = false) :
    (Nat.toDigits 10 k ++ tail).takeWhile Char.isDigit = Nat.toDigits 10 k := by
  rw [List.takeWhile_append_of_pos (by simpa using toDigits_digit k)]
  cases tail with
  | nil => simp
  | cons c cs => simp [ht c (by simp)]

private theorem digits_not_hex (k : Nat) (tail h : List Char) (ht : 'h' ∉ tail) :
    Nat.toDigits 10 k ++ tail ≠ '0' :: 'h' :: h := by
  intro e
  have hm : 'h' ∈ Nat.toDigits 10 k ++ tail := by rw [e]; simp
  rcases List.mem_append.mp hm with hm | hm
  · exact absurd (toDigits_digit k _ hm) (by decide)
  · exact ht hm

private theorem role_not_digits (r : Role) (k : Nat) (c : Char) :
    r.text.toList ≠ Nat.toDigits 10 k ++ [c] := by
  intro e
  have hd := congrArg List.dropLast e
  rw [List.dropLast_concat] at hd
  have hall : (r.text.toList.dropLast).all Char.isDigit = true := by
    rw [hd]; simpa using toDigits_digit k
  revert hall; cases r <;> decide

private theorem role_not_number (r : Role) (k : Nat) :
    r.text.toList ≠ Nat.toDigits 10 k := by
  intro e
  have hall : r.text.toList.all Char.isDigit = true := by
    rw [e]; simpa using toDigits_digit k
  revert hall; cases r <;> decide

private theorem find_none (s : String) (h : ∀ r : Role, r.text.toList ≠ s.toList) :
    roles.find? (·.text == s) = none := by
  rw [List.find?_eq_none]
  intro r _ e
  exact h r (by rw [beq_iff_eq.mp e])

private theorem find_role (r : Role) : roles.find? (·.text == r.text) = some r := by
  cases r <;> decide

/-! `madeField` on a decimal number `k` and the suffix `tail`. -/
private theorem madeField_digits (s : String) (k : Nat) (tail : List Char)
    (hs : s.toList = Nat.toDigits 10 k ++ tail) (hr : ∀ r : Role, r.text.toList ≠ s.toList)
    (ht : ∀ c ∈ tail.head?, c.isDigit = false) (hh : 'h' ∉ tail) :
    madeField s = match (generalizing := false) tail with
      | [] => some (.int k)
      | ['n'] => if k == 0 then none else some (.int (-k))
      | ['c'] => some (.call k)
      | ['v'] => some (.version k)
      | ['t'] => some (.temp k)
      | ['e'] => some (.elem k)
      | ['b'] => if k ≤ 1 then some (.bool (k == 1)) else none
      | _ => none := by
  unfold madeField
  rw [find_none s hr]
  simp only
  split
  · rename_i h e
    exact absurd (hs.symm.trans e) (digits_not_hex k tail h hh)
  · rw [hs, takeWhile_digits k tail ht, List.drop_left, decimal_toDigits]
    clear hr hs ht hh
    split <;> split <;> simp_all

private theorem userField_digit (s : String) (c : Char) (cs : List Char)
    (hs : s.toList = c :: cs) (hc : c.isDigit = true) : userField s = false := by
  unfold userField
  rw [hs]
  have : nameStart c = false := by
    have hv : c.toNat ≥ 48 ∧ c.toNat ≤ 57 := by
      simp [Char.isDigit, UInt32.le_iff_toNat_le] at hc; exact hc
    have hu : c ≠ '_' := by intro e; subst e; simp at hv
    simp [nameStart, Char.isAlpha, Char.isUpper, Char.isLower, UInt32.le_iff_toNat_le, hu]
    omega
  simp [this]

private theorem userField_digits (s : String) (k : Nat) (tail : List Char)
    (hs : s.toList = Nat.toDigits 10 k ++ tail) : userField s = false := by
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := k))
  exact userField_digit s c (cs ++ tail) (by rw [hs, hc]; rfl)
    (toDigits_digit k c (by rw [hc]; simp))

private theorem toList_suffix (k : Nat) (c : Char) :
    (toString k ++ String.singleton c).toList = Nat.toDigits 10 k ++ [c] := by
  simp

/-! `decodeField` inverts `Field.encode` on valid fields. -/
private theorem decodeField_encode (f : Field) (hf : f.valid = true) :
    decodeField f.encode = some f := by
  have number : ∀ (k : Nat) (c : Char) (g : Field),
      madeField (toString k ++ String.singleton c) = some g →
      decodeField (toString k ++ String.singleton c) = some g := by
    intro k c g hm
    unfold decodeField
    rw [userField_digits _ k [c] (toList_suffix k c)]
    exact hm
  have made : ∀ (k : Nat) (c : Char), c.isDigit = false → c ≠ 'h' →
      madeField (toString k ++ String.singleton c) = match (generalizing := false) [c] with
      | [] => some (.int k)
      | ['n'] => if k == 0 then none else some (.int (-k))
      | ['c'] => some (.call k)
      | ['v'] => some (.version k)
      | ['t'] => some (.temp k)
      | ['e'] => some (.elem k)
      | ['b'] => if k ≤ 1 then some (.bool (k == 1)) else none
      | _ => none := by
    intro k c hc hh
    exact madeField_digits _ k [c] (toList_suffix k c)
      (fun r => by rw [toList_suffix]; exact role_not_digits r k c) (by simpa using hc)
      (by simpa using hh.symm)
  cases f with
  | user s => simp [decodeField, Field.encode, show userField s = true from hf]
  | int n =>
    by_cases hn : n < 0
    · have e : s!"{n.natAbs}n" = toString n.natAbs ++ String.singleton 'n' := by simp; rfl
      simp only [Field.encode, hn, ↓reduceIte, e]
      refine number _ _ _ ?_
      rw [made _ _ (by decide) (by decide)]
      simp only [beq_iff_eq]
      rw [ite_eq_right_iff.mpr (by omega)]
      congr 2
      omega
    · simp only [Field.encode, hn, ↓reduceIte]
      have hs : (toString n.natAbs).toList = Nat.toDigits 10 n.natAbs ++ [] := by simp
      unfold decodeField
      rw [userField_digits _ _ [] hs, madeField_digits _ _ [] hs
        (fun r => by rw [hs, List.append_nil]; exact role_not_number r _) (by simp) (by simp)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 2
      omega
  | call k =>
    have e : s!"{k}c" = toString k ++ String.singleton 'c' := by simp; rfl
    simp only [Field.encode, e]
    exact number _ _ _ (by rw [made _ _ (by decide) (by decide)]; rfl)
  | version k =>
    have e : s!"{k}v" = toString k ++ String.singleton 'v' := by simp; rfl
    simp only [Field.encode, e]
    exact number _ _ _ (by rw [made _ _ (by decide) (by decide)]; rfl)
  | temp k =>
    have e : s!"{k}t" = toString k ++ String.singleton 't' := by simp; rfl
    simp only [Field.encode, e]
    exact number _ _ _ (by rw [made _ _ (by decide) (by decide)]; rfl)
  | elem k =>
    have e : s!"{k}e" = toString k ++ String.singleton 'e' := by simp; rfl
    simp only [Field.encode, e]
    exact number _ _ _ (by rw [made _ _ (by decide) (by decide)]; rfl)
  | bool b =>
    have hs : (Field.encode (.bool b)).toList = Nat.toDigits 10 (if b then 1 else 0) ++ ['b'] := by
      cases b <;> decide
    unfold decodeField
    rw [userField_digits _ _ _ hs, madeField_digits _ _ _ hs
      (fun r => by rw [hs]; exact role_not_digits r _ _) (by decide) (by decide)]
    cases b <;> rfl
  | digest h =>
    have hs : (Field.encode (.digest h)).toList = '0' :: 'h' :: h.toList := by
      simp [Field.encode]
    have hr : ∀ r : Role, r.text.toList ≠ (Field.encode (.digest h)).toList := by
      intro r e
      rw [hs] at e
      have := congrArg (·.take 2) e
      simp only [List.take_succ_cons, List.take_zero] at this
      revert this; cases r <;> decide
    unfold decodeField
    rw [userField_digit _ '0' _ hs (by decide)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold madeField
    rw [find_none _ hr, hs]
    simp [hf]
  | role r =>
    unfold decodeField
    rw [userField_digit _ '0' r.text.toList.tail (by cases r <;> decide) (by decide)]
    simp [madeField, Field.encode, find_role]

/-! Each valid field encodes to field characters, so it holds no `$`. -/

private theorem hex_fieldChar (c : Char) (h : hexDigit c = true) : fieldChar c = true := by
  by_cases hd : c.isDigit = true
  · exact digit_fieldChar c hd
  · simp only [hexDigit, hd, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl : c.isLower = true := by
      simp [Char.isLower, Char.le_def, UInt32.le_iff_toNat_le] at h ⊢; omega
    simp [fieldChar, nameStart, Char.isAlpha, hl]

private theorem user_chars (s : String) (hs : userField s = true) :
    ∃ c cs, s.toList = c :: cs ∧ nameStart c = true ∧ ∀ x ∈ cs, fieldChar x = true := by
  unfold userField at hs
  cases e : s.toList with
  | nil => simp [e] at hs
  | cons c cs =>
    simp only [e, Bool.and_eq_true, List.all_eq_true] at hs
    exact ⟨c, cs, rfl, hs.1, hs.2⟩

private def Fields (l : List Char) : Prop := l ≠ [] ∧ ∀ c ∈ l, fieldChar c = true

private theorem number_fields (k : Nat) (tail : List Char) (ht : ∀ c ∈ tail, fieldChar c = true) :
    Fields (Nat.toDigits 10 k ++ tail) := by
  refine ⟨by simp [Nat.toDigits_ne_nil], fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact digit_fieldChar c (toDigits_digit k c hc)
  · exact ht c hc

private theorem encode_fields (f : Field) (hf : f.valid = true) : Fields f.encode.toList := by
  cases f with
  | user s =>
    obtain ⟨c, cs, e, hc, hcs⟩ := user_chars s hf
    simp only [Field.encode, e]
    refine ⟨by simp, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [fieldChar, hc]
    · exact hcs x hx
  | int n =>
    by_cases hn : n < 0
    · have e : s!"{n.natAbs}n" = toString n.natAbs ++ String.singleton 'n' := by simp; rfl
      simp only [Field.encode, hn, ↓reduceIte, e, toList_suffix]
      exact number_fields _ _ (by decide)
    · simp only [Field.encode, hn, ↓reduceIte, toList_toString]
      simpa using number_fields n.natAbs [] (by simp)
  | call k =>
    have e : s!"{k}c" = toString k ++ String.singleton 'c' := by simp; rfl
    simp only [Field.encode, e, toList_suffix]
    exact number_fields _ _ (by decide)
  | version k =>
    have e : s!"{k}v" = toString k ++ String.singleton 'v' := by simp; rfl
    simp only [Field.encode, e, toList_suffix]
    exact number_fields _ _ (by decide)
  | temp k =>
    have e : s!"{k}t" = toString k ++ String.singleton 't' := by simp; rfl
    simp only [Field.encode, e, toList_suffix]
    exact number_fields _ _ (by decide)
  | elem k =>
    have e : s!"{k}e" = toString k ++ String.singleton 'e' := by simp; rfl
    simp only [Field.encode, e, toList_suffix]
    exact number_fields _ _ (by decide)
  | bool b => cases b <;> exact ⟨by decide, by decide⟩
  | digest h =>
    simp only [Field.valid, Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hx : ∀ c ∈ h.toList, hexDigit c = true := by simpa using hf.2
    simp only [Field.encode, String.toList_append, show "0h".toList = ['0', 'h'] from rfl]
    refine ⟨by simp, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with hc | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> decide
    · exact hex_fieldChar c (hx c hc)
  | role r => cases r <;> exact ⟨by decide, by decide⟩

private theorem fields_no_dollar (l : List Char) (h : Fields l) : '$' ∉ l :=
  fun hd => fieldChar_ne_dollar _ (h.2 _ hd) rfl

/-! The fields that `encode` joins. -/
private def parts (p : Name) : List String :=
  p.head :: if keyword p then ["0k"] else p.rest.map Field.encode

private theorem parts_fields (p : Name) (hp : p.valid = true) :
    ∀ s ∈ (parts p).tail, Fields s.toList := by
  simp only [Name.valid, Bool.and_eq_true, List.all_eq_true] at hp
  intro s hs
  simp only [parts, List.tail_cons] at hs
  split at hs
  · simp only [List.mem_singleton] at hs
    subst hs
    exact ⟨by decide, by decide⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hs
    exact encode_fields f (hp.2 f hf)

private theorem parts_no_dollar (p : Name) (hp : p.valid = true) :
    ∀ s ∈ parts p, '$' ∉ s.toList := by
  have hh : userField p.head = true := by
    simp only [Name.valid, Bool.and_eq_true] at hp; exact hp.1
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · obtain ⟨c, cs, e, hc, hcs⟩ := user_chars _ hh
    rw [e]
    exact fields_no_dollar _ ⟨by simp, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [fieldChar, hc]
      · exact hcs x hx⟩
  · exact fields_no_dollar _ (parts_fields p hp s hs)

/-! A split at each `$` gives back the joined fields. -/
private theorem split_join (l : List String) (h : ∀ s ∈ l, '$' ∉ s.toList) (hl : l ≠ []) :
    (("$".intercalate l).toList.splitOn '$').map String.ofList = l := by
  rw [String.toList_intercalate, show "$".toList = ['$'] from rfl,
    List.splitOn_intercalate '$' (by simpa using h) (by simpa using hl)]
  simp [List.map_map]

private theorem mapM_decode (fs : List Field) (h : ∀ f ∈ fs, f.valid = true) :
    (fs.map Field.encode).mapM decodeField = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp [List.mapM_cons, decodeField_encode f (h f (by simp)),
      ih (fun g hg => h g (by simp [hg]))]

/-! `decode` inverts `encode` on valid names (section 7.2). -/
theorem decode_encode (p : Name) (hp : p.valid = true) : decode (encode p) = some p := by
  have hd := parts_no_dollar p hp
  obtain ⟨h, rest⟩ := p
  simp only [Name.valid, Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨hh, hrest⟩ := hp
  unfold decode
  rw [show encode ⟨h, rest⟩ = "$".intercalate (parts ⟨h, rest⟩) from rfl,
    split_join _ hd (by simp [parts])]
  simp only [parts]
  by_cases hk : keyword ⟨h, rest⟩ = true
  · have hk' := hk
    simp only [keyword, Bool.and_eq_true, List.isEmpty_iff] at hk'
    obtain ⟨rfl, hc⟩ := hk'
    simp only [hk, ↓reduceIte]
    simp [show h ∈ keywords by simpa using hc]
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i h' e
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      cases rest with
      | nil => simp at e
      | cons f fs =>
        simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at e
        obtain ⟨e, rfl⟩ := e
        have := decodeField_encode f (hrest f (by simp))
        rw [e, show decodeField "0k" = none by decide] at this
        exact absurd this (by simp)
    · rename_i h' rest' _ e
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp [mapM_decode rest hrest, hh, hk]
    · simp at *

/-! `encode` is injective on valid names (section 10.3). -/
theorem names_injective (p q : Name) (hp : p.valid = true) (hq : q.valid = true)
    (h : encode p = encode q) : p = q := by
  have e := decode_encode p hp
  rw [h, decode_encode q hq] at e
  exact (Option.some.inj e).symm

/--
A leaf field `<k>e` never gives the name of the loop frame with the integer field `k`
(section 7.3). Thus the leaf `p.0.x` and the register `x` of the frame `p$0` differ.
-/
theorem leaf_ne_loop (h : String) (pre post : List Field) (k : Nat)
    (hp : (⟨h, pre ++ .elem k :: post⟩ : Name).valid = true) :
    encode ⟨h, pre ++ .elem k :: post⟩ ≠ encode ⟨h, pre ++ .int k :: post⟩ := by
  intro e
  have hq : (⟨h, pre ++ .int k :: post⟩ : Name).valid = true := by
    simpa [Name.valid, List.all_append, Field.valid] using hp
  have := names_injective _ _ hp hq e
  simp at this

/-! `encode` makes only legal core names. -/

private theorem fieldsRest_fields (a : List Char) (h : ∀ c ∈ a, fieldChar c = true)
    (rest : List Char) : fieldsRest (a ++ rest) = fieldsRest rest := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    simp [fieldsRest, fieldChar_ne_dollar c hc, hc, ih (fun x hx => h x (by simp [hx]))]

private theorem fieldsRest_join (a : List Char) (fs : List (List Char))
    (ha : ∀ c ∈ a, fieldChar c = true) (hfs : ∀ f ∈ fs, Fields f) :
    fieldsRest (['$'].intercalate (a :: fs)) = true := by
  induction fs generalizing a with
  | nil => simpa [fieldsRest] using fieldsRest_fields a ha []
  | cons f fs ih =>
    rw [List.intercalate_cons_cons, List.append_assoc, fieldsRest_fields a ha]
    obtain ⟨hne, hf⟩ := hfs f (by simp)
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hne
    have := ih (d :: ds) hf (fun g hg => hfs g (by simp [hg]))
    rw [List.intercalate_cons_cons_left] at this
    rw [List.intercalate_cons_cons_left, List.singleton_append, fieldsRest.eq_2, this]
    simp [hf d (by simp)]

theorem encode_validName (p : Name) (hp : p.valid = true) : validName (encode p) = true := by
  have hf := parts_fields p hp
  have hh : userField p.head = true := by
    simp only [Name.valid, Bool.and_eq_true] at hp; exact hp.1
  have join : encode p = "$".intercalate (parts p) := rfl
  obtain ⟨c, cs, e, hc, hcs⟩ := user_chars _ hh
  have pat : namePattern (encode p) = true := by
    unfold namePattern
    rw [join, String.toList_intercalate, show "$".toList = ['$'] from rfl]
    simp only [parts, List.map_cons, e, List.intercalate_cons_cons_left, hc, Bool.true_and]
    refine fieldsRest_join cs _ hcs fun f hm => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    exact hf s (by simpa [parts] using hs)
  simp only [validName, pat, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true]
  cases hk : keywords.contains (encode p) with
  | false => rfl
  | true =>
    exfalso
    have hm : encode p ∈ keywords := by simpa using hk
    have kw : ∀ s ∈ keywords, '$' ∉ s.toList := by decide
    cases ht : (parts p).tail with
    | nil =>
      simp only [parts, List.tail_cons] at ht
      split at ht
      · simp at ht
      · rename_i hnk
        have hr : p.rest = [] := by simpa using ht
        have hp' : parts p = [p.head] := by simp [parts, hnk, hr]
        rw [join, hp', String.intercalate_singleton] at hm
        simp [keyword, hr, hm] at hnk
    | cons b bs =>
      apply kw _ hm
      have hp' : parts p = p.head :: b :: bs := by
        rw [← ht]; rfl
      rw [join, hp', String.toList_intercalate]
      simp [List.intercalate_cons_cons]

end Silicon.Source.Names
