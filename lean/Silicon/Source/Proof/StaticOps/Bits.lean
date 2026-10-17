-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Container

/-!
The static pack of an enum payload (section 5.1) writes its leaves into the word buffer `Bits` of
`UInt64` words. `toNat_packAll` states its number: the leaf `l_i` at the offset `o_i`, the sum of
the widths of the earlier leaves, thus `l_0 ||| l_1 <<< o_1 ||| ...` (`refStep`), cut at the
width `P` of the buffer.

The proof views the words as one number (`num`) and states each bit of it (`testBit_num`). A step
of the loop of `Bits.put` writes one word of the leaf at the offset `o`: it sets the bits from `o`
to `o + 63` (`testBit_step`), also across two words. The loop of `(w + 63) / 64` steps thus writes
the `w` bits of the leaf (`put_spec`). A write above the last word is lost, so the number is cut
at the words, and `P` bits fit in them.

The statement holds for a list of leaves, each a `Bool` or a finite value (`Flat`). An aggregate
payload value and an enum payload value pack by recursion in `Value.pack`; the statement does not
cover them. The hardware pack takes the leaves as a flat list too (`Agg.packLeaves`), and no proof
ties the two lists together (#286).
-/
namespace Silicon.Source.StaticOps.Bits

open Eval

/-! The number of a list of words, the first word in the low bits. -/
def num (ws : List UInt64) : Nat := ws.foldr (fun w acc => (acc <<< 64) ||| w.toNat) 0

/-! `Bits.toNat` is the number of the words. -/
theorem toNat_eq (b : Eval.Bits) : b.toNat = num b.words.toList := by
  simp [Eval.Bits.toNat, num]

/-! The bit `k` of the number is the bit `k % 64` of the word `k / 64`, and 0 above the words. -/
theorem testBit_num : ∀ (ws : List UInt64) (k : Nat),
    (num ws).testBit k =
      if h : k / 64 < ws.length then ws[k / 64].toNat.testBit (k % 64) else false
  | [], k => by simp [num]
  | w :: ws, k => by
    simp only [num, List.foldr_cons]
    rw [← num, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hk : k < 64
    · have h1 : k / 64 = 0 := by omega
      have h2 : k % 64 = k := by omega
      have h3 : ¬ 64 ≤ k := by omega
      simp [h1, h2, h3]
    · have hw : w.toNat.testBit k = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le w.toNat_lt
          (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hw, testBit_num ws (k - 64)]
      have h1 : k / 64 = (k - 64) / 64 + 1 := by omega
      have h2 : k % 64 = (k - 64) % 64 := by omega
      have h3 : 64 ≤ k := by omega
      simp [h1, h2, h3]

theorem testBit_arr (ws : Array UInt64) (k : Nat) :
    (num ws.toList).testBit k =
      if h : k / 64 < ws.size then ws[k / 64].toNat.testBit (k % 64) else false := by
  rw [testBit_num]; simp

/-! An `or` into the word `i` sets the bits of `v` at the offset `64 * i`, inside the words. -/
theorem testBit_modify (ws : Array UInt64) (i : Nat) (v : UInt64) (k : Nat) :
    (num (ws.modify i (· ||| v)).toList).testBit k =
      ((num ws.toList).testBit k ||
        (decide (k / 64 = i) && decide (i < ws.size) && v.toNat.testBit (k % 64))) := by
  rw [testBit_arr, testBit_arr]
  simp only [Array.size_modify]
  split
  · rename_i h
    rw [Array.getElem_modify]
    by_cases hi : i = k / 64
    · subst hi; simp [UInt64.toNat_or, Nat.testBit_or, h]
    · simp [hi, Ne.symm hi]
  · rename_i h
    by_cases hi : k / 64 = i
    · subst hi; simp [h]
    · simp [hi]

/-! One step of the loop of `Bits.put`: the words, the rest of the leaf, and the offset. -/
def step (s : Array UInt64 × Nat × Nat) : Array UInt64 × Nat × Nat :=
  let ws := s.1.modify (s.2.2 / 64) (· ||| s.2.1.toUInt64 <<< (s.2.2 % 64).toUInt64)
  (if s.2.2 % 64 != 0 then
    ws.modify (s.2.2 / 64 + 1) (· ||| s.2.1.toUInt64 >>> (64 - s.2.2 % 64).toUInt64) else ws,
    s.2.1 >>> 64, s.2.2 + 64)

/-! A step sets the bits of the low word of the leaf from the offset `o` on, inside the words. -/
theorem testBit_step (ws : Array UInt64) (y o k : Nat) :
    (num (step (ws, y, o)).1.toList).testBit k =
      ((num ws.toList).testBit k || (decide (k < 64 * ws.size) && decide (o ≤ k) &&
        decide (k < o + 64) && y.testBit (k - o))) := by
  have hs : (o % 64).toUInt64.toNat = o % 64 := by simp; omega
  have hc : y.toUInt64.toNat = y % 2 ^ 64 := by simp
  simp only [step]
  split
  · rename_i hne
    have hne : o % 64 ≠ 0 := by simpa using hne
    have hr : (64 - o % 64).toUInt64.toNat % 64 = 64 - o % 64 := by simp; omega
    rw [testBit_modify, testBit_modify]
    simp only [Array.size_modify, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, hs, hr,
      hc, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    rw [Nat.mod_mod, Bool.or_assoc]
    congr 1
    by_cases c1 : k / 64 = o / 64 ∧ o % 64 ≤ k % 64
    · have e1 : k - o = k % 64 - o % 64 := by omega
      have e2 : ¬ k / 64 = o / 64 + 1 := by omega
      have e3 : (o / 64 < ws.size) = (k < 64 * ws.size) := by
        apply propext; omega
      simp [c1.1, c1.2, e1, e3, show o ≤ k by omega, show k < o + 64 by omega,
        show k % 64 - o % 64 < 64 by omega, show k % 64 < 64 by omega]
    by_cases c2 : k / 64 = o / 64 + 1 ∧ k % 64 < o % 64
    · have e1 : k - o = 64 - o % 64 + k % 64 := by omega
      have e2 : ¬ k / 64 = o / 64 := by omega
      have e3 : (o / 64 + 1 < ws.size) = (k < 64 * ws.size) := by
        apply propext; omega
      simp [c2.1, e1, e3, show o ≤ k by omega, show k < o + 64 by omega,
        show 64 - o % 64 + k % 64 < 64 by omega]
    · have e1 : ¬ (o ≤ k ∧ k < o + 64) := by omega
      by_cases c3 : k / 64 = o / 64
      · have : ¬ o % 64 ≤ k % 64 := fun h => c1 ⟨c3, h⟩
        simp [c3, this]
        omega
      · by_cases c4 : k / 64 = o / 64 + 1
        · have : ¬ 64 - o % 64 + k % 64 < 64 := by omega
          simp [c4, this]
          omega
        · simp [c3, c4]
          omega
  · rename_i he
    have he : o % 64 = 0 := by simpa using he
    rw [testBit_modify]
    simp only [UInt64.toNat_shiftLeft, hs, hc, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    rw [Nat.mod_mod]
    congr 1
    by_cases c1 : k / 64 = o / 64
    · have e1 : k - o = k % 64 := by omega
      have e3 : (o / 64 < ws.size) = (k < 64 * ws.size) := by
        apply propext; omega
      simp [c1, e1, e3, he, show o ≤ k by omega, show k < o + 64 by omega,
        show k % 64 < 64 by omega]
    · simp [c1]
      omega


theorem size_step (s : Array UInt64 × Nat × Nat) : (step s).1.size = s.1.size := by
  simp only [step]; split <;> simp

/-! After `j` steps, the bits from `o` to `o + 64 * j - 1` of the words hold the leaf. -/
theorem iterate_step (ws : Array UInt64) (x o : Nat) : ∀ j : Nat,
    (Nat.repeat step j (ws, x, o)).1.size = ws.size ∧
      (Nat.repeat step j (ws, x, o)).2.1 = x >>> (64 * j) ∧
      (Nat.repeat step j (ws, x, o)).2.2 = o + 64 * j ∧
      ∀ k, (num (Nat.repeat step j (ws, x, o)).1.toList).testBit k = ((num ws.toList).testBit k ||
        (decide (k < 64 * ws.size) && decide (o ≤ k) && decide (k < o + 64 * j) &&
          x.testBit (k - o)))
  | 0 => by
    refine ⟨rfl, by simp [Nat.repeat], by simp [Nat.repeat], fun k => ?_⟩
    simp only [Nat.repeat, Nat.mul_zero, Nat.add_zero]
    simp
    omega
  | j + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := iterate_step ws x o j
    rw [show Nat.repeat step (j + 1) (ws, x, o) = step (Nat.repeat step j (ws, x, o)) from rfl]
    generalize Nat.repeat step j (ws, x, o) = r at h1 h2 h3 h4
    obtain ⟨ws', y, o'⟩ := r
    simp only at h1 h2 h3 h4
    subst h2 h3
    refine ⟨by rw [size_step, h1], ?_, ?_, fun k => ?_⟩
    · simp [step, Nat.shiftRight_add, Nat.mul_succ]
    · simp [step]; omega
    · rw [testBit_step, h4, h1, Nat.testBit_shiftRight, Bool.or_assoc]
      congr 1
      by_cases c : o + 64 * j ≤ k ∧ k < o + 64 * j + 64
      · have e : 64 * j + (k - (o + 64 * j)) = k - o := by omega
        simp [e, c.1, c.2, show o ≤ k by omega, show k < o + 64 * (j + 1) by omega,
          show ¬ k < o + 64 * j by omega]
      · by_cases c2 : k < o + 64 * j
        · simp [c2, show k < o + 64 * (j + 1) by omega, show ¬ o + 64 * j ≤ k by omega]
        · simp [c2, show ¬ k < o + 64 * (j + 1) by omega]
          omega

theorem repeat_comm (s : Array UInt64 × Nat × Nat) : ∀ n,
    Nat.repeat step n (step s) = step (Nat.repeat step n s)
  | 0 => rfl
  | n + 1 => by simp only [Nat.repeat, repeat_comm s n]

/-! The `for` loop of `Bits.put` over `l` runs `step` once for each element of `l`. -/
theorem forIn_step
    (F : Nat → Array UInt64 × Nat × Nat → Id (ForInStep (Array UInt64 × Nat × Nat)))
    (hF : ∀ i s, F i s = pure (.yield (step s))) :
    ∀ (l : List Nat) s, forIn l s F = Nat.repeat step l.length s
  | [], _ => rfl
  | i :: l, s => by
    rw [List.forIn_cons, hF]
    simp only [pure_bind]
    rw [forIn_step F hF l, List.length_cons, repeat_comm]
    rfl

/-! `Bits.put` as `(w + 63) / 64` steps. -/
theorem put_eq (b : Bits) (w x : Nat) :
    b.put w x = ⟨(Nat.repeat step ((w + 63) / 64) (b.words, x, b.next)).1, b.next + w⟩ := by
  simp only [Bits.put, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_step _ fun i s => by simp only [step]; split <;> rfl]
  simp
  rfl


/-! The buffer `b` holds the number `a`, cut at its words. -/
def Rel (b : Bits) (a : Nat) : Prop :=
  ∀ k, (num b.words.toList).testBit k = (decide (k < 64 * b.words.size) && a.testBit k)

/-! `Bits.put` adds the `w` bits of `x` at the next free bit, and it keeps the word count. -/
theorem put_spec (b : Bits) (a w x : Nat) (hx : x < 2 ^ w) (h : Rel b a) :
    (b.put w x).words.size = b.words.size ∧ (b.put w x).next = b.next + w ∧
      Rel (b.put w x) (a ||| x <<< b.next) := by
  rw [put_eq]
  obtain ⟨h1, -, -, h4⟩ := iterate_step b.words x b.next ((w + 63) / 64)
  refine ⟨h1, rfl, fun k => ?_⟩
  simp only [h4, h1, h k, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases c : b.next ≤ k ∧ k - b.next < w
  · simp [c.1, show k < b.next + 64 * ((w + 63) / 64) by omega, Bool.and_or_distrib_left]
  · have : x.testBit (k - b.next) = false ∨ ¬ b.next ≤ k := by
      by_cases c1 : b.next ≤ k
      · exact .inl (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
          (Nat.pow_le_pow_right (by decide) (by omega))))
      · exact .inr c1
    rcases this with e | e <;> simp [e]

/-! The width and the number of a leaf of a pack: a `Bool` or a finite value. -/
def width : Value → Nat
  | .bool _ => 1
  | .uint w _ | .sint w _ => w
  | _ => 0

def bits : Value → Nat
  | .bool x => if x then 1 else 0
  | .uint _ x | .sint _ x => x.toNat
  | _ => 0

/-! A leaf of a pack: a `Bool` or a finite value. -/
def Flat : Value → Prop
  | .bool _ | .uint .. | .sint .. => True
  | _ => False

/-! One leaf of the reference pack: the number so far and its offset. -/
def refStep (s : Nat × Nat) (v : Value) : Nat × Nat := (s.1 ||| bits v <<< s.2, s.2 + width v)

/-! The pack of a leaf is one `Bits.put` of its width and its number. -/
theorem pack_flat (b : Bits) (v : Value) (hv : Flat v) :
    Value.pack b v = b.put (width v) (bits v) ∧ bits v < 2 ^ width v := by
  cases v <;> simp [Flat] at hv <;> simp [Value.pack, width, bits]
  all_goals first | exact BitVec.isLt _ | split <;> decide


/-! `Value.packAll` of flat leaves follows `refStep` from the number and the offset of `b`. -/
theorem packAll_spec : ∀ (vs : List Value) (b : Bits) (a : Nat), (∀ v ∈ vs, Flat v) → Rel b a →
    (Value.packAll b vs).words.size = b.words.size ∧
      (Value.packAll b vs).next = (vs.foldl refStep (a, b.next)).2 ∧
      Rel (Value.packAll b vs) (vs.foldl refStep (a, b.next)).1
  | [], b, a, _, h => by simp [Value.packAll, h]
  | v :: vs, b, a, hv, h => by
    obtain ⟨hp, hlt⟩ := pack_flat b v (hv v (by simp))
    obtain ⟨h1, h2, h3⟩ := put_spec b a (width v) (bits v) hlt h
    obtain ⟨g1, g2, g3⟩ := packAll_spec vs _ _ (fun u hu => hv u (by simp [hu])) h3
    simp only [Value.packAll, hp, List.foldl_cons]
    rw [h2] at g2 g3
    exact ⟨g1.trans h1, g2, g3⟩

/-! A new buffer holds 0. -/
theorem rel_new (P : Nat) : Rel (Bits.new P) 0 := fun k => by
  rw [testBit_arr]
  simp [Bits.new]

/--
`Value.packAll` of the leaves `vs` into a buffer of `P` bits gives the reference number, cut at
`P` bits. The reference number has the leaf `l_i` at the offset `o_i`, the sum of the earlier
widths.
-/
theorem toNat_packAll (P : Nat) (vs : List Value) (hv : ∀ v ∈ vs, Flat v) :
    BitVec.ofNat P (Value.packAll (Bits.new P) vs).toNat =
      BitVec.ofNat P (vs.foldl refStep (0, 0)).1 := by
  obtain ⟨h1, -, h3⟩ := packAll_spec vs (Bits.new P) 0 hv (rel_new P)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat, toNat_eq, h3 i, h1]
  simp [Bits.new, hi, show i < 64 * ((P + 63) / 64) by omega]

end Silicon.Source.StaticOps.Bits
