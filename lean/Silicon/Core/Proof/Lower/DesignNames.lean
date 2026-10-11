-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleWellFormed

/-!
Source module names are unique and match the name pattern. Memory model names are backend names,
and distinct configurations have distinct names.
-/
namespace Silicon.Core.LowerProof

theorem moduleName_invalid (c : MemConfig) : Rules.invalidName c.moduleName = true := by
  simp [Rules.invalidName, MemConfig.moduleName, backend_name_not_core]

private theorem split_injective {c : Char} {a b x y : List Char} (ha : c ∉ a) (hb : c ∉ b)
    (h : a ++ c :: x = b ++ c :: y) : a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons z zs =>
      have hz : z = c := (List.cons.inj h).1.symm
      subst z
      simp at hb
  | cons z zs ih =>
    cases b with
    | nil =>
      have hz : z = c := (List.cons.inj h).1
      subst z
      simp at ha
    | cons u us =>
      obtain ⟨rfl, ht⟩ := List.cons.inj h
      obtain ⟨rfl, rfl⟩ := ih (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h)) ht
      exact ⟨rfl, rfl⟩

private theorem digits (n : Nat) (c : Char) (hc : c.isDigit = false) : c ∉ n.repr.toList := by
  intro member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10)
    (show c ∈ Nat.toDigits 10 n from by simpa only [Nat.toList_repr] using member)
  rw [hc] at digit
  cases digit

private theorem repr_injective {a b : Nat} (h : a.repr.toList = b.repr.toList) : a = b :=
  Nat.repr_injective (String.toList_inj.mp h)

theorem moduleName_injective {a b : MemConfig} (h : a.moduleName = b.moduleName) : a = b := by
  replace h := String.append_right_inj ("mem" ++ "$$") |>.mp h
  change a.depth.repr ++ "x" ++ a.width.repr ++ "_r" ++ a.reads.repr ++ "w" ++
      a.writes.repr = b.depth.repr ++ "x" ++ b.width.repr ++ "_r" ++
      b.reads.repr ++ "w" ++ b.writes.repr at h
  have chars := congrArg String.toList h
  have hx : "x".toList = ['x'] := rfl
  have hr : "_r".toList = ['_', 'r'] := rfl
  have hw : "w".toList = ['w'] := rfl
  simp only [String.toList_append, List.append_assoc, hx, hr, hw, List.cons_append,
    List.nil_append] at chars
  obtain ⟨depth, tail⟩ := split_injective (digits _ 'x' rfl) (digits _ 'x' rfl) chars
  obtain ⟨width, tail⟩ := split_injective (digits _ '_' rfl) (digits _ '_' rfl) tail
  obtain ⟨reads, writes⟩ := split_injective (digits _ 'w' rfl) (digits _ 'w' rfl)
    (List.cons.inj tail).2
  cases a
  cases b
  simp only [MemConfig.mk.injEq]
  exact ⟨repr_injective depth, repr_injective width, repr_injective reads,
    repr_injective writes⟩

end Silicon.Core.LowerProof
