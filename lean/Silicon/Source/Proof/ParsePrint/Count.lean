-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Lex

/-!
The number of tokens of the lexer, for `parse_print`. The lexer gives at most one token for
each character, and then `eof`:

```lean
theorem lex_length (D : Nat) (s : String) : (Lex.lex D s).length ≤ s.length + 1
```

A mode with an open token, such as a word or a string, owes the token of that mode. The
invariant counts this token: each character gives at most one token, together with the token
that its mode owes. `begin` gives a token or a mode with an open token, never both.
-/
namespace Silicon.Source.ParsePrint

open Lex

/-! The number of tokens that the mode `m` owes: one for an open token. -/
def owed : Mode → Nat
  | .top => 0
  | .lineComment => 0
  | .skip m => owed m
  | _ => 1

theorem push_length (ts : List Token) (o : Option Token) :
    (∀ r, push ts o = .ok r → r.length ≤ ts.length + (if o.isSome then 1 else 0)) ∧
      (∀ r, push ts o = .error r → r.length ≤ ts.length + 1) := by
  cases o with
  | none => simp [push]
  | some t =>
    obtain ⟨p, k⟩ := t
    cases k <;> simp [push]

theorem nest_isSome (D d : Nat) (t : Option Token) : (nest D d t).1.isSome = t.isSome := by
  cases t with
  | none => rfl
  | some t => simp only [nest]; split <;> (try split) <;> rfl

theorem begin_owed (p : Pos) (c : Char) (cs : List Char) :
    (if (begin p c cs).2.isSome then 1 else 0) + owed (begin p c cs).1 ≤ 1 := by
  dsimp only [begin, begin.short]
  repeat' split
  all_goals simp_all [owed]

theorem start_length (D d : Nat) (p : Pos) (c : Char) (cs : List Char)
    (ih : ∀ (d : Nat) (m : Mode) (p : Pos) (ts : List Token),
      (run D d m p ts cs).length ≤ ts.length + owed m + cs.length + 1)
    (ts : List Token) (first : Option Token) :
    (match push ts first with
      | .error tokens => tokens
      | .ok tokens =>
        match push tokens (nest D d (begin p c cs).snd).fst with
        | .error tokens => tokens
        | .ok tokens =>
          run D (nest D d (begin p c cs).snd).snd (begin p c cs).fst (advance p c) tokens cs).length
      ≤ ts.length + (if first.isSome then 1 else 0) + cs.length + 2 := by
  obtain ⟨h1ok, h1err⟩ := push_length ts first
  have hb := begin_owed p c cs
  have hn := nest_isSome D d (begin p c cs).2
  split
  · rename_i r hr; have := h1err r hr; omega
  · rename_i r hr
    have h1 := h1ok r hr
    obtain ⟨h2ok, h2err⟩ := push_length r (nest D d (begin p c cs).2).1
    rw [hn] at h2ok
    split
    · rename_i r2 hr2; have := h2err r2 hr2; omega
    · rename_i r2 hr2
      have h2 := h2ok r2 hr2
      have := ih (nest D d (begin p c cs).2).2 (begin p c cs).1 (advance p c) r2
      generalize (if (begin p c cs).snd.isSome = true then 1 else 0) = x at hb h2
      omega

theorem run_length (D : Nat) (cs : List Char) : ∀ (d : Nat) (m : Mode) (p : Pos)
    (ts : List Token), (run D d m p ts cs).length ≤ ts.length + owed m + cs.length + 1 := by
  induction cs with
  | nil =>
    intro d m p ts
    simp only [run]
    split
    · rename_i r hr
      have := (push_length _ _).1 r hr
      cases m <;> simp_all [owed] <;> omega
    · rename_i r hr
      have := (push_length _ _).2 r hr
      cases m <;> simp_all [owed] <;> omega
  | cons c cs ih =>
    intro d m p ts
    have hs := start_length D d p c cs ih
    cases m with
    | top =>
      have := hs ts none
      simp only [run, List.length_cons, owed]; simp at this; omega
    | skip next =>
      have := ih d next (advance p c) ts
      simp only [run, List.length_cons, owed]; omega
    | word s acc =>
      simp only [run]
      split
      · have := ih d (.word s (c :: acc)) (advance p c) ts
        simp only [List.length_cons, owed] at this ⊢; omega
      · have := hs ts (some (wordToken s acc)); simp only [List.length_cons, owed]; simp at this
        omega
    | number s r acc =>
      simp only [run]
      split
      · have := ih d (.number s r (c :: acc)) (advance p c) ts
        simp only [List.length_cons, owed] at this ⊢; omega
      · have := hs ts (some (numberToken s r acc)); simp only [List.length_cons, owed]
        simp at this; omega
    | string s acc e =>
      cases e with
      | true =>
        simp only [run]
        split
        · rename_i x _
          have := ih d (.string s (x :: acc) false) (advance p c) ts
          simp only [List.length_cons, owed] at this ⊢; omega
        · simp [owed]; omega
      | false =>
        simp only [run]
        split
        · have := ih d .top (advance p c) (⟨s, .string (String.ofList acc.reverse)⟩ :: ts)
          simp only [List.length_cons, owed] at this ⊢; omega
        · split
          · have := ih d (.string s acc true) (advance p c) ts
            simp only [List.length_cons, owed] at this ⊢; omega
          · split
            · simp [owed]; omega
            · have := ih d (.string s (c :: acc) false) (advance p c) ts
              simp only [List.length_cons, owed] at this ⊢; omega
    | lineComment =>
      have := ih d (if (c == '\n') = true then .top else .lineComment) (advance p c) ts
      have h0 : owed (if (c == '\n') = true then .top else .lineComment) = 0 := by
        split <;> rfl
      simp only [run, List.length_cons, owed, h0] at this ⊢; omega
    | blockComment s star =>
      simp only [run]
      split
      · have := ih d .top (advance p c) ts
        simp only [List.length_cons, owed] at this ⊢; omega
      · have := ih d (.blockComment s (c == '*')) (advance p c) ts
        simp only [List.length_cons, owed] at this ⊢; omega

/-! The lexer gives at most one token for each character, and then `eof`. -/
theorem lex_length (D : Nat) (s : String) : (lex D s).length ≤ s.length + 1 := by
  have := run_length D s.toList 0 .top ⟨1, 1⟩ []
  simp only [List.length_nil, owed, String.length_toList] at this
  simp only [lex, List.length_reverse]
  omega

end Silicon.Source.ParsePrint
