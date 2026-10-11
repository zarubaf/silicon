-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Proof.ParsePrint.Count
import Silicon.Source.Proof.ParsePrint.Statement
import Silicon.Source.Proof.ParsePrint.Parse.Item

/-!
The theorem `parse_print` of section 10.3 of the front-end spec. The parser reads the printed
text of a printable AST back to the same AST, up to positions.

The proof has three parts. `lex_print` gives the kinds of the tokens of the printed text.
`Input.win_print` gives the results of the bracket pass on these tokens. `Runs.items` reads
the tokens back to the items. `lex_length` bounds the number of tokens by the length of the
text, and thus by the syntax depth `N`. Thus each height is at most `N`, and the fuel of
`parse` is sufficient.
-/
namespace Silicon.Source.ParsePrint

open Lex Parse

/-! The parser reads the printed text of printable items back to them, up to positions. -/
theorem parse_print_erase (items : List Item) (hp : Printable items) (N : Nat)
    (hN : (Print.print items).length ≤ N) :
    ∃ items', Parse.parseSource N (Print.print items) = .ok items' ∧
      items'.map Item.erase = items.map Item.erase := by
  have hk := lex_print items hp N hN
  have hlen := lex_length N (Print.print items)
  have h2 := congrArg List.length hk
  simp only [List.length_map, List.length_append, List.length_singleton] at h2
  have hw := Input.win_print items hp N hN
  let ctx : Ctx := ⟨Input.of (Lex.lex N (Print.print items)).toArray, N, false⟩
  have hr := Runs.items items ctx 0
    (32 * ((Lex.lex N (Print.print items)).toArray.size + 1)) [] [] rfl hp hw
    (by simp only [List.size_toArray]; omega) (by show _ ≤ N; omega) none
  obtain ⟨r, hrun, ms, hr, hms⟩ := hr
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  refine ⟨r, ?_, hms⟩
  unfold Parse.parseSource Parse.parse
  simp [ctx] at hrun
  simp [hrun]
  rfl

/-! The proposition `Statement` holds. -/
theorem statement : Statement :=
  Statement.of_erased fun items he hp N hN => by
    obtain ⟨items', h, he'⟩ := parse_print_erase items hp N hN
    exact ⟨items', h, he'.trans he⟩

/-!
The theorem `parse_print`. Let the syntax depth `N` be at least the length of the printed text.
Then the parser gives printable items back, up to positions.
-/
theorem parse_print (items : List Item) (h : Printable items)
    (N : Nat) (hN : (Print.print items).length ≤ N) :
    ∃ items', Parse.parseSource N (Print.print items) = .ok items' ∧
      items'.map Item.erase = items.map Item.erase :=
  statement items h N hN

end Silicon.Source.ParsePrint
