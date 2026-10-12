-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Parse
import Silicon.Source.Proof.ParsePrint.Erase

/-!
The statement of `parse_print` (section 10.3 of the front-end spec). This module states the
theorem as the proposition `Statement`. `Source.Proof.ParsePrint` proves it:

```lean
theorem parse_print (items : List Item) (h : Printable items)
    (N : Nat) (hN : (Print.print items).length ≤ N) :
    ∃ items', Parse.parseSource N (Print.print items) = .ok items' ∧
      items'.map Item.erase = items.map Item.erase
```

The syntax depth `N` is at least the length of the text. Each bracket depth and each height
is below that length, so no limit check fails.

The proof has two parts. A lexer lemma gives the tokens of the printed text. A parser lemma
reads these tokens back to the erased AST. `Statement.of_erased` reduces the theorem to an
AST without positions.
-/
namespace Silicon.Source.ParsePrint

/-! The proposition of `parse_print`. -/
def Statement : Prop :=
  ∀ (items : List Item), Printable items → ∀ (N : Nat), (Print.print items).length ≤ N →
    ∃ items', Parse.parseSource N (Print.print items) = .ok items' ∧
      items'.map Item.erase = items.map Item.erase

/-!
It is sufficient to prove `parse_print` for an AST without positions. The printer and
`Printable` ignore positions.
-/
theorem Statement.of_erased
    (h : ∀ (items : List Item), items.map Item.erase = items → Printable items →
      ∀ (N : Nat), (Print.print items).length ≤ N →
        ∃ items', Parse.parseSource N (Print.print items) = .ok items' ∧
          items'.map Item.erase = items) :
    Statement := by
  intro items hp N hN
  have he : (items.map Item.erase).map Item.erase = items.map Item.erase := by
    simp [List.map_map, Function.comp_def]
  rw [← Print.print_erase] at hN ⊢
  exact h _ he ((printable_erase items).2 hp) N hN

/-! Examples: the precondition holds for a small AST, and it fails for each kind of defect. -/

private def p : Pos := ⟨1, 1⟩
private def nm (s : String) : Ident := ⟨p, s⟩
private def v (s : String) : Expr := .name p s
private def t (s : String) : TypeExpr := .name p s

private def counter : Item :=
  .module p (nm "Counter") [⟨p, true, nm "W", t "Nat"⟩] (some [nm "clk"])
    [.output p (nm "q") (.index p (t "UInt") [v "W"]),
     .connect p (.field p (v "u") (nm "d")) (.str p "a\n\"b\""),
     .expr p (.cond p (v "en") (.num p 1) (.num p 0))]

private def helper : Item :=
  .fn p false (nm "g") [⟨p, true, nm "n", t "Nat"⟩] (t "Nat")
    [.local p true (nm "y") none (v "n"), .assign p (v "y") (.unary p .neg (v "y")),
     .ctIf p (v "b") [] (some []), .ret p (some (v "y"))]

example : Printable [counter, helper] := by decide +kernel

/-! A keyword name, an empty index, and a target that is not a place. -/
example : ¬ Printable [.const p (nm "in") (t "T") (.num p 0)] := by decide
example : ¬ Printable [.const p (nm "X") (t "T") (.index p (v "a") [])] := by decide
example : ¬ Printable [.fn p false (nm "f") [] (t "T") [.assign p (.num p 0) (v "x")]] := by
  decide

/-! A place with an index or a field, but no container form yet. -/
example : Printable [.fn p false (nm "f") [] (t "T")
    [.assign p (.field p (.index p (v "a") [.num p 0]) (nm "b")) (v "x")]] := by
  decide +kernel
example : ¬ Printable [.fn p false (nm "f") [] (t "T")
    [.assign p (.select p (v "a") p 0) (v "x")]] := by decide

/-! A module parameter without `comptime`, and two domains. -/
example : ¬ Printable [.module p (nm "M") [⟨p, false, nm "W", t "Nat"⟩] none []] := by decide
example : ¬ Printable [.module p (nm "M") [] (some [nm "a", nm "b"]) []] := by decide

/-! A resource in a `fn` without `comptime`, but not in a `comptime fn`. -/
example : ¬ Printable [.fn p false (nm "f") [] (t "T") [.wire p (nm "w") (t "T")]] := by decide
example : Printable [.fn p true (nm "f") [] (t "T") [.wire p (nm "w") (t "T")]] := by decide

/-! A control character in a string, and a number that is too large. -/
example : ¬ Printable [.const p (nm "X") (t "T") (.str p "\x01")] := by decide
example : ¬ Printable [.const p (nm "X") (t "T") (.num p (2 ^ 65536))] := by decide +kernel

end Silicon.Source.ParsePrint
