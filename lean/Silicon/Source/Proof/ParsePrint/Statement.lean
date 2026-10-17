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
  .module p (nm "Counter") [⟨p, .comptime, nm "W", t "Nat"⟩] (some [nm "clk"])
    [.output p (nm "q") (.index p (t "UInt") [v "W"]),
     .connect p (.field p (v "u") (nm "d")) (.str p "a\n\"b\""),
     .expr p (.cond p (v "en") (.num p 1) (.num p 0))]

private def helper : Item :=
  .fn p false (nm "g") [⟨p, .comptime, nm "n", t "Nat"⟩] (t "Nat")
    [.local p true (nm "y") none (v "n"), .assign p (v "y") (.unary p .neg (v "y")),
     .ctIf p (v "b") [] (some []), .ret p (some (v "y"))]

example : Printable [counter, helper] := by decide +kernel

/-! A keyword name, an empty index, and a target that is not a place. -/
example : ¬ Printable [.const p (nm "in") (t "T") (.num p 0)] := by decide
example : ¬ Printable [.const p (nm "X") (t "T") (.index p (v "a") [])] := by decide
example : ¬ Printable [.fn p false (nm "f") [] (t "T") [.assign p (.num p 0) (v "x")]] := by
  decide

/-! A place with an index, a field, or a selector. -/
example : Printable [.fn p false (nm "f") [] (t "T")
    [.assign p (.field p (.index p (v "a") [.num p 0]) (nm "b")) (v "x")]] := by
  decide +kernel
example : Printable [.fn p false (nm "f") [] (t "T")
    [.assign p (.select p (v "a") p 0) (v "x")]] := by decide +kernel

/-! The unit value, tuples of one and two elements, arrays, and a selector of a call. -/
example : Printable [.const p (nm "X") (t "T")
    (.tuple p [.unit p, .tuple p [v "a"], .array p [], .array p [.num p 1, v "b"],
      .select p (.call p (v "g") []) p 1])] := by decide +kernel

/-! An empty tuple: the printer writes it as `()`, the unit value. -/
example : ¬ Printable [.const p (nm "X") (t "T") (.tuple p [])] := by decide

/-! The unit type, tuple types of one and two elements, and array types. -/
example : Printable [.const p (nm "X")
    (.tuple p [.unit p, .tuple p [t "T"], .array p (.tuple p [t "T", t "U"]) (.num p 4),
      .index p (.array p (t "T") (v "N")) [.num p 0]]) (v "x")] := by decide +kernel

/-! An empty tuple type: the printer writes it as `()`, the unit type. -/
example : ¬ Printable [.const p (nm "X") (.tuple p []) (v "x")] := by decide

/-! A struct with parameters and fields, a struct without them, and a `type` item and statement. -/
example : Printable [.struct p (nm "P") [⟨p, .comptime, nm "W", t "Nat"⟩]
    [⟨nm "a", .index p (t "UInt") [v "W"]⟩, ⟨nm "b", t "Bool"⟩], .struct p (nm "E") [] [],
    .alias p (nm "T") (t "U"), .fn p false (nm "f") [] (t "T") [.alias p (nm "L") (t "T")]] := by
  decide +kernel

/-! A struct parameter without `comptime`, and a keyword as a field name. -/
example : ¬ Printable [.struct p (nm "P") [⟨p, .none, nm "W", t "Nat"⟩] []] := by decide
example : ¬ Printable [.struct p (nm "P") [] [⟨nm "in", t "T"⟩]] := by decide

/-! Array types in expressions: in an array, as the base of an index, and in a type argument. -/
example : Printable [.const p (nm "X") (t "Type")
    (.array p [.arrayType p (.array p (t "Bool") (.num p 2)) (v "N"),
      .index p (.arrayType p (t "T") (.num p 1)) [.num p 0],
      .call p (v "f") [.arrayType p (.index p (t "UInt") [.arrayType p (t "U") (v "M")])
        (.num p 3)]])] := by decide +kernel

/-! An array type in an expression with an empty tuple type as its element. -/
example : ¬ Printable [.const p (nm "X") (t "Type") (.arrayType p (.tuple p []) (.num p 4))] := by
  decide

/-! A module parameter without `comptime`, and two domains. -/
example : ¬ Printable [.module p (nm "M") [⟨p, .none, nm "W", t "Nat"⟩] none []] := by decide
example : ¬ Printable [.module p (nm "M") [] (some [nm "a", nm "b"]) []] := by decide

/-! A resource in a `fn` without `comptime`, but not in a `comptime fn`. -/
example : ¬ Printable [.fn p false (nm "f") [] (t "T") [.wire p (nm "w") (t "T")]] := by decide
example : Printable [.fn p true (nm "f") [] (t "T") [.wire p (nm "w") (t "T")]] := by decide

/-! A `mut` parameter of a function, but not of a module or a struct. -/
example : Printable [.fn p false (nm "f") [⟨p, .mut, nm "x", t "T"⟩, ⟨p, .none, nm "y", t "T"⟩]
    (t "T") []] := by decide +kernel
example : ¬ Printable [.module p (nm "M") [⟨p, .mut, nm "W", t "Nat"⟩] none []] := by decide
example : ¬ Printable [.struct p (nm "P") [⟨p, .mut, nm "W", t "Nat"⟩] []] := by decide

/-!
Receiver calls: on a name, a field, a sum, and a call result, then an index and a call of the
result.
-/
example : Printable [.const p (nm "X") (t "T")
    (.tuple p [.method p (v "a") (nm "m") [], .method p (.field p (v "a") (nm "b")) (nm "m")
      [v "x", .num p 1], .method p (.binary p .add (v "a") (v "b")) (nm "m") [],
      .index p (.method p (.method p (v "a") (nm "m") [v "x"]) (nm "n") []) [.num p 0],
      .call p (.method p (v "a") (nm "m") []) [v "y"]])] := by decide +kernel
example : Printable [.fn p false (nm "f") [] (t "T")
    [.expr p (.method p (v "xs") (nm "push") [v "x"])]] := by decide +kernel

/-! A keyword as a method name, and a receiver call as an assignment target. -/
example : ¬ Printable [.const p (nm "X") (t "T") (.method p (v "a") (nm "in") [])] := by decide
example : ¬ Printable [.fn p false (nm "f") [] (t "T")
    [.assign p (.method p (v "a") (nm "m") []) (v "x")]] := by decide

/-! An enum with and without payload types, a variant path, and a constructor call. -/
example : Printable [.enum p (nm "Op") (t "T")
    [⟨nm "A", [], .num p 0⟩, ⟨nm "B", [t "U", .tuple p [t "V"]], .num p 1⟩],
    .enum p (nm "E") (t "T") [],
    .const p (nm "X") (t "Op") (.call p (.path p (nm "Op") (nm "B")) [.path p (nm "E") (nm "C")])]
    := by decide +kernel

/-! A keyword in a variant path, and an empty tuple type as a payload type. -/
example : ¬ Printable [.const p (nm "X") (t "T") (.path p (nm "in") (nm "A"))] := by decide
example : ¬ Printable [.enum p (nm "E") (t "T") [⟨nm "A", [.tuple p []], .num p 0⟩]] := by
  decide

/-! A control character in a string, and a number that is too large. -/
example : ¬ Printable [.const p (nm "X") (t "T") (.str p "\x01")] := by decide
example : ¬ Printable [.const p (nm "X") (t "T") (.num p (2 ^ 65536))] := by decide +kernel

end Silicon.Source.ParsePrint
