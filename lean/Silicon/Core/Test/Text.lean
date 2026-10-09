import Silicon.Core.Text

/-!
These tests check the text format at its public boundary.
-/

namespace Silicon.Core.Test

/-! The counter uses a clock, a reset, and a conditional update. -/
def counter : String := "(design counter\n" ++
  "  (module counter\n" ++
  "    (input clk clock)\n" ++
  "    (input rst (bits 1))\n" ++
  "    (input en (bits 1))\n" ++
  "    (output q (bits 8))\n" ++
  "    (reg r (bits 8) clk (reset sync rst (const 8 0)))\n" ++
  "    (let inc (bits 8) (add r (const 8 1)))\n" ++
  "    (next r (mux en inc r))\n" ++
  "    (assign q r)))"

#guard (parse counter).isOk
#guard match parse counter with
  | .ok d => match parse (print d) with
    | .ok d' => d'.erasePos == d.erasePos
    | .error _ => false
  | .error _ => false

/-! Keywords cannot name values. A missing closing token points to the end. -/
#guard match parse "(design m (module m (let add (bits 1) (const 1 0))))" with
  | .error e => e.code == .E001 && e.pos == ⟨1, 26, []⟩
  | .ok _ => false
#guard match parse "(design m" with
  | .error e => e.code == .E001 && e.pos == ⟨1, 10, []⟩
  | .ok _ => false

/-! These checks compare syntax trees, so an operation cannot silently change its meaning. -/
def readsExpr (source : String) (expected : Expr) : Bool :=
  match parse ("(design m (module m (assign q " ++ source ++ ")))") with
  | .ok d => match d.erasePos.items with
    | [.module { body := [.assign _ "q" value], .. }] => value == expected &&
        match parse (print d) with
        | .ok d' => d'.erasePos == d.erasePos
        | .error _ => false
    | _ => false
  | .error _ => false

def zeroPos : Pos := ⟨0, 0, []⟩
def lhs : Expr := .ref zeroPos "a"
def rhs : Expr := .ref zeroPos "b"

#guard readsExpr "a" lhs
#guard readsExpr "u.q" (.port zeroPos "u" "q")
#guard readsExpr "(const 1000 18446744073709551616)"
  (.const zeroPos 1000 18446744073709551616)
#guard readsExpr "(not a)" (.un zeroPos .not lhs)
#guard ([ ("add", BinOp.add), ("sub", .sub), ("mul", .mul), ("and", .and),
          ("or", .or), ("xor", .xor), ("shl", .shl), ("shru", .shru),
          ("shrs", .shrs), ("concat", .concat) ].all fun (word, op) =>
  readsExpr ("(" ++ word ++ " a b)") (.bin zeroPos op lhs rhs))
#guard ([ ("eq", Pred.eq), ("ne", .ne), ("ult", .ult), ("ule", .ule),
          ("ugt", .ugt), ("uge", .uge), ("slt", .slt), ("sle", .sle),
          ("sgt", .sgt), ("sge", .sge) ].all fun (word, pred) =>
  readsExpr ("(icmp " ++ word ++ " a b)") (.icmp zeroPos pred lhs rhs))
#guard readsExpr "(mux a b (const 1 0))"
  (.mux zeroPos lhs rhs (.const zeroPos 1 0))
#guard readsExpr "(extract a 3 5)" (.extract zeroPos lhs 3 5)
#guard readsExpr "(replicate a 7)" (.replicate zeroPos lhs 7)
#guard readsExpr "(read ram (add a b))"
  (.read zeroPos "ram" (.bin zeroPos .add lhs rhs))

/-! Constant values have no limit. Other numbers have a 32-bit syntax limit. -/
#guard readsExpr "(const 4294967295 0)" (.const zeroPos 4294967295 0)
#guard readsExpr "(const 0 9)" (.const zeroPos 0 9)
#guard readsExpr "(replicate a 0)" (.replicate zeroPos lhs 0)
#guard readsExpr "(extract a 0 0)" (.extract zeroPos lhs 0 0)
#guard (parse ("(design m (module m (input a (bits 0)) " ++
  "(let x (bits 0) a) (reg r (bits 0) clk) (mem ram (bits 0) 0 clk)))")).isOk

/-! All statement forms retain their fields, including optional reset and instance inputs. -/
def statements : String := "(design m (module m " ++
  "(reg r (bits 8) clk) " ++
  "(reg s (bits 8) clk (reset sync rst (const 8 0))) " ++
  "(mem ram (bits 8) 13 clk) " ++
  "(inst u child (clk clk) (d a)) " ++
  "(let v (bits 8) (read ram a)) " ++
  "(next r v) (write ram 12 a v en) (assign q u.q)))"

def expectedStatements : List Stmt :=
  [.reg zeroPos "r" 8 "clk" none,
   .reg zeroPos "s" 8 "clk"
     (some ⟨.sync, .ref zeroPos "rst", .const zeroPos 8 0⟩),
   .mem zeroPos "ram" 8 13 "clk",
   .inst zeroPos "u" "child" [("clk", .ref zeroPos "clk"), ("d", lhs)],
   .let_ zeroPos "v" 8 (.read zeroPos "ram" lhs),
   .next zeroPos "r" (.ref zeroPos "v"),
   .write zeroPos "ram" 12 lhs (.ref zeroPos "v") (.ref zeroPos "en"),
   .assign zeroPos "q" (.port zeroPos "u" "q")]

#guard match parse statements with
  | .ok d => match d.erasePos.items with
    | [.module m] => m.body == expectedStatements
    | _ => false
  | .error _ => false

/-! Extern dependencies can be empty. Their order and port order are part of the text. -/
def externSource : String := "(design m (extern blackbox " ++
  "(input z clock) (output q (bits 8)) (input a (bits 8)) (output p (bits 8)) " ++
  "(deps q (a z)) (deps p ())))"

#guard match parse externSource with
  | .ok d => match d.erasePos.items with
    | [.extern e] =>
      e.ports == [⟨zeroPos, .input, "z", .clock⟩, ⟨zeroPos, .output, "q", .bits 8⟩,
        ⟨zeroPos, .input, "a", .bits 8⟩, ⟨zeroPos, .output, "p", .bits 8⟩] &&
      e.deps == [⟨zeroPos, "q", ["a", "z"]⟩, ⟨zeroPos, "p", []⟩] &&
      canonicalize d == d
    | _ => false
  | .error _ => false

/-! A comment can contain tokens. Names allow ASCII letters and the stated suffixes. -/
#guard match parse "; ) (ignored\n(design _; comment\n(module _)) ; trailing )" with
  | .ok d => d.top == "_" && match d.items with
    | [.module m] => m.pos.line == 3 && m.pos.col == 1
    | _ => false
  | .error _ => false
#guard (["_", "A", "z", "_0$", "Az09_$", "add0", "Add"].all fun n =>
  (parse ("(design " ++ n ++ " (module " ++ n ++ "))")).isOk)
#guard readsExpr "U_0.q$" (.port zeroPos "U_0" "q$")
#guard (["0a", "$a", "a.b", "é", "add", "sync", "eq"].all fun n =>
  match parse ("(design " ++ n ++ ")") with
  | .error e => e.code == .E001 && e.pos == ⟨1, 9, []⟩
  | .ok _ => false)

/-! Grammar errors name the first bad token, even if a later closing token is absent. -/
def rejectsAt (source : String) (pos : Pos) : Bool :=
  match parse source with
  | .error e => e.code == .E001 && e.pos == pos
  | .ok _ => false

#guard rejectsAt "(design m (module m (assign q U_0.$q)))" ⟨1, 31, []⟩
#guard rejectsAt "(design m (module m (let add (bits 1) (const 1 0))" ⟨1, 26, []⟩
#guard rejectsAt "(design m) extra" ⟨1, 12, []⟩
#guard rejectsAt "(design m))" ⟨1, 11, []⟩
#guard rejectsAt "(design m) (design n)" ⟨1, 12, []⟩
#guard rejectsAt "(design m\n; no close\n" ⟨3, 1, []⟩
#guard rejectsAt "" ⟨1, 1, []⟩
#guard rejectsAt "(design m (module m (assign q (add a))))" ⟨1, 37, []⟩
#guard rejectsAt "(design m (module m (assign q (not a b))))" ⟨1, 38, []⟩
#guard rejectsAt "(design m (module m (assign q (icmp bad a b))))" ⟨1, 37, []⟩
#guard rejectsAt "(design m (module m (assign q (const 1 -1))))" ⟨1, 40, []⟩
#guard rejectsAt "(design m (module m (assign q u.q.r)))" ⟨1, 31, []⟩
#guard rejectsAt "(design m (module m (inst u child (d a b))))" ⟨1, 40, []⟩
#guard rejectsAt "(design m (extern e (deps q a)))" ⟨1, 29, []⟩
#guard rejectsAt "(design m (module m (let a clock b)))" ⟨1, 28, []⟩
#guard rejectsAt "(design m (module m (assign q a) (input a (bits 1))))" ⟨1, 35, []⟩

/-! Canonical form sorts all kinds, names, and numeric write indices across items. -/
def unsortedSource : String := "(design z (module z " ++
  "(output zq (bits 8)) (input ac clock) " ++
  "(assign zq r) (write ram 10 a b en) (next r v) (let z (bits 8) a) " ++
  "(inst u child (z a) (a b)) (mem ram (bits 8) 4 ac) " ++
  "(reg z (bits 8) ac) (let a (bits 8) b) (reg a (bits 8) ac) " ++
  "(write ram 2 a b en)) (extern a (output q (bits 1)) (deps q ())) (module b))"

def sortedSource : String := "(design z " ++
  "(extern a (output q (bits 1)) (deps q ())) (module b) (module z " ++
  "(output zq (bits 8)) (input ac clock) " ++
  "(reg a (bits 8) ac) (reg z (bits 8) ac) (mem ram (bits 8) 4 ac) " ++
  "(inst u child (z a) (a b)) (let a (bits 8) b) (let z (bits 8) a) " ++
  "(next r v) (write ram 2 a b en) (write ram 10 a b en) (assign zq r)))"

#guard match parse unsortedSource with
  | .ok d =>
    canonicalize (canonicalize d) == canonicalize d
  | .error _ => false
#guard match parse unsortedSource, parse sortedSource with
  | .ok a, .ok b => print (canonicalize a) == print (canonicalize b)
  | _, _ => false

/-! The counter fixes indentation, parentheses, and the final LF byte for byte. -/
#guard (parse counter).toOption.map print == some (counter ++ "\n")
#guard (parse "(design m)").toOption.map print == some "(design m)\n"
#guard (parse "(design m (module m) (extern e (deps q ())))").toOption.map print ==
  some "(design m\n  (module m)\n  (extern e\n    (deps q ())))\n"

#guard rejectsAt "(design m (module m (assign q (const 4294967296 0))))" ⟨1, 38, []⟩
#guard rejectsAt "(design m (module m (input a (bits 4294967296))))" ⟨1, 36, []⟩
#guard rejectsAt "(design m (module m (mem ram (bits 8) 4294967296 clk)))" ⟨1, 39, []⟩
#guard rejectsAt "(design m (module m (write ram 4294967296 a b en)))" ⟨1, 32, []⟩
#guard rejectsAt "(design m (module m (assign q (extract a 4294967296 1))))" ⟨1, 42, []⟩
#guard rejectsAt "(design m (module m (assign q (extract a 0 4294967296))))" ⟨1, 44, []⟩
#guard rejectsAt "(design m (module m (assign q (replicate a 4294967296))))" ⟨1, 44, []⟩

/-! Only compound expressions count toward the nesting limit. -/
def nestedNot (depth : Nat) : String :=
  String.join (List.replicate depth "(not ") ++ "a" ++
    String.join (List.replicate depth ")")

def assigned (expr : String) : String := "(design m (module m (assign q " ++ expr ++ ")))"

set_option maxRecDepth 4096 in
#guard (parse (assigned (nestedNot 256))).isOk
set_option maxRecDepth 4096 in
#guard rejectsAt (assigned (nestedNot 257)) ⟨1, 31 + 5 * 256, []⟩
set_option maxRecDepth 4096 in
#guard (parse ("(design m (module m (reg r (bits 1) clk (reset sync " ++
  nestedNot 256 ++ " " ++ nestedNot 256 ++ "))))")).isOk
set_option maxRecDepth 4096 in
#guard (parse ("(design m (module m (inst u child (d " ++ nestedNot 256 ++ "))))")).isOk

/-! Bad characters have their own position within a maximal token. -/
#guard rejectsAt ("(design" ++ String.singleton (Char.ofNat 12) ++ "m)") ⟨1, 8, []⟩
#guard rejectsAt "(design aé)" ⟨1, 10, []⟩
#guard rejectsAt "(design a-b)" ⟨1, 10, []⟩
#guard rejectsAt "(design 12abc)" ⟨1, 9, []⟩
#guard rejectsAt (assigned "a.1") ⟨1, 31, []⟩
#guard rejectsAt (assigned "a.") ⟨1, 31, []⟩
#guard (parse "(design\tm\r\n(module m))").isOk

/-! Port declarations determine dependency and connection order, not their names. -/
def portOrderSource : String := "(design parent " ++
  "(module parent (inst u child (a x) (z y)) " ++
  "(inst v ext (a x) (z y)) (inst w missing (a x) (z y))) " ++
  "(module child (input z (bits 1)) (input a (bits 1))) " ++
  "(extern ext (input z (bits 1)) (input a (bits 1)) " ++
  "(output q (bits 1)) (output p (bits 1)) (deps p (a z)) (deps q ())))"

def portOrderExpected : String := "(design parent " ++
  "(module child (input z (bits 1)) (input a (bits 1))) " ++
  "(extern ext (input z (bits 1)) (input a (bits 1)) " ++
  "(output q (bits 1)) (output p (bits 1)) (deps q ()) (deps p (a z))) " ++
  "(module parent (inst u child (z y) (a x)) " ++
  "(inst v ext (z y) (a x)) (inst w missing (a x) (z y))))"

#guard match parse portOrderSource, parse portOrderExpected with
  | .ok a, .ok b => (canonicalize a).erasePos == b.erasePos &&
    canonicalize (canonicalize a) == canonicalize a
  | _, _ => false

/-! The first syntax error wins across numbers, grammar, and bad characters. -/
#guard rejectsAt "(design m (module m (let x (bits 4294967296) a) (bad)))" ⟨1, 34, []⟩
#guard rejectsAt "(design m (module m (bad) (assign q aé)))" ⟨1, 22, []⟩
#guard rejectsAt "(design 12aé)" ⟨1, 12, []⟩
set_option maxRecDepth 4096 in
#guard rejectsAt ("(design m (module m (reg r (bits 1) clk (reset sync " ++
  nestedNot 257 ++ " a))))") ⟨1, 53 + 5 * 256, []⟩
set_option maxRecDepth 4096 in
#guard rejectsAt ("(design m (module m (inst u child (d " ++ nestedNot 257 ++ "))))")
  ⟨1, 38 + 5 * 256, []⟩
set_option maxRecDepth 4096 in
#guard rejectsAt (assigned (String.join (List.replicate 256 "(not ") ++
  "(const 1 0)" ++ String.join (List.replicate 256 ")"))) ⟨1, 31 + 5 * 256, []⟩

#guard (parse ("(design z (module z (output q (bits 1)) (input a (bits 1)) " ++
  "(assign q a) (let x (bits 1) a)) (module a))")).toOption.map print ==
  some ("(design z\n  (module z\n    (output q (bits 1))\n    (input a (bits 1))\n" ++
    "    (assign q a)\n    (let x (bits 1) a))\n  (module a))\n")

#guard (parse ("(design m (extern e (output q (bits 1)) (output p (bits 1)) " ++
  "(deps p ()) (deps q ())) (module m (inst u e (p a) (q b))))")).toOption.map print ==
  some ("(design m\n  (extern e\n    (output q (bits 1))\n    (output p (bits 1))\n" ++
    "    (deps p ())\n    (deps q ()))\n  (module m\n    (inst u e (p a) (q b))))\n")

/-! This concrete counter design omits source positions. -/
def counterDesign : Design := ⟨"counter", [.module ⟨zeroPos, "counter",
  [⟨zeroPos, .input, "clk", .clock⟩, ⟨zeroPos, .input, "rst", .bits 1⟩,
   ⟨zeroPos, .input, "en", .bits 1⟩, ⟨zeroPos, .output, "q", .bits 8⟩],
  [.reg zeroPos "r" 8 "clk" (some ⟨.sync, .ref zeroPos "rst", .const zeroPos 8 0⟩),
   .let_ zeroPos "inc" 8 (.bin zeroPos .add (.ref zeroPos "r") (.const zeroPos 8 1)),
   .next zeroPos "r" (.mux zeroPos (.ref zeroPos "en")
     (.ref zeroPos "inc") (.ref zeroPos "r")),
   .assign zeroPos "q" (.ref zeroPos "r")]⟩], zeroPos⟩

#guard (parse counter).toOption.map Design.erasePos == some counterDesign

example : counterDesign.ValidNames := by
  simp [Design.ValidNames, counterDesign, Item.names, Stmt.names, Reset.names, Expr.names]
  decide

#guard rejectsAt "(design m (module m (assign q (const 4294967296 nope))))" ⟨1, 38, []⟩
#guard rejectsAt "(design m (module m (assign q (extract a 4294967296 nope))))" ⟨1, 42, []⟩
#guard rejectsAt "(design m (module m (bad) (assign q (const 4294967296 0))))" ⟨1, 22, []⟩
#guard (parse ("(design m (module m (input a (bits 4294967295)) " ++
  "(mem ram (bits 4294967295) 4294967295 clk) " ++
  "(write ram 4294967295 a a a)))")).isOk

example : counterDesign.WithinLimits := by
  unfold Design.WithinLimits
  decide

end Silicon.Core.Test
