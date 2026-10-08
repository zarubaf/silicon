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
  | .error e => e.code == .E001 && e.pos == ⟨1, 26⟩
  | .ok _ => false
#guard match parse "(design m" with
  | .error e => e.code == .E001 && e.pos == ⟨1, 10⟩
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

def zeroPos : Pos := ⟨0, 0⟩
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

/-! Size limits belong to the checker. The parser retains all decimal natural numbers. -/
#guard readsExpr "(const 18446744073709551616 0)"
  (.const zeroPos 18446744073709551616 0)
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
    | [.module m] => m.body == expectedStatements && print d == statements
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
      print (canonicalize d) == externSource
    | _ => false
  | .error _ => false

/-! A comment can contain tokens. Names allow ASCII letters and the stated suffixes. -/
#guard match parse "; ) (ignored\n(design _; comment\n(module _)) ; trailing )" with
  | .ok d => d.top == "_" && match d.items with
    | [.module m] => m.pos == ⟨3, 1⟩
    | _ => false
  | .error _ => false
#guard (["_", "A", "z", "_0$", "Az09_$", "add0", "Add"].all fun n =>
  (parse ("(design " ++ n ++ " (module " ++ n ++ "))")).isOk)
#guard readsExpr "U_0.q$" (.port zeroPos "U_0" "q$")
#guard (["0a", "$a", "a-b", "a.b", "é", "aé", "add", "sync", "eq"].all fun n =>
  match parse ("(design " ++ n ++ ")") with
  | .error e => e.code == .E001 && e.pos == ⟨1, 9⟩
  | .ok _ => false)

/-! Grammar errors name the first bad token, even if a later closing token is absent. -/
def rejectsAt (source : String) (pos : Pos) : Bool :=
  match parse source with
  | .error e => e.code == .E001 && e.pos == pos
  | .ok _ => false

#guard rejectsAt "(design m (module m (assign q U_0.$q)))" ⟨1, 31⟩
#guard rejectsAt "(design m (module m (let add (bits 1) (const 1 0))" ⟨1, 26⟩
#guard rejectsAt "(design m) extra" ⟨1, 12⟩
#guard rejectsAt "(design m))" ⟨1, 11⟩
#guard rejectsAt "(design m) (design n)" ⟨1, 12⟩
#guard rejectsAt "(design m\n; no close\n" ⟨3, 1⟩
#guard rejectsAt "" ⟨1, 1⟩
#guard rejectsAt "(design m (module m (assign q (add a))))" ⟨1, 37⟩
#guard rejectsAt "(design m (module m (assign q (not a b))))" ⟨1, 38⟩
#guard rejectsAt "(design m (module m (assign q (icmp bad a b))))" ⟨1, 37⟩
#guard rejectsAt "(design m (module m (assign q (const 1 -1))))" ⟨1, 40⟩
#guard rejectsAt "(design m (module m (assign q u.q.r)))" ⟨1, 31⟩
#guard rejectsAt "(design m (module m (inst u child (d a b))))" ⟨1, 40⟩
#guard rejectsAt "(design m (extern e (deps q a)))" ⟨1, 29⟩
#guard rejectsAt "(design m (module m (let a clock b)))" ⟨1, 28⟩
#guard rejectsAt "(design m (module m (assign q a) (input a (bits 1))))" ⟨1, 35⟩

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
  | .ok d => print d == unsortedSource && print (canonicalize d) == sortedSource &&
    canonicalize (canonicalize d) == canonicalize d
  | .error _ => false
#guard match parse unsortedSource, parse sortedSource with
  | .ok a, .ok b => print (canonicalize a) == print (canonicalize b)
  | _, _ => false

end Silicon.Core.Test
