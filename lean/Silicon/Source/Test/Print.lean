-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Print

/-!
These tests fix the bytes of the AST dump, which the Rust front end must copy, and the
parentheses of the source printer.
-/

namespace Silicon.Source.Test.Print

open Silicon.Source

/-! The dump and the printer ignore positions, so one position serves each node. -/
def p : Pos := ⟨1, 1⟩
def nm (s : String) : Ident := ⟨p, s⟩
def n (v : Nat) : Expr := .num p v
def v (s : String) : Expr := .name p s
def t (s : String) : TypeExpr := .name p s
def bin (op : BinOp) (l r : Expr) : Expr := .binary p op l r
def u8 : TypeExpr := .index p (t "UInt") [n 8]

def exprDump (e : Expr) : String := e.dump
def stmtDump (s : Stmt) : String := s.dump
def exprText (e : Expr) : String := e.print 0

/-! Each expression kind. -/
#guard exprDump (n 42) == "(num 42)"
#guard exprDump (.bool p true) == "(bool true)"
#guard exprDump (.bool p false) == "(bool false)"
#guard exprDump (.str p "hi") == "(str \"hi\")"
#guard exprDump (v "x") == "(name \"x\")"
#guard exprDump (.unary p .neg (v "x")) == "(unary neg (name \"x\"))"
#guard exprDump (bin .addw (v "a") (n 1)) == "(binary addw (name \"a\") (num 1))"
#guard exprDump (.cond p (v "c") (n 1) (n 0)) == "(cond (name \"c\") (num 1) (num 0))"
#guard exprDump (.call p (v "f") []) == "(call (name \"f\") ())"
#guard exprDump (.call p (v "f") [n 1, n 2]) == "(call (name \"f\") ((num 1) (num 2)))"
#guard exprDump (.index p (v "UInt") [n 8]) == "(index (name \"UInt\") ((num 8)))"
#guard exprDump (.field p (v "x") (nm "0")) == "(field (name \"x\") \"0\")"


/-! Each container form of slice 2. A `select` prints its selector in decimal. -/
#guard exprDump (.unit p) == "(unit)"
#guard exprDump (.tuple p [n 1]) == "(tuple ((num 1)))"
#guard exprDump (.tuple p [n 1, v "x"]) == "(tuple ((num 1) (name \"x\")))"
#guard exprDump (.array p []) == "(array ())"
#guard exprDump (.array p [n 1, n 2]) == "(array ((num 1) (num 2)))"
#guard exprDump (.select p (v "t") p 16) == "(select (name \"t\") 16)"

/-! Each type kind. -/
#guard u8.dump == "(index (name \"UInt\") ((num 8)))"
#guard (t "Bool").dump == "(name \"Bool\")"
#guard (TypeExpr.unit p).dump == "(unit)"
#guard (TypeExpr.tuple p [u8]).dump == "(tuple ((index (name \"UInt\") ((num 8)))))"
#guard (TypeExpr.tuple p [t "Bool", .unit p]).dump == "(tuple ((name \"Bool\") (unit)))"
#guard (TypeExpr.array p (t "Bool") (v "N")).dump == "(array (name \"Bool\") (name \"N\"))"
#guard (TypeExpr.array p (.array p u8 (n 2)) (n 3)).dump ==
  "(array (array (index (name \"UInt\") ((num 8))) (num 2)) (num 3))"

/-! The escapes of the grammar, and a non-ASCII character as itself. -/
#guard exprDump (.str p "a\"b\\c\nd\re\tf") == "(str \"a\\\"b\\\\c\\nd\\re\\tf\")"
#guard exprDump (.str p "µ") == "(str \"µ\")"

/-! Each statement kind, with both forms of each `Option`. -/
#guard stmtDump (.local p true (nm "x") (some u8) (n 1)) ==
  "(local true \"x\" (some (index (name \"UInt\") ((num 8)))) (num 1))"
#guard stmtDump (.local p false (nm "x") none (n 1)) == "(local false \"x\" none (num 1))"
#guard stmtDump (.assign p (v "x") (n 1)) == "(assign (name \"x\") (num 1))"
#guard stmtDump (.connect p (v "o") (v "x")) == "(connect (name \"o\") (name \"x\"))"
#guard stmtDump (.reg p (nm "r") (t "Bool") (.bool p false)) ==
  "(reg \"r\" (name \"Bool\") (bool false))"
#guard stmtDump (.wire p (nm "w") (t "Bool")) == "(wire \"w\" (name \"Bool\"))"
#guard stmtDump (.input p (nm "i") (t "Bool")) == "(input \"i\" (name \"Bool\"))"
#guard stmtDump (.output p (nm "o") (t "Bool")) == "(output \"o\" (name \"Bool\"))"
#guard stmtDump (.inst p (nm "u") (nm "M") [n 8]) == "(inst \"u\" \"M\" ((num 8)))"
#guard stmtDump (.ret p none) == "(ret none)"
#guard stmtDump (.ret p (some (n 1))) == "(ret (some (num 1)))"
#guard stmtDump (.ctIf p (v "c") [] none) == "(ctif (name \"c\") () none)"
#guard stmtDump (.ctIf p (v "c") [.ret p none] (some [])) ==
  "(ctif (name \"c\") ((ret none)) (some ()))"
#guard stmtDump (.ctFor p (nm "i") (n 0) (n 4) []) == "(ctfor \"i\" (num 0) (num 4) ())"
#guard stmtDump (.block p [.ret p none, .ret p none]) == "(block ((ret none) (ret none)))"
#guard stmtDump (.expr p (v "x")) == "(expr (name \"x\"))"

/-! Each item kind and the parameter structure. -/
def counter : Item :=
  .module p (nm "Counter") [⟨p, true, nm "W", t "Nat"⟩] (some [nm "clk"])
    [.output p (nm "q") (.index p (t "UInt") [v "W"])]

def inc : Item :=
  .fn p false (nm "inc") [⟨p, false, nm "x", u8⟩] u8 [.ret p (some (bin .addw (v "x") (n 1)))]

#guard (Item.const p (nm "N") (t "Nat") (n 3)).dump == "(const \"N\" (name \"Nat\") (num 3))"
#guard inc.dump ==
  "(fn false \"inc\" ((param false \"x\" (index (name \"UInt\") ((num 8))))) " ++
  "(index (name \"UInt\") ((num 8))) ((ret (some (binary addw (name \"x\") (num 1))))))"
#guard counter.dump ==
  "(module \"Counter\" ((param true \"W\" (name \"Nat\"))) (some (\"clk\")) " ++
  "((output \"q\" (index (name \"UInt\") ((name \"W\"))))))"

/-! One line for each item, each line ends with LF, and no items give an empty dump. -/
#guard Print.dump [] == ""
#guard Print.dump [.const p (nm "N") (t "Nat") (n 3)] == "(const \"N\" (name \"Nat\") (num 3))\n"
#guard (Print.dump [inc, counter]).splitOn "\n" == [inc.dump, counter.dump, ""]

/-!
A deep chain and a long block dump correctly. This test guards the linear dump against a
regression at these sizes. A quadratic dump also passes it at these sizes.
-/
def chain : Expr := (List.range 4096).foldl (fun e _ => bin .add e (n 1)) (n 0)

def long : Item := .fn p false (nm "f") [] (t "Unit") (List.replicate 100000 (.expr p (n 0)))

#guard chain.dump.length == "(num 0)".length + 4096 * "(binary add  (num 1))".length
#guard (Print.dump [long]).length ==
  "(fn false \"f\" () (name \"Unit\") ())\n".length + 100000 * "(expr (num 0)) ".length - 1

/-! The printer adds parentheses only where the precedence needs them. -/
#guard exprText (bin .add (v "a") (bin .mul (v "b") (v "c"))) == "a + b * c"
#guard exprText (bin .mul (bin .add (v "a") (v "b")) (v "c")) == "(a + b) * c"
#guard exprText (bin .sub (bin .sub (v "a") (v "b")) (v "c")) == "a - b - c"
#guard exprText (bin .sub (v "a") (bin .sub (v "b") (v "c"))) == "a - (b - c)"
#guard exprText (bin .lor (bin .land (v "a") (v "b")) (v "c")) == "a && b || c"
#guard exprText (bin .land (v "a") (bin .lor (v "b") (v "c"))) == "a && (b || c)"
#guard exprText (bin .lt (bin .lt (v "a") (v "b")) (v "c")) == "(a < b) < c"
#guard exprText (bin .eq (v "a") (bin .shl (v "b") (n 1))) == "a == b << 1"
#guard exprText (bin .and (bin .eq (v "a") (v "b")) (v "c")) == "a == b & c"
#guard exprText (bin .eq (bin .and (v "a") (v "b")) (v "c")) == "(a & b) == c"
#guard exprText (.unary p .neg (.unary p .neg (v "x"))) == "--x"
#guard exprText (.unary p .not (bin .or (v "a") (v "b"))) == "!(a | b)"
#guard exprText (bin .sub (v "a") (.unary p .neg (v "b"))) == "a - -b"
#guard exprText (.field p (.unary p .inv (v "x")) (nm "0")) == "(~x).0"
#guard exprText (.call p (.field p (v "a") (nm "f")) [n 1, bin .add (n 2) (n 3)]) ==
  "(a.f)(1, 2 + 3)"
#guard exprText (.index p (bin .add (v "a") (v "b")) [n 0]) == "(a + b)[0]"
#guard exprText (bin .addw (v "a") (.cond p (v "c") (v "x") (v "y"))) ==
  "a +% (if (c) { x } else { y })"
#guard exprText (.cond p (.cond p (v "c") (v "d") (v "e")) (v "x") (bin .add (v "y") (n 1))) ==
  "if (if (c) { d } else { e }) { x } else { y + 1 }"
#guard exprText (.str p "a\"b") == "\"a\\\"b\""

/-!
A tuple of one element ends with `,)`. A container is a primary, and its elements print at
level 0. A `select` is a postfix form.
-/
#guard exprText (.unit p) == "()"
#guard exprText (.tuple p [v "a"]) == "(a,)"
#guard exprText (.tuple p [bin .add (v "a") (n 1), .unit p]) == "(a + 1, ())"
#guard exprText (.tuple p [.tuple p [v "a"]]) == "((a,),)"
#guard exprText (.array p []) == "[]"
#guard exprText (.array p [.cond p (v "c") (n 1) (n 0), n 2]) ==
  "[if (c) { 1 } else { 0 }, 2]"
#guard exprText (.select p (v "t") p 0) == "t.0"
#guard exprText (.select p (.select p (v "t") p 1) p 2) == "t.1.2"
#guard exprText (.select p (.tuple p [n 1, n 2]) p 1) == "(1, 2).1"
#guard exprText (.select p (bin .add (v "a") (v "b")) p 0) == "(a + b).0"
#guard exprText (.select p (.unary p .neg (v "t")) p 0) == "(-t).0"
#guard exprText (.unary p .neg (.select p (v "t") p 0)) == "-t.0"
#guard exprText (.index p (.select p (.array p [n 1]) p 0) [n 0]) == "[1].0[0]"
#guard exprText (.field p (.select p (v "t") p 0) (nm "f")) == "t.0.f"

/-! A type prints `()`, a tuple type, and `[T; N]` with `N` at level 0. -/
#guard (TypeExpr.unit p).print == "()"
#guard (TypeExpr.tuple p [u8]).print == "(UInt[8],)"
#guard (TypeExpr.tuple p [t "Bool", .unit p]).print == "(Bool, ())"
#guard (TypeExpr.array p (.array p u8 (n 2)) (bin .add (v "N") (n 1))).print ==
  "[[UInt[8]; 2]; N + 1]"

/-! Statements and items print as indented lines. -/
#guard Print.print [counter, inc] ==
  "module Counter(comptime W: Nat) domains(clk) {\n" ++
  "    output q: UInt[W];\n" ++
  "}\n\n" ++
  "fn inc(x: UInt[8]) -> UInt[8] {\n" ++
  "    return x +% 1;\n" ++
  "}\n"
#guard (Stmt.ctIf p (v "c") [.local p true (nm "x") none (n 1)] (some [])).print 0 ==
  "comptime if (c) {\n    let mut x = 1;\n} else {}\n"
#guard (Stmt.ctFor p (nm "i") (n 0) (n 4) [.block p [.connect p (v "o") (v "i")]]).print 0 ==
  "comptime for i in 0 .. 4 {\n    {\n        o := i;\n    }\n}\n"

end Silicon.Source.Test.Print
