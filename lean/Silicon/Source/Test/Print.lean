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

/-! Each type kind. -/
#guard u8.dump == "(index (name \"UInt\") ((num 8)))"
#guard (t "Bool").dump == "(name \"Bool\")"

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
  .module p (nm "Counter") [⟨p, true, nm "W", t "Nat"⟩] [nm "clk"]
    [.output p (nm "q") (.index p (t "UInt") [v "W"])]

def inc : Item :=
  .fn p false (nm "inc") [⟨p, false, nm "x", u8⟩] u8 [.ret p (some (bin .addw (v "x") (n 1)))]

#guard (Item.const p (nm "N") (t "Nat") (n 3)).dump == "(const \"N\" (name \"Nat\") (num 3))"
#guard inc.dump ==
  "(fn false \"inc\" ((param false \"x\" (index (name \"UInt\") ((num 8))))) " ++
  "(index (name \"UInt\") ((num 8))) ((ret (some (binary addw (name \"x\") (num 1))))))"
#guard counter.dump ==
  "(module \"Counter\" ((param true \"W\" (name \"Nat\"))) (\"clk\") " ++
  "((output \"q\" (index (name \"UInt\") ((name \"W\"))))))"

/-! One line for each item, each line ends with LF, and no items give an empty dump. -/
#guard Print.dump [] == ""
#guard Print.dump [.const p (nm "N") (t "Nat") (n 3)] == "(const \"N\" (name \"Nat\") (num 3))\n"
#guard (Print.dump [inc, counter]).splitOn "\n" == [inc.dump, counter.dump, ""]

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
  "a.f(1, 2 + 3)"
#guard exprText (.index p (bin .add (v "a") (v "b")) [n 0]) == "(a + b)[0]"
#guard exprText (bin .addw (v "a") (.cond p (v "c") (v "x") (v "y"))) ==
  "a +% (if (c) { x } else { y })"
#guard exprText (.cond p (.cond p (v "c") (v "d") (v "e")) (v "x") (bin .add (v "y") (n 1))) ==
  "if (if (c) { d } else { e }) { x } else { y + 1 }"
#guard exprText (.str p "a\"b") == "\"a\\\"b\""

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
