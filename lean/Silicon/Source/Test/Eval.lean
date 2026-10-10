import Silicon.Source.Cli

/-!
These tests check the static evaluator at the boundary of `eval` and `cost`. They check each
operator with its boundary cases, the fit rule, the static faults, and the table of constants.
They also check the calls and the exact charges of the cost model at the budget limits.

Slice 1 has no lists and no arrays. The budget cases of section 11.3 with a list copy and with
a nested doubling thus come with slice 2.
-/

namespace Silicon.Source.Test.Eval

open Silicon.Source

/-! The result of `eval`: the serialization, or the code and the position of the error. -/
def out (src expr : String) (fuel : Nat := 100000000) (depth : Nat := 1000) : String :=
  match Cli.evalText { budget := { fuel, depth } } src expr with
  | .ok (v, _) => v.serialize
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"

/-! The fuel that `eval` uses with the default budgets. -/
def cost (src expr : String) : Nat :=
  match Cli.evalText {} src expr with
  | .ok (_, used) => used
  | .error _ => 0

/-! The cost is `units`. This fuel passes, and one unit less gives `S015`. -/
def exact (src expr : String) (units : Nat) : Bool :=
  cost src expr == units && !(out src expr units).startsWith "S" &&
    (out src expr (units - 1)).startsWith "S015"

/-! The result of `cost` with the top selection `t`. -/
def top (src t : String) (fuel : Nat := 100000000) (depth : Nat := 1000) : String :=
  match Cli.costText { budget := { fuel, depth } } src t with
  | .ok text => text
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .usage _ => "usage"

/-! The ordinary operators on `Int` do not wrap. Division truncates toward zero. -/
#guard out "" "1 + 2" == "(int 3)"
#guard out "" "1 - 2" == "(int -1)"
#guard out "" "18446744073709551615 + 1" == "(int 18446744073709551616)"
#guard out "" "4294967296 * 4294967296" == "(int 18446744073709551616)"
#guard out "" "7 / 2" == "(int 3)"
#guard out "" "-7 / 2" == "(int -3)"
#guard out "" "7 / -2" == "(int -3)"
#guard out "" "-7 % 2" == "(int -1)"
#guard out "" "7 % -2" == "(int 1)"
#guard out "" "-(-5)" == "(int 5)"

/-! The wrapping operators keep the finite type. A static integer takes the other type. -/
#guard out "" "UInt[8](250) +% 10" == "(uint 8 4)"
#guard out "" "UInt[8](0) -% 1" == "(uint 8 255)"
#guard out "" "UInt[8](16) *% 16" == "(uint 8 0)"
#guard out "" "SInt[8](127) +% 1" == "(sint 8 -128)"
#guard out "" "SInt[8](-128) -% 1" == "(sint 8 127)"
#guard out "" "1 +% UInt[1](1)" == "(uint 1 0)"
#guard out "" "-UInt[8](1)" == "(uint 8 255)"
#guard out "" "-SInt[8](-128)" == "(sint 8 -128)"

/-! The bitwise operators. An `Int` uses infinite two's complement. -/
#guard out "" "UInt[8](12) & 10" == "(uint 8 8)"
#guard out "" "UInt[8](12) | 10" == "(uint 8 14)"
#guard out "" "UInt[8](12) ^ 10" == "(uint 8 6)"
#guard out "" "~UInt[8](0)" == "(uint 8 255)"
#guard out "" "~SInt[8](0)" == "(sint 8 -1)"
#guard out "" "~5" == "(int -6)"
#guard out "" "~-1" == "(int 0)"
#guard out "" "-6 & 3" == "(int 2)"
#guard out "" "-6 | 3" == "(int -5)"
#guard out "" "-6 ^ 3" == "(int -7)"
#guard out "" "-6 & -3" == "(int -8)"
#guard out "" "-6 | -3" == "(int -1)"
#guard out "" "-6 ^ -3" == "(int 7)"
#guard out "" "12 & 10" == "(int 8)"

/-! The Boolean operators. `&&` and `||` skip the right operand when the left decides. -/
#guard out "" "!true" == "(bool false)"
#guard out "" "true && false" == "(bool false)"
#guard out "" "false || true" == "(bool true)"
#guard out "" "false && 1 / 0 == 0" == "(bool false)"
#guard out "" "true || 1 / 0 == 0" == "(bool true)"
#guard out "" "true && 1 / 0 == 0" == "S013 1:9"
#guard out "" "if (true) { 1 } else { 1 / 0 }" == "(int 1)"

/-! Equality and order. `UInt` orders unsigned, `SInt` signed. -/
#guard out "" "3 == 3" == "(bool true)"
#guard out "" "true != false" == "(bool true)"
#guard out "" "\"a\" == \"a\"" == "(bool true)"
#guard out "" "UInt[8] == UInt[8]" == "(bool true)"
#guard out "" "UInt[8] == SInt[8]" == "(bool false)"
#guard out "" "UInt[8](255) > 1" == "(bool true)"
#guard out "" "SInt[8](-1) < 1" == "(bool true)"
#guard out "" "SInt[8](-128) <= SInt[8](-128)" == "(bool true)"
#guard out "" "-1 >= 0" == "(bool false)"
#guard out "" "UInt[8](300 - 45) == 255" == "(bool true)"

/-! Shifts. A finite shift of the width or more gives zero or the sign bits. -/
#guard out "" "1 << 8" == "(int 256)"
#guard out "" "-3 >> 1" == "(int -2)"
#guard out "" "-3 >> 100" == "(int -1)"
#guard out "" "3 >> 100" == "(int 0)"
#guard out "" "1 << 64" == "(int 18446744073709551616)"
#guard out "" "UInt[8](1) << 7" == "(uint 8 128)"
#guard out "" "UInt[8](1) << 8" == "(uint 8 0)"
#guard out "" "UInt[8](128) >> 7" == "(uint 8 1)"
#guard out "" "SInt[8](-128) >> 7" == "(sint 8 -1)"
#guard out "" "SInt[8](-128) >> 1000" == "(sint 8 -1)"
#guard out "" "SInt[8](64) >> 1000" == "(sint 8 0)"
#guard out "" "UInt[8](1) << UInt[2](3)" == "(uint 8 8)"
#guard out "" "1 << -1" == "S013 1:1"
#guard out "" "UInt[8](1) << -1" == "S013 1:1"
#guard out "" "UInt[8](1) << SInt[2](1)" == "S010 1:1"
#guard out "" "1 << UInt[2](1)" == "S010 1:1"
#guard out "" "true << 1" == "S010 1:1"

/-! `resize` keeps the signedness, and `reinterpret` keeps the width. -/
#guard out "" "resize(UInt[16], UInt[8](255))" == "(uint 16 255)"
#guard out "" "resize(SInt[16], SInt[8](-1))" == "(sint 16 -1)"
#guard out "" "resize(UInt[4], UInt[8](250))" == "(uint 4 10)"
#guard out "" "resize(SInt[4], SInt[8](-7))" == "(sint 4 -7)"
#guard out "" "resize(SInt[16], UInt[8](1))" == "S010 1:1"
#guard out "" "resize(UInt[16], 1)" == "S010 1:1"
#guard out "" "reinterpret(SInt[8], UInt[8](255))" == "(sint 8 -1)"
#guard out "" "reinterpret(UInt[8], SInt[8](-128))" == "(uint 8 128)"
#guard out "" "reinterpret(UInt[4], SInt[8](1))" == "S010 1:1"

/-! The fit rule `S012`: a value fits its finite type, a `Nat` is not negative, a width is 1 to
65536. -/
#guard out "" "UInt[8](255)" == "(uint 8 255)"
#guard out "" "UInt[8](256)" == "S012 1:1"
#guard out "" "UInt[8](-1)" == "S012 1:1"
#guard out "" "SInt[8](-128)" == "(sint 8 -128)"
#guard out "" "SInt[8](127)" == "(sint 8 127)"
#guard out "" "SInt[8](-129)" == "S012 1:1"
#guard out "" "SInt[8](128)" == "S012 1:1"
#guard out "" "SInt[1](-1)" == "(sint 1 -1)"
#guard out "" "SInt[1](1)" == "S012 1:1"
#guard out "" "Nat(0)" == "(int 0)"
#guard out "" "Nat(-1)" == "S012 1:1"
#guard out "" "UInt[8](1) +% 256" == "S012 1:1"
#guard out "" "UInt[0]" == "S012 1:1"
#guard out "" "UInt[65536]" == "(type (uint 65536))"
#guard out "" "UInt[65537]" == "S012 1:1"

/-! The type rule `S010` on static operands. -/
#guard out "" "UInt[8](1) + 1" == "S010 1:1"
#guard out "" "1 +% 1" == "S010 1:1"
#guard out "" "true + 1" == "S010 1:1"
#guard out "" "UInt[8](1) +% SInt[8](1)" == "S010 1:1"
#guard out "" "UInt[8](1) == UInt[4](1)" == "S010 1:1"
#guard out "" "true < false" == "S010 1:1"
#guard out "" "!1" == "S010 1:1"
#guard out "" "\"a\" + \"b\"" == "S010 1:1"
#guard out "" "if (1) { 1 } else { 2 }" == "S010 1:1"
#guard out "" "UInt[true]" == "S010 1:1"
#guard out "" "Bool(1)" == "S010 1:1"

/-! The static faults `S013` and the assertions `S014`. -/
#guard out "" "1 / 0" == "S013 1:1"
#guard out "" "1 % 0" == "S013 1:1"
def asserts : String :=
  "comptime fn check(n: Nat) -> Nat {\n" ++
  "    static_assert(n < 4, \"n is small\");\n" ++
  "    comptime if (n == 3) { error(\"three\"); }\n" ++
  "    return n;\n" ++
  "}"
#guard out asserts "check(2)" == "(int 2)"
#guard out asserts "check(3)" == "S014 3:28"
#guard out asserts "check(4)" == "S014 2:5"
#guard out asserts "static_assert(true, \"x\")" == "S010 1:1"

/-! Locals, assignment, `comptime for`, and recursion. -/
def program : String :=
  "comptime fn fact(n: Nat) -> Nat {\n" ++
  "    comptime if (n == 0) { return 1; }\n" ++
  "    return n * fact(n - 1);\n" ++
  "}\n" ++
  "comptime fn sum(n: Nat) -> Int {\n" ++
  "    let mut s = 0;\n" ++
  "    comptime for i in 0..n { s = s + i; }\n" ++
  "    return s;\n" ++
  "}\n" ++
  "comptime fn fib(n: Nat) -> Nat {\n" ++
  "    comptime if (n < 2) { return n; } else { return fib(n - 1) + fib(n - 2); }\n" ++
  "}\n" ++
  "comptime fn mask(comptime w: Nat) -> UInt[w] {\n" ++
  "    let x: UInt[w] = 0;\n" ++
  "    return ~x;\n" ++
  "}\n" ++
  "comptime fn bad(n: Nat) -> Nat {\n" ++
  "    let x = n;\n" ++
  "    x = 1;\n" ++
  "    return n - 5;\n" ++
  "}\n" ++
  "comptime fn none(n: Nat) -> Nat {\n" ++
  "    comptime if (n == 0) { return 0; }\n" ++
  "}\n" ++
  "fn wraps(x: UInt[8]) -> UInt[8] { return x +% 1; }"
#guard out program "fact(20)" == "(int 2432902008176640000)"
#guard out program "fact(0)" == "(int 1)"
#guard out program "sum(10)" == "(int 45)"
#guard out program "sum(0)" == "(int 0)"
#guard out program "fib(15)" == "(int 610)"
#guard out program "mask(12)" == "(uint 12 4095)"
#guard out program "wraps(255)" == "(uint 8 0)"
#guard out program "wraps(256)" == "S012 1:1"
#guard out program "fact(-1)" == "S012 1:1"
#guard out program "bad(1)" == "S010 19:5"
#guard out program "none(0)" == "(int 0)"
#guard out program "none(1)" == "S010 1:1"
#guard out program "fact" == "S010 1:1"
#guard out program "resize" == "S010 1:1"

/-! A return checks its type. A `Nat` result is not negative. -/
#guard out "comptime fn f(n: Int) -> Nat {\n    return n;\n}" "f(-1)" == "S012 2:5"
#guard out "comptime fn f(n: Int) -> Bool {\n    return n;\n}" "f(1)" == "S010 2:5"
#guard out "comptime fn f(n: Int) -> Int {\n    let x: Nat = n;\n    return x;\n}" "f(-2)" ==
  "S012 2:5"

/-! A static evaluation makes no hardware: `:=` in a `fn` is `S011`. -/
#guard out "fn f(x: Bool) -> Bool {\n    x := x;\n    return x;\n}" "f(true)" == "S011 2:5"

/-! Constants evaluate once. A constant that depends on itself is `S019` at the use. -/
def consts : String :=
  "const A: Nat = 2;\n" ++
  "const B: UInt[8] = A + 250;\n" ++
  "const C: Nat = C + 1;\n" ++
  "const D: Nat = E;\n" ++
  "const E: Nat = D;\n" ++
  "const F: Nat = 1 / 0;\n" ++
  "const G: Nat = A - 3;"
#guard out consts "A" == "(int 2)"
#guard out consts "B" == "(uint 8 252)"
#guard out consts "B +% B" == "(uint 8 248)"
#guard out consts "C" == "S019 3:16"
#guard out consts "D" == "S019 5:16"
#guard out consts "E" == "S019 4:16"
#guard out consts "F" == "S013 6:16"
#guard out consts "G" == "S012 7:1"

/-!
Exact charges. `1 + 2`: the node 1, each literal 1 and its size 1, and the sum of the operand
sizes 2. A use of a done constant charges only its node.
-/
#guard exact "" "1 + 2" 7
#guard exact "" "true" 2
#guard exact "" "\"abc\"" 5
#guard exact "" "-5" 4
#guard exact "" "UInt[8]" 6
#guard exact "" "UInt[8](3)" 12
#guard exact "" "3 * 4" 6
#guard exact "" "18446744073709551616 * 18446744073709551616" 11
#guard exact "" "1 << 64" 7
#guard exact "" "1 << 63" 6
#guard exact "" "true && false" 5
#guard exact "" "false && true" 3
#guard exact "" "if (true) { 1 } else { 2 }" 5
#guard exact "const A: Nat = 2;" "A + A" 8
#guard exact "const A: Nat = 2;\nconst B: Nat = A;" "B" 7
#guard exact "comptime fn f(n: Nat) -> Nat { return n; }" "f(1)" 11
#guard exact "comptime fn s() -> Int { comptime for i in 0..3 {} return 0; }" "s()" 21
#guard exact "comptime fn s() -> Int { let x = 1; let y = x; return y; }" "s()" 13
/-! A block statement charges its unit once. A builtin argument is a copy: `resize` pays 3. -/
#guard exact "comptime fn s() -> Int { { } return 0; }" "s()" 9
#guard exact "comptime fn s() -> Int { return 0; }" "s()" 8
#guard exact "" "resize(UInt[16], UInt[8](1))" 25
#guard exact "comptime fn s() -> Int { static_assert(true, \"abc\"); return 0; }" "s()" 23
#guard exact program "fact(10)" (cost program "fact(10)")
#guard exact program "sum(100)" (cost program "sum(100)")

/-! A large shift fails before it runs: its charge is the size of its result. -/
#guard out "" "1 << 100000000000" == "S015 1:1"
#guard out "" "1 << 6400000000" 100000000 == "S015 1:1"
#guard cost "" "1 << 64000" == 1006

/-! A shift with an enormous count makes no value above its charge. These pass with 20 units. -/
#guard out "" "0 << 100000000000" 20 == "(int 0)"
#guard out "" "0 << 18446744073709551616" 20 == "(int 0)"
#guard out "" "-1 << 100000000000" 20 == "S015 1:1"
#guard out "" "0 >> 100000000000" 20 == "(int 0)"
#guard out "" "1 >> 100000000000" 20 == "(int 0)"
#guard out "" "-1 >> 100000000000" 20 == "(int -1)"

/-! A `comptime for` pays its range and each loop value. A large offset thus pays its size. -/
def bigFor : String :=
  "comptime fn f() -> Int { let a = 1 << 64000000; comptime for i in a..a + 10000 {} return 0; }"
#guard out bigFor "f()" 4000000 == "S015 1:49"
def wideFor : String :=
  "comptime fn f() -> Int { let a = 1 << 6400; comptime for i in a..a + 3 {} return 0; }"
#guard exact wideFor "f()" (cost wideFor "f()")
#guard cost wideFor "f()" == 731

/-!
A frame holds only the bindings that run. `f` and `r` declare `locals` locals in a branch that
does not run, so a call does not pay for them in fuel or in memory.
-/
def skipped (locals : Nat) : String :=
  let dead := String.join ((List.range locals).map fun i => s!"let x{i} = 0; ")
  s!"comptime fn f() -> Int \{ comptime if (false) \{ {dead}} let y = 0; return y; }\n" ++
  "comptime fn g(n: Nat) -> Int { comptime for i in 0..n { let z = f(); } return 0; }\n" ++
  s!"comptime fn r(n: Nat) -> Int \{ comptime if (false) \{ {dead}}\n" ++
  "  comptime if (n == 0) { return 0; } return r(n - 1); }\n"
#guard out (skipped 2000) "g(100)" == "(int 0)"
#guard out (skipped 2000) "r(500)" == "(int 0)"
#guard cost (skipped 2000) "g(100)" == cost (skipped 1) "g(100)"

/-! A message prints a large integer as its bit length and cuts a long string. -/
#guard Eval.intText (2 ^ 256 - 1) == toString ((2 : Int) ^ 256 - 1)
#guard Eval.intText (2 ^ 256) == "an integer of 257 bits"
#guard Eval.intText (-(2 ^ 6400000)) == "a negative integer of 6400001 bits"
#guard Eval.strText "abc" == "abc"
#guard Eval.strText (String.ofList (List.replicate 100 'a')) ==
  String.ofList (List.replicate 64 'a') ++ "... (100 characters)"
#guard out "" "UInt[1 << 6400000]" 100008 == "S012 1:1"
#guard out "" "Nat(-(1 << 6400000))" 400000 == "S012 1:1"
#guard out "" "UInt[8](1 << 6400000)" 400000 == "S012 1:1"
#guard out "" "1 << -(1 << 6400000)" 300000 == "S013 1:1"
#guard out "" "1 << (1 << 6400)" 1000 == "S015 1:1"

/-! A right shift reads its operand in full, so it pays the size of its operand. -/
#guard exact "" "-(1 << 6400) >> 6399" 312
#guard out "" "UInt[8](1) << 100000000000" 20 == "(uint 8 0)"
#guard out "" "SInt[8](-1) >> 100000000000" 20 == "(sint 8 -1)"
#guard out "" "UInt[65536](1) << 100000000000" 20 == "S015 1:1"
#guard out "" "resize(UInt[65536], UInt[8](1))" 20 == "S015 1:1"

/-!
The nesting depth counts active calls. `d(5)` has 6 active calls. The call that goes above the
limit fails.
-/
def deep : String :=
  "comptime fn d(n: Nat) -> Nat {\n" ++
  "    comptime if (n == 0) { return 0; }\n" ++
  "    return d(n - 1);\n" ++
  "}"
#guard out deep "d(5)" (depth := 6) == "(int 0)"
#guard out deep "d(5)" (depth := 5) == "S015 3:12"
#guard out deep "d(0)" (depth := 0) == "S015 1:1"
#guard out deep "d(2000)" == "S015 3:12"

/-!
A chain of 300 acyclic constants. `eval` nests the 300 constants. The top selection nests one
level more, as section 11.3 states: the depth 301 passes, and 300 gives `S015`. The top adds
18 units: its argument 2, the `instance` charge 1, the parameter type 9, and its conversion 6.
-/
def chain : String := Id.run do
  let mut s := "const C0: Nat = 0;\n"
  for k in [1:300] do
    s := s ++ s!"const C{k}: Nat = C{k - 1} + 1;\n"
  return s ++ "module Top(comptime x: UInt[C299 + 1]) {\n}\n"
#guard out chain "C299" (depth := 300) == "(int 299)"
#guard exact chain "C299" 2097
#guard out chain "C299" (depth := 299) == "S015 2:17"
#guard top chain "Top(5)" (depth := 301) == s!"total {cost chain "C299" + 18}\n"
#guard top chain "Top(5)" (depth := 300) == "S015 2:17"

/-! `cost` covers the static part of the top selection: its arguments and parameter types. -/
def counter : String := "module Counter(comptime W: Nat, comptime E: Bool) {\n}"
#guard top counter "Counter(8, true)" == "total 8\n"
#guard top counter "Counter(8, true)" (fuel := 5) == "S015 1:1"
#guard top counter "Counter(-1, true)" == "S012 1:1"
#guard top counter "Counter(8, 1)" == "S010 1:1"
#guard top counter "Counter(8)" == "S007 1:1"
#guard top counter "Counter(8, true)" (depth := 0) == "S015 1:1"
#guard top counter "Counter(8 + 1, true)" == "usage"
#guard top counter "Nope(8)" == "usage"

/-! Errors of the earlier passes come first, also in `EXPR`. -/
#guard out "const A: Nat = ;" "1" == "S001 1:16"
#guard out "" "x" == "S003 1:1"
#guard out "" "1 +" == "S001 1:4"
#guard out "" "UInt[8, 9]" == "S007 1:1"
#guard out "module M() { reg r: Bool = false; }" "M" == "S003 1:1"

end Silicon.Source.Test.Eval
