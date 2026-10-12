-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli

/-!
These tests check the static evaluator at the boundary of `eval` and `cost`. They check each
operator with its boundary cases, the fit rule, the static faults, and the table of constants.
They also check the calls and the exact charges of the cost model at the budget limits.

The static containers of slice 2 come next. Their tests check the literals, the typed uses,
the index, the selector, and `len`. They also check the equality, the join, the depth bound,
and the nested doubling of section 11.3.

The types as values of slice 2 come last. Their tests check the type constructors with their
charges, the aliases, the table of struct specializations, and the struct cases of section 11.3.
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
  | .reject line => line
  | .usage _ => "usage"
  | .defect _ => "defect"

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
59 units. Its argument charges 2, the `instance` charge 1, and the decimal form 1. Its
serialization charges 34 bytes and `Top$5` 5 bytes. The parameter type charges 9, its
conversion 6, and its body 1. The lowering charges 30: the module and its name 5, the domain
ports 20, and the design and its name 5.
-/
def chain : String := Id.run do
  let mut s := "const C0: Nat = 0;\n"
  for k in [1:300] do
    s := s ++ s!"const C{k}: Nat = C{k - 1} + 1;\n"
  return s ++ "module Top(comptime x: UInt[C299 + 1]) {\n}\n"
#guard out chain "C299" (depth := 300) == "(int 299)"
#guard exact chain "C299" 2097
#guard out chain "C299" (depth := 299) == "S015 2:17"
#guard top chain "Top(5)" (depth := 301) ==
  s!"total {cost chain "C299" + 89}\nTop$5 {cost chain "C299" + 41}\n"
#guard top chain "Top(5)" (depth := 300) == "S015 2:17"

/-!
`cost` covers the top selection: its arguments with their `instance` charge, its serialization
of 50 bytes, and its emitted name of 12 bytes. Then its instantiation charges its parameter types
and its body. The lowering charges 42: the module and its name 11, the domain ports 20, and the
design and its name 11.
-/
def counter : String := "module Counter(comptime W: Nat, comptime E: Bool) {\n}"
#guard top counter "Counter(8, true)" == "total 114\nCounter$8$1b 34\n"
#guard top counter "Counter(8, true)" (fuel := 5) == "S015 1:1"
#guard top counter "Counter(-1, true)" == "S012 1:1"
#guard top counter "Counter(8, 1)" == "S010 1:1"
#guard top counter "Counter(8)" == "S007 1:1"
#guard top counter "Counter(8, true)" (depth := 0) == "S015 1:1"
#guard top counter "Counter(8 + 1, true)" == "usage"
#guard top counter "Nope(8)" == "usage"

/-! `()`, tuples, and arrays. A literal charges its node, its elements, and its size. -/
#guard out "" "()" == "(unit)"
#guard out "" "(1,)" == "(tuple ((int 1)))"
#guard out "" "(1, true)" == "(tuple ((int 1) (bool true)))"
#guard out "" "[1, 2]" == "(array int ((int 1) (int 2)))"
#guard out "" "[[1, 2], [3, 4]]" ==
  "(array (array int 2) ((array int ((int 1) (int 2))) (array int ((int 3) (int 4)))))"
#guard exact "" "()" 2
#guard exact "" "(1, true)" 8
#guard exact "" "[1, 2]" 8

/-!
The elements of an array take their common type by the operand rule. `UInt[8](2)` charges 12,
and the conversion of `1` charges 2.
-/
#guard out "" "[1, UInt[8](2)]" == "(array (uint 8) ((uint 8 1) (uint 8 2)))"
#guard exact "" "[1, UInt[8](2)]" 20
#guard out "" "[1, true]" == "S010 1:1"
#guard out "" "[[1], [2, 3]]" == "S010 1:1"
#guard out "" "[UInt[8](1), UInt[16](2)]" == "S010 1:1"
#guard out "" "[(\"a\", 1)]" == "S010 1:1"
#guard out "" "[300, UInt[8](1)]" == "S012 1:1"

/-! `[]` takes its type only at a typed use. As an element or an operand, it is `S010` there. -/
def empty : String :=
  "fn f(x: [UInt[8]; 0]) -> Int { return len(x); }\n" ++
  "fn g(comptime x: [Bool; 0]) -> Int { return len(x); }\n" ++
  "fn h() -> [Bool; 0] { return []; }\n" ++
  "const E: [Bool; 0] = [];"
#guard out empty "f([])" == "(int 0)"
#guard out empty "g([])" == "(int 0)"
#guard out empty "h()" == "(array bool ())"
#guard out empty "E" == "(array bool ())"
#guard out "" "[]" == "S010 1:1"
#guard out "" "[[]]" == "S010 1:2"
#guard out "" "len([])" == "S010 1:5"
#guard out "" "[] == []" == "S010 1:1"
#guard out "fn f() -> Int { let a = []; return 0; }" "f()" == "S010 1:25"
#guard out "fn f() -> Int { []; return 0; }" "f()" == "S010 1:17"
#guard out "fn f() -> Int { let a: [Bool; 1] = []; return 0; }" "f()" == "S010 1:17"

/-!
A typed use of a container converts each element. It charges the size of the value plus the
size of the result: 3 + 3 here. The type `[UInt[8]; 2]` charges 13, and its metadata 3.
-/
def typed (ty v : String) : String := s!"fn f() -> Int \{ let a: {ty} = {v}; return 0; }"
#guard cost (typed "[UInt[8]; 2]" "[1, 2]") "f()" ==
  cost "fn f() -> Int { let a = [1, 2]; return 0; }" "f()" + 16 + 6
#guard out "fn f(a: [UInt[8]; 2]) -> UInt[8] { return a[1]; }" "f([1, 2])" == "(uint 8 2)"
#guard out "fn f(a: [UInt[8]; 2]) -> UInt[8] { return a[1]; }" "f([1, 256])" == "S012 1:1"
#guard out "fn f(a: [UInt[8]; 2]) -> UInt[8] { return a[1]; }" "f([1, 2, 3])" == "S010 1:1"
#guard out "fn f() -> [Nat; 2] { let a: [Nat; 2] = [1, 2]; return a; }" "f()" ==
  "(array nat ((int 1) (int 2)))"
#guard out (typed "[Nat; 2]" "[1, -1]") "f()" == "S012 1:17"
#guard out (typed "(UInt[8], Bool)" "(1, true)") "f()" == "(int 0)"
#guard out (typed "(UInt[8], Bool)" "(1, 2)") "f()" == "S010 1:17"
#guard out (typed "()" "()") "f()" == "(int 0)"
#guard out (typed "Unit" "()") "f()" == "(int 0)"

/-! A `()` part of a container keeps its value when another part converts. -/
#guard out "fn f() -> (Nat, ()) { let x: (Nat, ()) = (1, ()); return x; }" "f()" ==
  "(tuple ((int 1) (unit)))"
#guard out (typed "((), Nat)" "((), 1)") "f()" == "(int 0)"
#guard out (typed "[(Nat, ()); 1]" "[(1, ())]") "f()" == "(int 0)"
def unitArg : String :=
  "module C(comptime A: ([Nat; 2], ())) {\n  output y: Bool;\n  y := true;\n}\n" ++
  "module M() {\n  output y: Bool;\n  instance c = C(([1, 2], ()));\n  y := c.y;\n}\n"
#guard (top unitArg "M()").startsWith "total"
#guard out "fn f() -> Int { let mut a: [Int; 1] = [1]; a = [2]; return a[0]; }" "f()" ==
  "(int 2)"

/-!
The length of an array type is a static `Nat` at its expression. A container type checks its
depth.
-/
#guard out (typed "[Bool; -1]" "[]") "f()" == "S012 1:31"
#guard out (typed "[Bool; true]" "[]") "f()" == "S010 1:31"
#guard out (typed "[[Bool; 1]; 1]" "[[true]]") "f()" (depth := 3) == "(int 0)"
#guard out (typed "[[Bool; 1]; 1]" "[[true]]") "f()" (depth := 2) == "S015 1:24"
#guard out (typed "([Bool; 1],)" "([true],)") "f()" (depth := 2) == "S015 1:24"

/-!
An index and a selector refer to an element, and `len` refers to its array. They charge no
size. The selector can be any number literal.
-/
#guard out "" "[1, 2][1]" == "(int 2)"
#guard out "" "(1, true)[1]" == "(bool true)"
#guard out "" "(1, 2).1" == "(int 2)"
#guard out "" "(1, 2).0x1" == "(int 2)"
#guard out "" "len([1, 2, 3])" == "(int 3)"
#guard exact "" "[1, 2][0]" 11
#guard exact "" "(1, 2).0" 9
#guard exact "" "len([1, 2])" 10
#guard out "" "[1, 2][2]" == "S013 1:8"
#guard out "" "[1, 2][-1]" == "S013 1:8"
#guard out "" "(1, 2).2" == "S013 1:8"
#guard out "" "[1, 2][true]" == "S010 1:8"
#guard out "" "[1, 2][0, 1]" == "S010 1:1"
#guard out "" "[1, 2].0" == "S010 1:1"
#guard out "" "1[0]" == "S010 1:1"
#guard out "" "len(1)" == "S010 1:1"

/-!
A binding of an element copies it. `a[0]` charges 4 and its copy 3, where the literal `[1, 2]`
charges 8.
-/
#guard cost "fn f() -> Int { let a = [[1, 2]]; let b = a[0]; return 0; }" "f()" ==
  cost "fn f() -> Int { let a = [[1, 2]]; let b = [1, 2]; return 0; }" "f()" - 8 + 4 + 3

/-!
`==` and `!=` on containers need a common type for each pair of elements. They charge the sum
of the sizes. The orderings take no container.
-/
#guard out "" "[1, 2] == [1, 2]" == "(bool true)"
#guard out "" "[1, 2] != [1, 3]" == "(bool true)"
#guard out "" "() == ()" == "(bool true)"
#guard out "" "(1, (2, 3)) == (1, (2, 4))" == "(bool false)"
#guard out "" "(\"a\", 1) == (\"a\", 1)" == "(bool true)"
#guard out "" "[1, 2] == [UInt[8](1), 2]" == "(bool true)"
#guard exact "" "[1, 2] == [1, 2]" 23
#guard out "" "[300] == [UInt[8](1)]" == "S012 1:1"
#guard out "" "[1] == [1, 2]" == "S010 1:1"
#guard out "" "(1,) == (1, 2)" == "S010 1:1"
#guard out "" "[1] == (1,)" == "S010 1:1"
#guard out "" "[1] == 1" == "S010 1:1"
#guard out "" "[1] < [2]" == "S010 1:1"
#guard out "" "() >= ()" == "S010 1:1"
#guard out "" "[1] + [2]" == "S010 1:1"

/-! A new container above the nesting depth is `S015` at the node that makes it. -/
#guard out "fn f() -> Int { let a = [[[1]]]; return 0; }" "f()" (depth := 4) == "(int 0)"
#guard out "fn f() -> Int { let a = [[[1]]]; return 0; }" "f()" (depth := 3) == "S015 1:25"
#guard out "fn f() -> Int { let a = (((1,),),); return 0; }" "f()" (depth := 3) == "S015 1:25"

/-!
In this phase a container holds only static values. A hardware element is `S010` at the
element, and so is a handle. A hardware index is `S011` at the index.
-/
def hw (body : String) : String :=
  "module M(comptime N: Nat) {\n  input x: UInt[8];\n  output y: UInt[8];\n" ++
  "  reg r: UInt[8] = 0;\n" ++ body ++ "\n  r := x;\n  y := r;\n}\n"
#guard top (hw "  let t = (1, x);") "M(1)" == "S010 5:15"
#guard top (hw "  let t = [r];") "M(1)" == "S010 5:12"
#guard top (hw "  let h = x +% 1;\n  let u = [1, 2][h];") "M(1)" == "S011 6:18"
#guard top (hw "  let h = x +% 1;\n  let u: [Int; h] = [1];") "M(1)" == "S011 6:16"
#guard top (hw "  let u = x.0;") "M(1)" == "S010 5:11"
#guard top (hw "  let u = len(x);") "M(1)" == "S010 5:11"
#guard top (hw "  let t = [1, 2] == x;") "M(1)" == "S010 5:11"
#guard top (hw "  let t = [1, 2];\n  let u = t[N];") "M(2)" == "S013 6:13"
#guard (top (hw "  let t = [1, 2];\n  let u = t[N];") "M(1)").startsWith "total"

/-!
The nested doubling of section 11.3: making `a_k` charges `2^(k + 2) - 1`. Each `let` adds 4
units: the statement, the literal, and the two names. The join of the two element types
visits `k` pairs of arrays. With the fuel 1000000, the sum first goes above the fuel at the
`let` of `a17`.
-/
def doubling (k : Nat) : String :=
  "fn d() -> Int {\n" ++ String.join ((List.range (k + 1)).map fun i =>
    if i == 0 then "  let a0 = [0, 0];\n" else s!"  let a{i} = [a{i - 1}, a{i - 1}];\n") ++
  "  return 0;\n}"
#guard exact (doubling 0) "d()" 17
#guard (List.range 6).all fun k =>
  cost (doubling (k + 1)) "d()" == cost (doubling k) "d()" + 2 ^ (k + 3) - 1 + 4 + (k + 1)
#guard out (doubling 20) "d()" 1000000 == "S015 19:13"

/-!
The expected type flows into the elements of a literal, so a nested `[]` takes its type there.
Without a typed use, the first `[]` is `S010`. The shape of the literal must match the type.
-/
#guard out "fn f() -> [[Bool; 0]; 1] { let x: [[Bool; 0]; 1] = [[]]; return x; }" "f()" ==
  "(array (array bool 0) ((array bool ())))"
#guard out "fn f() -> ([Bool; 0], Int) { return ([], 1); }" "f()" ==
  "(tuple ((array bool ()) (int 1)))"
#guard out "fn g(x: [[Bool; 0]; 2]) -> Int { return len(x); }" "g([[], []])" == "(int 2)"
#guard out "fn f() -> Int { let x: [Bool; 0] = [[]]; return 0; }" "f()" == "S010 1:17"
#guard out "fn f() -> Int { let x = ([], 1); return 0; }" "f()" == "S010 1:26"
#guard out "" "[1, []]" == "S010 1:5"

/-!
An assignment to a place with an index or a selector `.N` replaces the selected part. The
right side takes the element type. A binding that shares the root keeps its value.
-/
def body (s : String) : String := s!"fn f() -> Int \{ {s} }"
#guard out (body "let mut a = [1, 2]; a[0] = 5; return a[0];") "f()" == "(int 5)"
#guard out "fn f() -> [[Int; 2]; 2] { let mut a = [[1, 2], [3, 4]]; a[1][0] = 9; return a; }"
  "f()" == "(array (array int 2) ((array int ((int 1) (int 2))) (array int ((int 9) (int 4)))))"
#guard out ("fn f() -> (Int, (Bool, Int)) { let mut a = (1, (true, 2)); a.1.0 = false; " ++
  "a.1.1 = 7; return a; }") "f()" == "(tuple ((int 1) (tuple ((bool false) (int 7)))))"
#guard out "fn f() -> [(Int, Int); 1] { let mut a = [(1, 2)]; a[0].1 = 5; return a; }" "f()" ==
  "(array (tuple (int int)) ((tuple ((int 1) (int 5)))))"
#guard out "fn f() -> [[Int; 2]; 1] { let mut a = [[1, 2]]; let b = a; a[0][0] = 9; return b; }"
  "f()" == "(array (array int 2) ((array int ((int 1) (int 2)))))"
#guard out "fn f() -> Int { let mut x: [[Bool; 0]; 1] = [[]]; x[0] = []; return len(x[0]); }"
  "f()" == "(int 0)"

/-!
The indices of the place evaluate first, from left to right, each with its checks. Then the
right side evaluates.
-/
#guard out (body "let mut a = [[1, 2]]; a[1 / 0][0] = 1 / 0; return 0;") "f()" == "S013 1:41"
#guard out (body "let mut a = [[1, 2]]; a[0][1 / 0] = 1 / 0; return 0;") "f()" == "S013 1:44"
#guard out (body "let mut a = [[1, 2]]; a[0][5] = 1 / 0; return 0;") "f()" == "S013 1:44"
#guard out (body "let mut a = [[1, 2]]; a[0][0] = 1 / 0; return 0;") "f()" == "S013 1:49"
#guard out (body "let mut a = (1, 2); a.2 = 3; return 0;") "f()" == "S013 1:39"
#guard out (body "let mut a: [UInt[8]; 2] = [1, 2]; a[0] = 256; return 0;") "f()" ==
  "S012 1:51"
#guard out (body "let mut a: [UInt[8]; 2] = [1, 2]; a[0] = true; return 0;") "f()" ==
  "S010 1:51"
#guard out (body "let a = [1, 2]; a[0] = 3; return 0;") "f()" == "S010 1:33"
#guard out (body "let mut a = [1, 2]; a[0, 1] = 3; return 0;") "f()" == "S010 1:37"
#guard out (body "let mut a = 1; a[0] = 3; return 0;") "f()" == "S010 1:32"

/-!
Each step of the place charges 1 at its node before it applies. The update copies only the
containers on its path, so it charges nothing more. The statement and the step `[0]` charge 1
each, and the index `0` and the right side `5` charge 2 each. A reference on the right side pays its
copy: the name `b` charges 1, and its copy 3.
-/
#guard cost (body "let mut a = [1, 2]; a[0] = 5; return 0;") "f()" ==
  cost (body "let mut a = [1, 2]; return 0;") "f()" + 6
#guard cost (body "let mut a = [[1, 2]]; let b = [3, 4]; a[0] = b; return 0;") "f()" ==
  cost (body "let mut a = [[1, 2]]; let b = [3, 4]; return 0;") "f()" + 1 + 1 + 2 + 1 + 3

/-! Each selector `.N` charges 1: the statement, the three steps, and the right side add 6. -/
#guard cost (body "let mut a = ((1, (2, 3)), 4); a.0.1.0 = 5; return 0;") "f()" ==
  cost (body "let mut a = ((1, (2, 3)), 4); return 0;") "f()" + 1 + 3 + 2

/-!
The step `[1]` charges at its node `1:39` after the index `0` at `1:41` and before the index
`1`. The index `1`, the right side `5`, and `return 0;` charge 8 units after it.
-/
def twoSteps : String := body "let mut a = [[1, 2]]; a[0][1] = 5; return 0;"
#guard out twoSteps "f()" (cost twoSteps "f()" - 9) == "S015 1:39"
#guard out twoSteps "f()" (cost twoSteps "f()" - 10) == "S015 1:41"

/-!
A join charges 1 for each pair of container types that it visits. `[1, 2]` joins no container,
and `[[1], [2]]` visits one pair of arrays: it charges 1 more than the tuple `([1], [2])`. `==`
on two arrays joins their element types. The outer pair of the equality below visits one pair
of arrays, after the two literals and before the sum of the sizes.
-/
#guard cost "" "[[1], [2]]" == cost "" "([1], [2])" + 1
#guard exact "" "[[1], [2]] == [[1], [2]]" (1 + 2 * cost "" "[[1], [2]]" + 1 + 10)

/-!
A type is a static value of type `Type`. `[T; N]` in an expression is a type. A type equality
charges the sum of the sizes: `Bool == Bool` charges its node, the two names, and 2.
`[UInt[8]; 4]` charges its node, 6 for `UInt[8]`, and 2 for `4`. Then it charges its size 4
and the three products of its metadata, 3.
-/
#guard out "" "Bool" == "(type bool)"
#guard out "" "Type" == "(type type)"
#guard out "" "[UInt[8]; 4]" == "(type (array (uint 8) 4))"
#guard out "" "[[Bool; 2]; 3]" == "(type (array (array bool 2) 3))"
#guard out "" "(Bool, Nat)" == "(tuple ((type bool) (type nat)))"
#guard out "" "[Bool, UInt[8]]" == "(array type ((type bool) (type (uint 8))))"
#guard out "" "[Bool; 2] == [Bool; 2]" == "(bool true)"
#guard out "" "[Bool; 2] != [Bool; 3]" == "(bool true)"
#guard exact "" "Bool == Bool" 5
#guard exact "" "[UInt[8]; 4]" 16
#guard out "" "[Bool; -1]" == "S012 1:8"
#guard out "" "[Bool; 2][0]" == "S007 1:1"
#guard out "" "[[Bool; 1]; 1]" (depth := 2) == "S015 1:1"

/-!
A tuple type charges its size and the sizes of the four integers of its metadata. Here these
are the node 1, the two names 2, the size 3, and the metadata 4.
-/
def body2 (s : String) : String := s!"fn f() -> Type \{ {s} }"
#guard out (body2 "type X = (Bool, UInt[8]); return X;") "f()" ==
  "(type (tuple (bool (uint 8))))"
#guard cost (body "type X = (Bool, Bool); return 0;") "f()" ==
  cost (body "type X = Bool; return 0;") "f()" + 9

/-!
A local of type `Type` is a static value and can be a type. A local that holds another value is
`S010` at the type name. An index of a local is `S007` in `Elab`.
-/
#guard out "fn f(comptime T: Type, x: T) -> T { return x; }" "f(UInt[8], 3)" == "(uint 8 3)"
#guard out "fn f(T: Type) -> Type { return [T; 2]; }" "f(Bool)" == "(type (array bool 2))"
#guard out "fn f(comptime T: Type) -> Type { let mut u = T; u = (T, T); return u; }" "f(Bool)" ==
  "S010 1:49"
#guard out "fn f(Bool: Nat, x: Bool) -> Int { return 0; }" "f(1, 2)" == "S010 1:20"
#guard out "fn f(comptime T: Type) -> Int { let x: T[2] = 0; return 0; }" "f(Bool)" == "S007 1:40"
#guard out "fn f(comptime T: Type) -> Int { let x = T[2]; return 0; }" "f(Bool)" == "S007 1:41"

/-!
A `type` item is a constant of type `Type`. It evaluates at its first use. A `type` statement
binds a local of type `Type`. A cycle of aliases is `S019` at the use in progress.
-/
def aliases : String :=
  "type T = UInt[8];
type U = V;
type V = U;
const C: Type = [T; 2];
" ++
  "fn f() -> T { type X = [T; 2]; let x: X = [1, 2]; return x[1]; }"
#guard out aliases "T" == "(type (uint 8))"
#guard out aliases "T == UInt[8]" == "(bool true)"
#guard out aliases "C" == "(type (array (uint 8) 2))"
#guard out aliases "f()" == "(uint 8 2)"
#guard out aliases "U" == "S019 3:10"
#guard out aliases "V" == "S019 2:10"

/-!
A struct type is a static value. Its identity is the struct item and its static arguments. The
first use charges the size of the struct type, evaluates the field types in the scope of the
struct, and charges the metadata. `P[8]` charges its node, its name, the argument 2, the size
2, the parameter type 1, the field types 6, and the metadata 2 + 4. A later use charges only
its node, its name, and its argument.
-/
def structs : String :=
  "struct P(comptime W: Nat) { a: UInt[W], b: Bool }
struct Q { p: P[8], q: [P[4]; 2] }
" ++
  "struct R { r: R }
struct A { b: B }
struct B { a: A }
" ++
  "struct L(comptime T: Type) { a: T }
struct S { a: X }
type X = S;
" ++
  "struct F(comptime W: Nat) { a: UInt[W - 1] }"
#guard out structs "P[8]" == "(type (struct root P ((int 8))))"
#guard out structs "Q" == "(type (struct root Q ()))"
#guard out structs "L[L[Bool]]" ==
  "(type (struct root L ((type (struct root L ((type bool)))))))"
#guard out structs "P[8] == P[8]" == "(bool true)"
#guard out structs "P[8] == P[9]" == "(bool false)"
#guard out structs "[P[8]; 2]" == "(type (array (struct root P ((int 8))) 2))"
#guard exact structs "P[8]" 19
#guard exact structs "P[8] == P[8]" 28
#guard out structs "P[-1]" == "S012 1:1"
#guard out structs "P[true]" == "S010 1:1"
#guard out structs "F[1]" == "S012 9:32"
#guard out structs "R" == "S019 3:15"
#guard out structs "A" == "S019 5:15"
#guard out structs "S" == "S019 8:10"

/-!
The struct chain of section 11.3, specialized from the innermost struct outward. `S_k` has the
depth `k + 2`. It runs at the exact depth, and one level above it gives `S015` at its use.
-/
def structChain (k : Nat) : String :=
  "struct S0 { a: Bool }
" ++
  String.join ((List.range k).map fun i => s!"struct S{i + 1} \{ a: S{i} }\n") ++
  "fn f() -> Int {\n" ++
  String.join ((List.range (k + 1)).map fun i => s!"  type T{i} = S{i};\n") ++ "  return 0;\n}"
#guard out (structChain 5) "f()" (depth := 7) == "(int 0)"
#guard out (structChain 5) "f()" (depth := 6) == "S015 13:13"

/-!
The chain of 300 acyclic structs of section 11.3. The first use specializes each struct in
turn, so the call and the 300 specializations nest 301 levels deep. One level below gives
`S015` at the use of the last struct.
-/
def structDeep (k : Nat) : String :=
  String.join ((List.range (k - 1)).map fun i => s!"struct S{i} \{ a: S{i + 1} }\n") ++
  s!"struct S{k - 1} \{ a: Bool }\n" ++ "fn f() -> Int { type X = S0; return 0; }"
#guard out (structDeep 300) "f()" (depth := 301) == "(int 0)"
#guard out (structDeep 300) "f()" (depth := 300) == "S015 299:18"

/-!
The loop `t = P[t];` of section 11.3. The type `t` nests its arguments, so each step adds 1 to
its depth. The loop runs at the exact depth, and one more step gives `S015` at the node `P[t]`.
-/
def nest (k : Nat) : String :=
  "struct P(comptime T: Type) { x: Bool }
" ++
  s!"fn f() -> Int \{\n  let mut t: Type = Bool;\n  comptime for i in 0..{k} \{\n" ++
  "    t = P[t];
  }
  return 0;
}"
#guard out (nest 9) "f()" (depth := 10) == "(int 0)"
#guard out (nest 10) "f()" (depth := 10) == "S015 5:9"

/-!
The doubling chain of section 11.3: each `S_k` has two fields of `S_(k-1)`, so its width is
`64 * 2^k`. The metadata stays cheap: each step charges 11 units while the four integers fit
one word, and 200 steps charge less than 3000 units.
-/
def wide (k : Nat) : String :=
  "struct S0 { a: UInt[64] }
" ++
  String.join ((List.range k).map fun i => s!"struct S{i + 1} \{ a: S{i}, b: S{i} }\n") ++
  "fn f() -> Int {\n" ++
  String.join ((List.range (k + 1)).map fun i => s!"  type T{i} = S{i};\n") ++ "  return 0;\n}"
#guard (List.range 50).all fun k => cost (wide (k + 1)) "f()" == cost (wide k) "f()" + 11
#guard cost (wide 200) "f()" < 3000
#guard out (wide 3) "S3" == "(type (struct root S3 ()))"

/-! Errors of the earlier passes come first, also in `EXPR`. -/
#guard out "const A: Nat = ;" "1" == "S001 1:16"
#guard out "" "x" == "S003 1:1"
#guard out "" "1 +" == "S001 1:4"
#guard out "" "UInt[8, 9]" == "S007 1:1"
#guard out "module M() { reg r: Bool = false; }" "M" == "S003 1:1"

end Silicon.Source.Test.Eval
