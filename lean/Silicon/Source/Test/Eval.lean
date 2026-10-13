-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli

/-!
These tests check the static evaluator at the boundary of `eval` and `cost`. They check each
operator with its boundary cases, the fit rule, the static faults, and the table of constants.
They also check the calls and the exact charges of the cost model at the budget limits.

The static containers of slice 2 come next. Their tests check the literals, the typed uses,
the index, the selector, and `len`. They also check the equality, the join, the depth bound,
and the nested doubling of section 11.3.

The types as values of slice 2 come next. Their tests check the type constructors with their
charges, the aliases, the table of struct specializations, and the struct cases of section 11.3.

The function types of slice 2 come next. Their tests check the type constructor with its
charge, the typed use, `==`, the join, the constructor, the index, and the hardware `if`.

The function names as values of slice 2 come last. Their tests check the charges of a name,
the generic functions and the builtins, the depth, and the flow through bindings, arguments,
returns, containers, and `==`.
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
#guard out program "fact" == "(function root fact)"
#guard out program "mask" == "S010 1:1"
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
A tuple type charges its size, then the sums of its metadata. The sums charge the sizes of the
four integers of each element, then the sizes of the four new integers. Here these are the node
1, the two names 2, the size 3, the reads 8, and the metadata 4, less the node of `Bool`.
-/
def body2 (s : String) : String := s!"fn f() -> Type \{ {s} }"
#guard out (body2 "type X = (Bool, UInt[8]); return X;") "f()" ==
  "(type (tuple (bool (uint 8))))"
#guard cost (body "type X = (Bool, Bool); return 0;") "f()" ==
  cost (body "type X = Bool; return 0;") "f()" + 17

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
2, the parameter type 1, the field types 6, and the metadata 8 + 4. A later use charges only
its node, its name, its argument, and its parameter type.
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
#guard exact structs "P[8]" 26
#guard exact structs "P[8] == P[8]" 37
#guard out structs "P[-1]" == "S012 1:1"
#guard out structs "P[true]" == "S010 1:1"
#guard out structs "F[1]" == "S012 9:32"
#guard out structs "R" == "S019 3:15"
#guard out structs "A" == "S019 5:15"
#guard out structs "S" == "S019 8:10"

/-!
The key of a specialization holds each argument after its typed use at its parameter type: the
normalized identity. Thus `N[8]` and `N[UInt[4](8)]` are one type. Each use pays the conversion
and gets its errors. A typed use at `Nat` does not convert a `UInt`.
-/
def norm : String :=
  "struct N(comptime W: UInt[4]) { a: Bool }
struct P(comptime W: Nat) { a: Bool }"
#guard out norm "N[8]" == "(type (struct root N ((uint 4 8))))"
#guard out norm "N[UInt[4](8)]" == "(type (struct root N ((uint 4 8))))"
#guard out norm "N[8] == N[UInt[4](8)]" == "(bool true)"
#guard exact norm "N[8] == N[8]" 42
#guard exact norm "N[8] == N[UInt[4](8)]" 50
#guard out norm "N[16]" == "S012 1:1"
#guard out norm "N[UInt[8](8)]" == "S010 1:1"
#guard out norm "P[UInt[4](8)]" == "S010 1:1"

/-!
A literal with `[]` as a struct argument takes the type of its parameter, as a module argument
does. This holds also for a nested literal and for a parameter type that depends on an earlier
argument. A literal of another shape is `S010` at the use.
-/
def empties : String :=
  "struct P(comptime X: [Bool; 0]) { a: Bool }
struct Q(comptime n: Nat, comptime X: [[Bool; 0]; n]) { a: Bool }"
#guard out empties "P[[]]" == "(type (struct root P ((array bool ()))))"
#guard out empties "P[[]] == P[[Bool; 0]()]" == "(bool true)"
#guard out empties "Q[1, [[]]]" ==
  "(type (struct root Q ((int 1) (array (array bool 0) ((array bool ()))))))"
#guard out empties "Q[2, [[]]]" == "S010 1:1"
#guard out empties "P[[[]]]" == "S010 1:1"

/-!
A use of a struct while its own parameter types evaluate is a cycle: `S019` at the use. This
holds also for a cycle of two structs through their parameter types.
-/
def paramCycle : String :=
  "struct P(comptime x: P[1]) { a: Bool }
struct A(comptime x: B[1]) { a: Bool }
struct B(comptime y: A[1]) { a: Bool }"
#guard out paramCycle "P[1]" == "S019 1:22"
#guard out paramCycle "A[1]" == "S019 3:22"

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
`64 * 2^k`. The metadata stays cheap: each step charges 17 units while the four integers fit
one word, and 200 steps charge less than 6000 units.
-/
def wide (k : Nat) : String :=
  "struct S0 { a: UInt[64] }
" ++
  String.join ((List.range k).map fun i => s!"struct S{i + 1} \{ a: S{i}, b: S{i} }\n") ++
  "fn f() -> Int {\n" ++
  String.join ((List.range (k + 1)).map fun i => s!"  type T{i} = S{i};\n") ++ "  return 0;\n}"
#guard (List.range 50).all fun k => cost (wide (k + 1)) "f()" == cost (wide k) "f()" + 17
#guard cost (wide 200) "f()" < 6000
#guard out (wide 3) "S3" == "(type (struct root S3 ()))"

/-!
A record constructor charges the copies of its arguments, the typed use of each field in
declaration order, and the size of the record. `P[8](1, true)` adds 12 units to `P[8]`: the call
1, the arguments 4, their copies 2, the conversion of `1` 2, and the size 3. A field type that
differs is `S010`, and a value that does not fit is `S012`. A field `.f` only refers, so it
charges its node. A missing field is `S010`.
-/
def recs : String :=
  "struct P(comptime W: Nat) { a: UInt[W], b: Bool }
struct Q { p: P[8], q: [P[4]; 2] }
struct E {}
struct T { t: Type }
type X = P[8];
"
#guard out recs "P[8](1, true)" == "(record (struct root P ((int 8))) ((uint 8 1) (bool true)))"
#guard exact recs "P[8](1, true)" 38
#guard exact recs "P[8](1, true).a" 39
#guard out recs "P[8](1, true).a" == "(uint 8 1)"
#guard out recs "X(1, true).b" == "(bool true)"
#guard out recs "T(Bool).t" == "(type bool)"
#guard out recs "E" == "(type (struct root E ()))"
#guard out recs "P[8](256, true)" == "S012 1:1"
#guard out recs "P[8](1, 2)" == "S010 1:1"
#guard out recs "P[8]([], true)" == "S010 1:1"
#guard out recs "P[8](1, true).c" == "S010 1:1"
#guard out recs "(1, 2).a" == "S010 1:1"
#guard out recs "X(1)" == "S007 1:1"
#guard out recs "[P[8](1, true), P[8](2, false)]" ==
  "(array (struct root P ((int 8))) " ++
  "((record (struct root P ((int 8))) ((uint 8 1) (bool true))) " ++
  "(record (struct root P ((int 8))) ((uint 8 2) (bool false)))))"

/-!
`==` on two records needs one struct type. The join of the two types charges as a type equality,
2 + 2 here. The operator then charges the sum of the sizes, 3 + 3. The second constructor uses
the done specialization.
-/
#guard out recs "P[8](1, true) == P[8](1, true)" == "(bool true)"
#guard out recs "P[8](1, true) != P[8](1, false)" == "(bool true)"
#guard exact recs "P[8](1, true) == P[8](1, true)" 67
#guard out recs "P[8](1, true) == P[4](1, true)" == "S010 1:1"
#guard out recs "P[8](1, true) == (1, true)" == "S010 1:1"
#guard out recs "P[8](1, true) < P[8](1, true)" == "S010 1:1"

/-!
`T()` is the zero of a hardware data type, also of a struct type. It charges its node and the
size of the zero from the metadata, before it exists. A type that is not hardware data is
`S010`, also a struct with a field that is not. A struct without fields is hardware data with no
bit. The zero checks its depth first: a record is one level deeper than its struct type.
-/
#guard out recs "Bool()" == "(bool false)"
#guard out recs "SInt[8]()" == "(sint 8 0)"
#guard out recs "Unit()" == "(unit)"
#guard out recs "[UInt[8]; 2]()" == "(array (uint 8) ((uint 8 0) (uint 8 0)))"
#guard out recs "P[8]()" == "(record (struct root P ((int 8))) ((uint 8 0) (bool false)))"
#guard out recs "E()" == "(record (struct root E ()) ())"
#guard out recs "Q()" ==
  "(record (struct root Q ()) ((record (struct root P ((int 8))) ((uint 8 0) (bool false))) " ++
  "(array (struct root P ((int 4))) " ++
  "((record (struct root P ((int 4))) ((uint 4 0) (bool false))) " ++
  "(record (struct root P ((int 4))) ((uint 4 0) (bool false)))))))"
#guard exact recs "Bool()" 3
#guard exact recs "P[8]()" 30
#guard out recs "Int()" == "S010 1:1"
#guard out recs "Type()" == "S010 1:1"
#guard out recs "T()" == "S010 1:1"
#guard out recs "[[UInt[8]; 1048576]; 1048576]()" == "S015 1:1"
#guard out recs "[[Bool; 1]; 1]()" (depth := 3) ==
  "(array (array bool 1) ((array bool ((bool false)))))"
#guard out recs "Q()" (depth := 4) == "S015 1:1"
#guard (out recs "Q()" (depth := 5)).startsWith "(record"

/-!
`data_bits(T)` charges its node, its name, and the size of the width: the metadata of `T` holds
the width. A value that is not a type and a type that is not hardware data are `S010`.
-/
#guard out recs "data_bits(Q)" == "(int 19)"
#guard out recs "data_bits([P[3]; 3])" == "(int 12)"
#guard out recs "data_bits(E)" == "(int 0)"
#guard out recs "data_bits(Unit)" == "(int 0)"
#guard exact recs "data_bits(P[8])" 29
#guard out recs "data_bits(T)" == "S010 1:1"
#guard out recs "data_bits(Int)" == "S010 1:1"
#guard out recs "data_bits(1)" == "S010 1:1"

/-! `T.data_bits()` binds its receiver to `T`, the parameter without `comptime`. -/
#guard out recs "Q.data_bits()" == "(int 19)"
#guard out recs "Int.data_bits()" == "S010 1:1"

/-!
A field is a step of a place. Each step charges 1 before it applies. The right side is a typed
use at the type of the field. Thus `q.p.b = false;` costs 4 units more than an empty block: the
statement 1, the two steps 2, and the literal 2, without the block 1. An error of a step or of
the typed use is at 6:32, where the statement and its target start.
-/
def place (s : String) : String :=
  recs ++ s!"fn f() -> Q \{ let mut q = Q(); {s} return q; }"
#guard out (place "q.q[1].b = true; q.p.a = 300 - 45;") "f()" ==
  "(record (struct root Q ()) ((record (struct root P ((int 8))) ((uint 8 255) (bool false))) " ++
  "(array (struct root P ((int 4))) " ++
  "((record (struct root P ((int 4))) ((uint 4 0) (bool false))) " ++
  "(record (struct root P ((int 4))) ((uint 4 0) (bool true)))))))"
#guard cost (place "q.p.b = false;") "f()" == cost (place "{ }") "f()" + 4
#guard out (place "q.p.a = 256;") "f()" == "S012 6:32"
#guard out (place "q.p.b = 1;") "f()" == "S010 6:32"
#guard out (place "q.r = 1;") "f()" == "S010 6:32"
#guard out (place "q.p = P[4](1, true);") "f()" == "S010 6:32"

/-! Errors of the earlier passes come first, also in `EXPR`. -/
#guard out "const A: Nat = ;" "1" == "S001 1:16"
#guard out "" "x" == "S003 1:1"
#guard out "" "1 +" == "S001 1:4"
#guard out "" "UInt[8, 9]" == "S007 1:1"
#guard out "module M() { reg r: Bool = false; }" "M" == "S003 1:1"

/-!
Strings (section 5.1). `+` joins two strings and charges the sum of their sizes: 1 for the
node, 4 for each literal, and 6 for the join. No ordering takes a string.
-/
#guard out "" "\"ab\" + \"cd\"" == "(string \"abcd\")"
#guard exact "" "\"ab\" + \"cd\"" 15
#guard out "" "\"a\" == \"a\"" == "(bool true)"
#guard out "" "\"a\" != \"b\"" == "(bool true)"
#guard out "" "\"a\" < \"b\"" == "S010 1:1"
#guard out "" "\"a\" * \"b\"" == "S010 1:1"
#guard out "" "\"a\" + 1" == "S010 1:1"
#guard out "" "String" == "(type string)"
#guard out "comptime fn f(s: String) -> String { return s + \"!\"; }" "f(\"a\")" ==
  "(string \"a!\")"
#guard out "comptime fn f() -> String { let mut s = \"a\"; s = s + \"b\"; return s; }" "f()" ==
  "(string \"ab\")"
#guard out "comptime fn f() -> String { let s: String = 1; return s; }" "f()" == "S010 1:29"

/-!
`s[i]` gives a string with the scalar `i` of `s`. It charges the size of `s` after the type of
the index and before its range. The units are 1 for the node, 7 for the literal, 2 for the
index, and 6 for the scan. Thus a fuel of 11 fails at the charge, and 12 reaches the range check.
-/
#guard out "" "\"héllo\"[1]" == "(string \"é\")"
#guard exact "" "\"héllo\"[1]" 16
#guard out "" "\"abc\"[UInt[8](2)]" == "(string \"c\")"
#guard out "" "\"abc\"[3]" == "S013 1:7"
#guard out "" "\"abc\"[-1]" == "S013 1:7"
#guard out "" "\"abc\"[true]" == "S010 1:7"
#guard out "" "\"abc\"[5]" (fuel := 11) == "S015 1:1"
#guard out "" "\"abc\"[5]" (fuel := 12) == "S013 1:7"

/-! `len(s)` counts the scalars and charges the size of `s` before the scan. -/
#guard out "" "len(\"héllo\")" == "(int 5)"
#guard out "" "len(\"\")" == "(int 0)"
#guard exact "" "len(\"abc\")" 11

/-!
`str(n)` gives the decimal form of an `Int`. It charges the copy of `n`, the square of its
size, and the size of the result. Thus `str(-5)` charges 4 for `-5`, then 1, 1, and 3.
-/
#guard out "" "str(-5)" == "(string \"-5\")"
#guard exact "" "str(-5)" 11
#guard out "" "str(1 << 64)" == "(string \"18446744073709551616\")"
#guard exact "" "str(1 << 64)" (cost "" "1 << 64" + 2 + 2 + 4 + 21)
#guard out "" "str(UInt[8](1))" == "S010 1:1"
#guard out "" "str(\"a\")" == "S010 1:1"

/-!
`List[T]` is a type with the size 1 plus `T`. `list(T)` makes an empty list. It charges its
node, the callee, the copy of `T`, and 1 for the list.
-/
#guard out "" "List[Int]" == "(type (list int))"
#guard exact "" "List[Int]" 5
#guard out "" "List" == "S007 1:1"
#guard out "" "List[1]" == "S010 1:1"
#guard out "" "list(Int)" == "(list int ())"
#guard exact "" "list(Int)" 5
#guard out "" "list(1)" == "S010 1:1"
#guard out "" "List[List[Int]]" (depth := 2) == "S015 1:1"
#guard out "" "list(List[Int])" (depth := 2) == "S015 1:1"

/-! The list functions on a `let mut` place, each on its own line. -/
def lists : String :=
  "comptime fn f() -> List[Int] { let mut xs = list(Int); push(xs, 1); push(xs, 2); " ++
    "return xs; }\n" ++
  "comptime fn g() -> Int { let mut xs = list(Int); push(xs, 7); return pop(xs); }\n" ++
  "comptime fn h() -> Int { let mut xs = list(Int); return pop(xs); }\n" ++
  "comptime fn i() -> List[Int] { let mut xs = f(); xs[0] = 5; return xs; }\n" ++
  "comptime fn u() -> List[UInt[8]] { let mut xs = list(UInt[8]); push(xs, 1); return xs; }\n" ++
  "comptime fn v() -> Int { let mut xs = list(UInt[8]); push(xs, 300); return 0; }\n" ++
  "comptime fn w() -> Int { let mut xs = list(Int); push(xs, true); return 0; }\n" ++
  "comptime fn a() -> Int { let mut x = 1; push(x, 1); return 0; }\n" ++
  "comptime fn t() -> (List[Int], Int) { let mut t = (list(Int), 1); push(t.0, 3); return t; }\n" ++
  "comptime fn d() -> Int { let mut xs = list(Type); push(xs, List[List[Int]]); return 0; }\n" ++
  "comptime fn e() -> List[[Int; 0]] { let mut xs = list([Int; 0]); push(xs, []); return xs; }\n"

/-!
`push` and `pop` change the list place. `pop` of an empty list is `S013` at the call. `push`
makes the typed use of its element, and a value that does not fit is `S012` at the call.
-/
#guard out lists "f()" == "(list int ((int 1) (int 2)))"
#guard out lists "g()" == "(int 7)"
#guard out lists "h()" == "S013 3:57"
#guard out lists "u()" == "(list (uint 8) ((uint 8 1)))"
#guard out lists "v()" == "S012 6:54"
#guard out lists "w()" == "S010 7:50"
#guard out lists "a()" == "S010 8:41"
#guard out lists "t()" == "(tuple ((list int ((int 3))) (int 1)))"
#guard out lists "e()" == "(list (array int 0) ((array int ())))"

/-!
`f()` costs 31 units: the call 2, its result type 5, its body block 1, the `let` 6, each `push`
6, and the `return` 5. Each `push` costs its statement 1, its node 1, its callee 1, the literal
2, and the size of the element 1.
-/
#guard exact lists "f()" 31
#guard exact lists "g()" 21

/-! The new depth of a list comes from the element alone. -/
#guard out lists "d()" (depth := 3) == "S015 10:51"
#guard out lists "d()" (depth := 4) == "(int 0)"

/-!
The new depth of the root counts the steps of the place. Here the list is two tuples deep, so
the push makes the root 5 deep: the limit 5 passes, and 4 fails at the call.
-/
def deepList : String :=
  "comptime fn d() -> Int { let mut t = ((list(Type),),); push(t.0.0, List[Int]); return 0; }\n"
#guard out deepList "d()" (depth := 5) == "(int 0)"
#guard out deepList "d()" (depth := 4) == "S015 1:56"

/-!
A `mut` write-back checks the new depth of the root as `push` does. The push in `add` makes its
list 3 deep. The write-back adds the two steps of the place. Thus the limit 5 passes, and 4 fails
at the call.
-/
def deepBack : String :=
  "comptime fn add(mut xs: List[Type]) -> () { push(xs, List[Int]); return (); }\n" ++
  "comptime fn d() -> Int { let mut t = ((list(Type),),); add(t.0.0); return 0; }\n"
#guard out deepBack "d()" (depth := 5) == "(int 0)"
#guard out deepBack "d()" (depth := 4) == "S015 2:56"

/-! `len` and an index refer to a list. An index of a list is also a step of a place. -/
#guard out lists "len(f())" == "(int 2)"
#guard out lists "f()[1]" == "(int 2)"
#guard out lists "f()[2]" == "S013 1:5"
#guard out lists "i()" == "(list int ((int 5) (int 2)))"

/-!
`==` on two lists joins their element types. Two lists of different lengths are unequal. No
ordering takes a list. An array of lists joins the list types.
-/
#guard out lists "f() == f()" == "(bool true)"
#guard out lists "f() == list(Int)" == "(bool false)"
#guard out lists "f() == u()" == "(bool false)"
#guard out lists "list(Int) == list(Bool)" == "S010 1:1"
#guard out lists "f() < f()" == "S010 1:1"
#guard out lists "[f(), list(Int)]" ==
  "(array (list int) ((list int ((int 1) (int 2))) (list int ())))"
#guard out "" "[(\"a\", 1)]" == "(array (tuple (string int)) ((tuple ((string \"a\") (int 1)))))"

/-!
A receiver call binds its receiver at the first parameter without `comptime`, and it charges as
its plain call. The receiver evaluates first, so its `S013` comes before the `S013` of the
argument. The prelude functions take a receiver too.
-/
def calls : String :=
  "fn f(comptime n: Int, x: Int) -> Int { return n * 10 + x; }\n" ++
  "fn g() -> Int { let a = 3; return a.f(7); }\n" ++
  "fn h() -> Int { let a = 3; return f(7, a); }\n" ++
  "fn p() -> Int { return [1][5].f(1 / 0); }\n" ++
  "fn q() -> Int { let mut xs = list(Int); xs.push(4); xs.push(5); let y = xs.pop(); " ++
    "return y + xs.len(); }\n" ++
  "fn r() -> UInt[4] { return UInt[8](3).resize(UInt[4]); }\n" ++
  "fn s() -> String { return 12.str(); }\n"
#guard out calls "g()" == "(int 73)"
#guard cost calls "g()" == cost calls "h()"
#guard out calls "p()" == "S013 4:28"
#guard out calls "q()" == "(int 6)"
#guard out calls "r()" == "(uint 4 3)"
#guard out calls "s()" == "(string \"12\")"

/-!
A `mut` actual copies its place into the formal. At the return, the final value of the formal
goes back into the place, also through steps of the place and through a receiver. The place
has the type of the formal, else `S010` at the call. A `comptime fn` writes back its static
value.
-/
def muts : String :=
  "fn inc(mut x: Int) -> () { x = x + 1; return (); }\n" ++
  "fn two(mut x: Int, mut y: [Int; 2]) -> Int { x = x + y[0]; y[1] = 9; return x; }\n" ++
  "comptime fn ct(mut x: Int) -> Int { x = 2; return 0; }\n" ++
  "fn k() -> Int { let mut a = 1; inc(a); a.inc(); return a; }\n" ++
  "fn l() -> [Int; 2] { let mut a = [1, 2]; inc(a[1]); return a; }\n" ++
  "fn m() -> Int { let mut a: Nat = 1; inc(a); return a; }\n" ++
  "fn o() -> (Int, [Int; 2]) { let mut a = 5; let mut b = [1, 2]; let r = two(a, b); " ++
    "return (a, b); }\n" ++
  "fn u() -> Int { let mut a = 1; let z = ct(a); return a; }\n"
#guard out muts "k()" == "(int 3)"
#guard out muts "l()" == "(array int ((int 1) (int 3)))"
#guard out muts "m()" == "S010 6:37"
#guard out muts "o()" == "(tuple ((int 6) (array int ((int 1) (int 9)))))"
#guard out muts "u()" == "(int 2)"

/-!
A `mut` actual charges the copy in and the write-back, but its root name charges no node. With
a value of size 2, the call thus costs one unit more than the call with a copy only.
-/
def keep : String :=
  "fn keep(mut x: Int) -> () { return (); }\n" ++
  "fn id(x: Int) -> () { return (); }\n" ++
  "fn a() -> Int { let mut a = 18446744073709551616; keep(a); return 0; }\n" ++
  "fn b() -> Int { let mut a = 18446744073709551616; id(a); return 0; }\n"
#guard cost keep "a()" == cost keep "b()" + 1

/-!
A mutation of a held root charges the size of the root before the change (section 5.4). In
`a()`, the argument `xs` waits while `xs.pop()` evaluates, so the `pop` charges the size 3 of
the list `[1, 2]`, and the copy of `xs` is 1 unit larger than in `b()`. In `b()`, `xs` evaluates
after the `pop`, so nothing holds it. The index in `c()` reads the list before the `pop`.
-/
def holds : String :=
  "fn firstl(a: List[Int], b: Int) -> Int { return len(a); }\n" ++
  "fn secondl(b: Int, a: List[Int]) -> Int { return len(a); }\n" ++
  "fn mk() -> List[Int] { let mut xs = list(Int); xs.push(1); xs.push(2); return xs; }\n" ++
  "fn a() -> Int { let mut xs = mk(); return firstl(xs, xs.pop()); }\n" ++
  "fn b() -> Int { let mut xs = mk(); return secondl(xs.pop(), xs); }\n" ++
  "fn c() -> Int { let mut xs = mk(); return xs[xs.pop() - 1]; }\n"
#guard out holds "a()" == "(int 2)"
#guard out holds "b()" == "(int 1)"
#guard out holds "c()" == "(int 2)"
#guard cost holds "a()" == cost holds "b()" + 4

/-!
An assignment to a place with a step checks the new depth of the root, as `push` does. The
depth is the steps of the place plus the depth of the value. Each case makes a root 4 deep, by
an index, a `.N` selector, a field, and two steps. Thus the limit 4 passes, and 3 fails at the
assignment.
-/
def assigns : String :=
  "struct R { f: Type }\n" ++
  "comptime fn a() -> Int { let mut xs = list(Type); xs.push(Int); " ++
    "xs[0] = List[List[Int]]; return 0; }\n" ++
  "comptime fn b() -> Int { let mut t = (Int, 0); t.0 = List[List[Int]]; return 0; }\n" ++
  "comptime fn c() -> Int { let mut r = R(Int); r.f = List[List[Int]]; return 0; }\n" ++
  "comptime fn m() -> Int { let mut t = (list(Type), 0); t.0.push(Int); " ++
    "t.0[0] = List[Int]; return 0; }\n"
#guard ["a()", "b()", "c()", "m()"].all fun e => out assigns e (depth := 4) == "(int 0)"
#guard out assigns "a()" (depth := 3) == "S015 2:65"
#guard out assigns "b()" (depth := 3) == "S015 3:48"
#guard out assigns "c()" (depth := 3) == "S015 4:46"
#guard out assigns "m()" (depth := 3) == "S015 5:70"

/-!
A function type is a type. Its parameter types evaluate, then its result type. It charges its
node, its parts, and its size, and a `mut` mark is one more node of the size. `fn () -> Bool`
charges 1, 1 for `Bool`, and the size 2. `fn (fn () -> Bool) -> UInt[8]` charges 1, 4, 6 for
`UInt[8]`, and the size 5. A function type checks its depth: `fn () -> Bool` is 2 deep.
-/
#guard out "" "fn () -> Bool" == "(type (fn () bool))"
#guard out "" "fn (Bool, mut UInt[8]) -> (Bool, Nat)" ==
  "(type (fn (bool (mut (uint 8))) (tuple (bool nat))))"
#guard out "const C: Type = fn (mut [Bool; 2]) -> Bool;" "C" ==
  "(type (fn ((mut (array bool 2))) bool))"
#guard out "fn f(T: Type) -> Type { return fn (T) -> T; }" "f(Bool)" == "(type (fn (bool) bool))"
#guard exact "" "fn () -> Bool" 4
#guard exact "" "fn (Bool) -> Bool" 6
#guard exact "" "fn (mut Bool) -> Bool" 7
#guard exact "" "fn (fn () -> Bool) -> UInt[8]" 16
#guard out "" "fn () -> Bool" (depth := 2) == "(type (fn () bool))"
#guard out "" "fn () -> Bool" (depth := 1) == "S015 1:1"

/-! A function type in a type charges as in an expression: 1, 1, 1, and the size 4. -/
def fnBody (s : String) : String := s!"fn f() -> Bool \{ {s} }"
#guard cost (fnBody "type X = fn (mut Bool) -> Bool; return true;") "f()" ==
  cost (fnBody "type X = Bool; return true;") "f()" + 6

/-!
A typed use at a function type needs a function of that exact type, also in the `mut` marks.
It charges nothing. Another value is `S010` at the typed use.
-/
def fnG : Value := .function "g" #[] .bool
def typedFn (t : Ty) (v : Value) : String :=
  match Eval.convertLeaf t v with
  | .ok s => match s.run () with
    | .ok w => s!"{w.serialize} {s.charge}"
    | .error (c, _) => s!"{c}"
  | .error (c, _) => s!"{c}"
#guard typedFn (.fn #[] .bool) fnG == "(function root g) 0"
#guard typedFn (.fn #[.mk true .bool] .bool) (.function "g" #[.mk true .bool] .bool) ==
  "(function root g) 0"
#guard typedFn (.fn #[.mk true .bool] .bool) (.function "g" #[.mk false .bool] .bool) == "S010"
#guard typedFn (.fn #[] .bool) (.bool true) == "S010"
#guard typedFn .bool fnG == "S010"
#guard out (fnBody "let x: fn () -> Bool = true; return x;") "f()" == "S010 1:18"

/-!
A unary operator on a function type is `S010` at the operator, before its charge. A constructor
of a function type is `S010` at the call, after its callee and before its arguments, also with
a wrong number of arguments.
-/
#guard out "" "-fn () -> Bool" 5 == "S010 1:1"
#guard out "" "-fn () -> Bool" 4 == "S015 1:2"
#guard out "" "(fn () -> Bool)()" == "S010 1:1"
#guard out "" "(fn () -> Bool)(1)" == "S010 1:1"
#guard out "" "(fn () -> Bool)(1, 2, 3)" 5 == "S010 1:1"
#guard out "" "(fn () -> Bool)(1, 2, 3)" 4 == "S015 1:2"

/-!
`==` and `!=` are `S010` at the operator when the type of an operand holds a function type. The
check comes after both operands and before the join and the charge of the operator: the two
operands use 19 units here. Two function types are types, so they compare and charge the sum of
their sizes.
-/
def fnEq : String := "list(fn () -> Bool) == list(fn () -> Bool)"
#guard out "" fnEq 19 == "S010 1:1"
#guard out "" fnEq 18 == "S015 1:24"
#guard out "" "list(fn () -> Bool) != 1" == "S010 1:1"
#guard out (fnBody "let a: [fn () -> Bool; 0] = []; return a == a;") "f()" == "S010 1:57"
#guard out (fnBody "let a: [fn () -> Bool; 0] = []; return (1, [a]) != (1, [a]);") "f()" ==
  "S010 1:57"
#guard out "" "(fn () -> Bool) == (fn () -> Bool)" == "(bool true)"
#guard out "" "(fn () -> Bool) == (fn (mut Bool) -> Bool)" == "(bool false)"
#guard exact "" "(fn () -> Bool) == (fn () -> Bool)" 13

/-!
A join of two function types charges as a type equality, the sum of the two sizes. The two
types are equal, also in their `mut` marks, else the join fails: `S010` at the literal. The
array below charges 1 for the pair of lists and 4 for the pair of function types more than the
tuple.
-/
def fnLists (t u : String) : String := s!"[list({t}), list({u})]"
#guard out "" (fnLists "fn () -> Bool" "fn () -> Bool") ==
  "(array (list (fn () bool)) ((list (fn () bool) ()) (list (fn () bool) ())))"
#guard cost "" (fnLists "fn () -> Bool" "fn () -> Bool") ==
  cost "" "(list(fn () -> Bool), list(fn () -> Bool))" + 5
#guard out "" (fnLists "fn () -> Bool" "fn (mut Bool) -> Bool") == "S010 1:1"
#guard out "" (fnLists "fn (Bool) -> Bool" "fn (mut Bool) -> Bool") == "S010 1:1"

/-!
An index of a function type in a local is `S007` in pass 5, at the index, in an expression and
in a type.
-/
#guard out (fnBody "type T = fn () -> Bool; let x = T[8]; return true;") "f()" == "S007 1:50"
#guard out (fnBody "let T = fn () -> Bool; let x: T[8] = 1; return true;") "f()" ==
  "S007 1:48"

/-!
A hardware `if` with two function arms: one function item gives the static value, and two
different items are `S011` at the `if`. The pair charges as a static equality, 1 + 1, before the
comparison. A function and another value are `S010`.
-/
def fnArms (v w : Value) (fuel : Nat := 100) : String :=
  let p : Pos := ⟨1, 1⟩
  let c := Eval.Hw.mk p .bool (.lit (.bool true)) []
  match Eval.run { fuel } #[] (fun _ => Eval.mux p c (.static v) (.static w)) with
  | .ok (.static v, used) => s!"{v.serialize} {used}"
  | .ok _ => "hardware"
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
#guard fnArms fnG fnG == "(function root g) 2"
#guard fnArms fnG fnG 1 == "S015 1:1"
#guard fnArms fnG (.function "h" #[] .bool) == "S011 1:1"
#guard fnArms fnG (.function "h" #[] .bool) 1 == "S015 1:1"
#guard fnArms fnG (.bool true) == "S010 1:1"

/-!
A function name that is not a callee gives a function value. The name charges its node, then
the signature evaluates as type expressions, then the function type checks its depth and
charges its size. `g` charges 1, 1 for `Bool`, and the size 2. `k` charges 1, 1 for `Bool`, 1
for `Bool`, and the size 4. `h` charges 1, 4 for `fn () -> Bool`, 1 for `Bool`, and the size 4.
Each use evaluates the signature again.
-/
def fns : String :=
  "fn g() -> Bool { return true; }\n" ++
  "fn g2() -> Bool { return false; }\n" ++
  "fn k(mut b: Bool) -> Bool { return b; }\n" ++
  "fn h(x: fn () -> Bool) -> Bool { return true; }\n" ++
  "comptime fn c() -> Bool { return true; }\n" ++
  "fn gen(comptime n: Nat) -> Bool { return true; }\n" ++
  "const N: Nat = 2;\n" ++
  "fn a(x: [Bool; N]) -> Bool { return true; }\n"
#guard out fns "g" == "(function root g)"
#guard out fns "k" == "(function root k)"
#guard exact fns "g" 4
#guard exact fns "k" 7
#guard exact fns "h" 10
#guard exact fns "(g, g)" (1 + 4 + 4 + 3)
#guard cost fns "(g, g)" == cost fns "(true, true)" + 4

/-! The signature evaluates in the scope of the function, so it reads the items there. -/
#guard out fns "a" == "(function root a)"
#guard out fns "[a]" == "(array (fn ((array bool 2)) bool) ((function root a)))"

/-! A `comptime fn` gives a function value of the same function type. -/
#guard out fns "c" == "(function root c)"
#guard out fns "[g, c]" == "(array (fn () bool) ((function root g) (function root c)))"

/-!
A generic function and a builtin are `S010` at the name, after the charge of its node. The
signature does not evaluate.
-/
#guard out fns "gen" 1 == "S010 1:1"
#guard out fns "gen" 0 == "S015 1:1"
#guard out fns "len" 1 == "S010 1:1"
#guard out fns "len" 0 == "S015 1:1"
#guard out fns "(1, push)" == "S010 1:5"

/-!
The function type checks its depth at the name: `h` is 3 deep. The parameter type
`fn () -> Bool` is 2 deep, so it passes the depth 2, and the name fails.
-/
#guard out fns "h" (depth := 3) == "(function root h)"
#guard out fns "h" (depth := 2) == "S015 1:1"
#guard out fns "(1, h)" (depth := 2) == "S015 1:5"

/-!
A binding of a function name is not a copy: `let x = g;` charges as `let x = true;` with the
charges of `g` in place of 2 for `true`. A binding of a local that holds a function copies it:
the size 1. A typed use at the exact function type charges nothing more than its type.
-/
def fnLet (s : String) : String := fns ++ fnBody s
#guard out (fnLet "let x = g; return true;") "f()" == "(bool true)"
#guard cost (fnLet "let x = g; return true;") "f()" ==
  cost (fnLet "let x = true; return true;") "f()" + 2
#guard cost (fnLet "let x = g; let y = x; return true;") "f()" ==
  cost (fnLet "let x = g; return true;") "f()" + 3
#guard cost (fnLet "let x: fn () -> Bool = g; return true;") "f()" ==
  cost (fnLet "let x = g; return true;") "f()" + 4
#guard cost (fnLet "let x: fn (mut Bool) -> Bool = k; return true;") "f()" ==
  cost (fnLet "let x = k; return true;") "f()" + 7

/-!
A typed use needs the exact function type, also in the `mut` marks, else `S010` at the typed
use: a `let`, an assignment, an argument, and a return.
-/
#guard out (fnLet "let x: fn (Bool) -> Bool = k; return true;") "f()" == "S010 9:18"
#guard out (fnLet "let x: fn (mut Bool) -> Bool = g; return true;") "f()" == "S010 9:18"
#guard out (fnLet "let x: fn () -> Bool = c; return true;") "f()" == "(bool true)"
#guard out (fnLet "let x: Bool = g; return true;") "f()" == "S010 9:18"
#guard out (fnLet "let mut x = g; x = g2; return true;") "f()" == "(bool true)"
#guard out (fnLet "let mut x = g; x = k; return true;") "f()" == "S010 9:33"
#guard out fns "h(g)" == "(bool true)"
#guard out fns "h(c)" == "(bool true)"
#guard out fns "h(k)" == "S010 1:1"
#guard out (fns ++ "fn r() -> fn () -> Bool { return g2; }") "r()" == "(function root g2)"
#guard out (fns ++ "fn r() -> fn () -> Bool { return k; }") "r()" == "S010 9:27"
#guard out (fns ++ "fn r(x: fn () -> Bool) -> fn () -> Bool { return x; }") "r(g)" ==
  "(function root g)"

/-!
A function value is an element of an array, a tuple, and a list. The elements of an array join
their function types as a type equality: `[g, g2]` charges 2 + 2 for the join.
-/
#guard out fns "[g, g2]" == "(array (fn () bool) ((function root g) (function root g2)))"
#guard cost fns "[g, g2]" == cost fns "(g, g2)" + 4
#guard out fns "[g, k]" == "S010 1:1"
#guard out fns "(g, k)" == "(tuple ((function root g) (function root k)))"
#guard out (fnLet "let mut xs = list(fn () -> Bool); push(xs, g); push(xs, c); return true;")
  "f()" == "(bool true)"
#guard out (fns ++ "fn r() -> fn () -> Bool { let mut xs = list(fn () -> Bool); " ++
  "xs.push(g2); return xs.pop(); }") "r()" == "(function root g2)"
#guard out (fnLet "let mut xs = list(fn () -> Bool); push(xs, k); return true;") "f()" ==
  "S010 9:52"

/-!
`==` and `!=` are `S010` at the operator after both operands, before the charge: here the
operator charges 1 and each `g` charges 4.
-/
#guard out fns "g == g" 9 == "S010 1:1"
#guard out fns "g == g" 8 == "S015 1:6"
#guard out fns "[g] != [g]" == "S010 1:1"
#guard out fns "(1, g) == (1, g)" == "S010 1:1"

/-! A call through a function value is not supported yet: `S010` at the call, as a constructor. -/
#guard out (fnLet "let x = g; return x();") "f()" == "S010 9:36"

end Silicon.Source.Test.Eval
