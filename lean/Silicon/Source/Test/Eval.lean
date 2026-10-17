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

The function names as values of slice 2 come next. Their tests check the charges of a name,
the generic functions and the builtins, the depth, and the flow through bindings, arguments,
returns, containers, and `==`.

The calls through function values of slice 2 come next. Their tests check the charges, the
number of arguments, the callee rule, the `mut` actuals, and the wait of the callee.

The windows of the `mut` actuals at run time come last. Their tests check `S008` in pass 5
through function values, and its agreement with pass 4 on the calls of function items.
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

/-!
The size limit of section 5.4 (issue #255). A static integer has at most 2^32 bits. A string
has at most 2^32 bytes, and a list at most 2^32 elements. The check comes before the
charge, so the largest fuel cannot pay for a larger value. A value at the limit passes the
check, so a small fuel then fails at the charge.
-/
def said (src expr : String) (fuel : Nat) : String :=
  match Cli.evalText { budget := { fuel, depth := 1000 } } src expr with
  | .ok (v, _) => v.serialize
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col} {e.msg}"

def maxFuel : Nat := 2 ^ 64 - 1
def intLimit : String := s!"S015 1:1 {Eval.intLimitText}"

#guard Eval.limit == 4294967296
#guard !Eval.over Eval.limit && Eval.over (Eval.limit + 1)
#guard Eval.bitLength 0 == 0 && Eval.bitLength 1 == 1 && Eval.bitLength 255 == 8
#guard Eval.bitLength (-256) == 9

/-! `<<`: the repro of issue #255, with each sign of the operand. -/
#guard said "" "1 << 4294967296" maxFuel == intLimit
#guard said "" "-1 << 4294967296" maxFuel == intLimit
#guard said "" "3 << 4294967295" maxFuel == intLimit
#guard said "" "1 << 4294967295" 1000 ==
  "S015 1:1 the fuel cannot pay 67108864 unit(s); 995 remain; raise --fuel"
#guard said "" "0 << 18446744073709551616" maxFuel == "(int 0)"
#guard Eval.shlBits 1 (Eval.limit - 1) == Eval.limit && Eval.shlBits 0 (2 ^ 64) == 0

/-!
The other integer operators check a bound from the bit lengths of the operands. Operands at the
limit need a value of 2^32 bits, so these guards check the bounds and `capped` directly.
-/
def passes (b : Nat) : Bool := Eval.capped b ⟨0, fun _ => .ok .unit⟩ matches .ok _
#guard passes Eval.limit && !passes (Eval.limit + 1)
#guard Eval.intBound .add (Eval.limit - 1) 7 == Eval.limit
#guard Eval.intBound .sub Eval.limit 0 == Eval.limit + 1
#guard Eval.intBound .mul (2 ^ 31) (2 ^ 31) == Eval.limit
#guard Eval.intBound .mul (2 ^ 31) (2 ^ 31 + 1) == Eval.limit + 1
#guard Eval.intBound .and Eval.limit 1 == Eval.limit + 1
#guard Eval.intBound .or (Eval.limit - 1) 1 == Eval.limit
#guard Eval.intBound .xor 3 Eval.limit == Eval.limit + 1
#guard Eval.intBound .div Eval.limit Eval.limit == Eval.limit
#guard Eval.intBound .rem Eval.limit Eval.limit == Eval.limit
#guard said "" "~(1 << 4294967295)" 1000 ==
  "S015 1:3 the fuel cannot pay 67108864 unit(s); 994 remain; raise --fuel"
#guard out "" "(1 << 100) * (1 << 100) + ~7 - (5 ^ 3)" == out "" "(1 << 200) - 8 - 6"

/-!
`[T; N]`: the metadata products check the bound of `*`, with 1 more for the zero size. A large
length alone passes, because the zero of the type charges its size before it exists. A tuple
type checks a bound of its sums before they run (`sumBits`).
-/
def metaLimit : String := s!"S015 1:1 {Eval.metaLimitText}"
def zeroLimit : String := s!"S015 1:1 {Eval.zeroLimitText}"
#guard said "" "[Bool; 18446744073709551616]" maxFuel ==
  "(type (array bool 18446744073709551616))"
#guard (said "" "[Bool; 1 << 4294967296]" maxFuel) == s!"S015 1:8 {Eval.intLimitText}"
#guard said "" "[Bool; 18446744073709551616]()" maxFuel == zeroLimit
#guard said "" "[[Bool; 2305843009213693952]; 0]()" maxFuel ==
  "(array (array bool 2305843009213693952) ())"
#guard said "" "[[[(); 2305843009213693952]; 0]; 2]()" maxFuel ==
  "(array (array (array unit 2305843009213693952) 0) " ++
  "((array (array unit 2305843009213693952) ()) (array (array unit 2305843009213693952) ())))"
#guard Eval.arrayBits (Meta.finite 1) (2 ^ 32 - 1) == 32 + 2
#guard Eval.arrayBits ⟨2 ^ 70, 1, 1, 1, true, false, false⟩ 1 == 71 + 1
#guard Eval.arrayBits (Meta.finite 8) 4 == 3 + 4
#guard Eval.arrayBits Meta.unit 4 == 3 + 2
#guard Eval.metaBits (Meta.finite 8) == 4 && Eval.metaBits Meta.static == 1
#guard Eval.sumBits [Meta.finite 8, Meta.finite 8] == 4 + 2 && Eval.sumBits [] == 0
#guard Eval.sumBits [⟨2 ^ 70, 1, 1, 1, true, false, false⟩] == 71 + 1

/-!
A value that a type makes has a zero size of at most 2^32. A zero above it fails before its
charge, so the runtime never allocates it. A zero at the limit passes the check.
-/
#guard said "" "[Bool; 2305843009213693952]()" maxFuel == zeroLimit
#guard said "" "[[Bool; 65536]; 65536]()" maxFuel == zeroLimit
#guard (said "" "[Bool; 4294967295]()" 1000).startsWith "S015 1:1 the fuel cannot pay 4294967296"
#guard Eval.shlBits 1 (2 ^ 100) == Eval.limit + 1 && Eval.shlBits 1 Eval.limit == Eval.limit + 1
#guard said "" "1 << 340282366920938463463374607431768211456" maxFuel == intLimit
#guard out "" "\"\"" == "(string \"\")"
#guard said "" "data_bits([[UInt[65536]; 4294967296]; 4294967296])" maxFuel ==
  "(int 1208925819614629174706176)"

/-!
`s + t` checks the sum of the byte lengths, and `push` the length of the list plus 1. A value at
the limit needs 2^32 bytes or elements, so the guards check the small cases end to end.
-/
#guard out "" "\"ab\" + \"ü\"" == "(string \"abü\")"
#guard out "comptime fn f() -> Int { let mut xs = list(Int); push(xs, 1); return len(xs); }"
  "f()" == "(int 1)"

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

/-! The message of the first error of `eval`. Each budget message names its flag (section 6.2). -/
def msg (src expr : String) (fuel : Nat := 100000000) (depth : Nat := 1000) : String :=
  match Cli.evalOutcome { budget := { fuel, depth } } src expr with
  | .error e => e.msg
  | _ => "no error"

#guard msg deep "d(5)" (depth := 5) == "the nesting depth goes above 5; raise --depth"
#guard msg "" "1 << 4000000000" 1000 ==
  "the fuel cannot pay 62500001 unit(s); 995 remain; raise --fuel"
/-! The result of `eval` is the last charge, so its message names the fuel that suffices. -/
#guard cost "" "[1, 2]" == 8
#guard msg "" "[1, 2]" 18 ==
  "the fuel cannot pay 29 unit(s) of the result; 10 remain; raise --fuel to at least 37"
#guard msg "" "[1, 2]" 37 == "no error"

/-!
A chain of 300 acyclic constants. `eval` nests the 300 constants. The top selection nests one
level more, as section 11.3 states. The typed use of the argument evaluates the parameter type.
Thus the depth 301 passes, and 300 gives `S015`. The typed use belongs to the top selection, not
to `Top`. The argument converts to `UInt[300]`, a finite integer, so the emitted name is
`Top$5`.
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
  s!"total {cost chain "C299" + 122}\nTop$5 26\n"
#guard top chain "Top(5)" (depth := 300) == "S015 2:17"

/-!
`cost` covers the top selection: its arguments with their `instance` charge, its serialization
of 50 bytes, and its emitted name of 12 bytes. The parameter types charge at the top selection
too, and the size of each argument charges right after its typed use. The fuel 5 thus ends at
the size of `8`, and the fuel 6 ends at the type `Bool`. Then its instantiation charges its
body. The lowering charges 42: the module and its name 11, the domain ports 20, and the design
and its name 11.
-/
def counter : String := "module Counter(comptime W: Nat, comptime E: Bool) {\n}"
#guard top counter "Counter(8, true)" == "total 114\nCounter$8$1b 32\n"
#guard top counter "Counter(8, true)" (fuel := 5) == "S015 1:1"
#guard top counter "Counter(8, true)" (fuel := 6) == "S015 1:45"
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
#guard msg "fn f() -> Int { let a = [[[1]]]; return 0; }" "f()" (depth := 3) ==
  "the depth 4 goes above the nesting depth 3; raise --depth to at least 4"

/-!
A container holds hardware elements (section 5.1). A handle as an element is `S010` at the
element until slice 3. A hardware index is `S011` at the index.
-/
def hw (body : String) : String :=
  "module M(comptime N: Nat) {\n  input x: UInt[8];\n  output y: UInt[8];\n" ++
  "  reg r: UInt[8] = 0;\n" ++ body ++ "\n  r := x;\n  y := r;\n}\n"
#guard top (hw "  let t = (1, x);") "M(1)" == "total 146\nM$1 103\n"
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
at its own node.
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
An index that changes its own root charges the size of its result, and the result is a new value
(section 5.4). Each pair differs only in the local that the index changes: `t` or `u`. In `a()`,
the `push` charges the size 5 of the held root `t`, and the read charges the size 3 of the old
list `[1, 2]`. `v()` gives that old list. In `c()`, the binding of the result is not a copy, so
it charges only the held root more than `d()`, where the binding copies the list. `b()`, `d()`,
`f()`, and `h()` keep their charges. In `e()`, the inner and the outer read each charge 3, and the
`push` charges the held root once. In `g()`, each iteration charges the root and the list that
it holds then: 5 and 3, 6 and 4, 7 and 5. The cost line of `M` shows the 8 units of `a()`.
-/
def changes : String :=
  "fn mk() -> (Int, List[Int]) { let mut xs = list(Int); xs.push(1); xs.push(2); " ++
    "return (0, xs); }\n" ++
  "fn a() -> Int { let mut t = mk(); let mut u = mk(); t[(t.1.push(3), 1).1]; return 0; }\n" ++
  "fn b() -> Int { let mut t = mk(); let mut u = mk(); t[(u.1.push(3), 1).1]; return 0; }\n" ++
  "fn c() -> Int { let mut t = mk(); let mut u = mk(); " ++
    "let y = t[(t.1.push(3), 1).1]; return 0; }\n" ++
  "fn d() -> Int { let mut t = mk(); let mut u = mk(); " ++
    "let y = t[(u.1.push(3), 1).1]; return 0; }\n" ++
  "fn e() -> Int { let mut t = mk(); let mut u = mk(); " ++
    "t[(t[(t.1.push(3), 1).1], 1).1]; return 0; }\n" ++
  "fn f() -> Int { let mut t = mk(); let mut u = mk(); " ++
    "t[(t[(u.1.push(3), 1).1], 1).1]; return 0; }\n" ++
  "fn g() -> Int { let mut t = mk(); let mut u = mk(); " ++
    "comptime for i in 0..3 { t[(t.1.push(i), 1).1]; } return 0; }\n" ++
  "fn h() -> Int { let mut t = mk(); let mut u = mk(); " ++
    "comptime for i in 0..3 { t[(u.1.push(i), 1).1]; } return 0; }\n" ++
  "fn v() -> Int { let mut t = mk(); return len(t[(t.1.push(3), 1).1]); }\n" ++
  "module M() { output o: UInt[8]; o := UInt[8](a()); }\n" ++
  "module N() { output o: UInt[8]; o := UInt[8](b()); }\n"
#guard out changes "v()" == "(int 2)"
#guard exact changes "a()" 152
#guard exact changes "b()" 144
#guard exact changes "c()" 152
#guard exact changes "d()" 147
#guard exact changes "e()" 166
#guard exact changes "f()" 155
#guard exact changes "g()" 216
#guard exact changes "h()" 186
#guard top changes "M" == "total 226\nM 198\n"
#guard top changes "N" == "total 218\nN 190\n"

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
def fnG : Value := .function 0 "g" #[] .bool
def typedFn (t : Ty) (v : Value) : String :=
  match Eval.convertLeaf t v with
  | .ok s => match s.run () with
    | .ok w => s!"{w.serialize} {s.charge}"
    | .error (c, _) => s!"{c}"
  | .error (c, _) => s!"{c}"
#guard typedFn (.fn #[] .bool) fnG == "(function root g) 0"
#guard typedFn (.fn #[.mk true .bool] .bool) (.function 0 "g" #[.mk true .bool] .bool) ==
  "(function root g) 0"
#guard typedFn (.fn #[.mk true .bool] .bool) (.function 0 "g" #[.mk false .bool] .bool) == "S010"
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
#guard fnArms fnG (.function 1 "h" #[] .bool) == "S011 1:1"
#guard fnArms fnG (.function 1 "h" #[] .bool) 1 == "S015 1:1"
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
A function whose parameter type or result type names one of its parameters is generic too. It
is `S010` at the name, also when the type of `T` would be wrong (`d3`), because the signature
does not evaluate. A name of an item in the signature does not make a function generic.
-/
def gens : String :=
  "fn d(T: Type, x: T) -> T { return x; }\n" ++
  "fn d2(n: Nat) -> UInt[n] { return 0; }\n" ++
  "fn d3(T: Bool, x: [Bool; 1]) -> fn (T) -> Bool { return x; }\n" ++
  "fn d4(n: Nat, x: [Bool; n + 1]) -> Bool { return true; }\n" ++
  "const N: Nat = 2;\n" ++
  "fn a(x: UInt[N]) -> Bool { return true; }\n"
#guard out gens "d" 1 == "S010 1:1"
#guard out gens "d" 0 == "S015 1:1"
#guard out gens "d2" 1 == "S010 1:1"
#guard out gens "d3" 1 == "S010 1:1"
#guard out gens "(1, d4)" == "S010 1:5"
#guard out gens "a" == "(function root a)"
#guard out gens "d(Bool, true)" == "(bool true)"

/-!
The function type checks its depth at the name: `h` is 3 deep. The parameter type
`fn () -> Bool` is 2 deep, so it passes the depth 2, and the name fails.
-/
#guard out fns "h" (depth := 3) == "(function root h)"
#guard out fns "h" (depth := 2) == "S015 1:1"
#guard out fns "(1, h)" (depth := 2) == "S015 1:5"

/-!
Each depth check of the signature reports at the name: a parameter type of `p` and the result
type of `r` are 3 deep. A constant in the signature nests, so the type of `D`, 3 deep, reports
at its own node.
-/
def deepSig : String :=
  "fn p(x: fn () -> fn () -> Bool) -> Bool { return true; }\n" ++
  "fn r() -> fn () -> fn () -> Bool { return r; }\n" ++
  "const D: [[Bool; 1]; 1] = [[true]];\n" ++
  "fn q(x: [Bool; len(D)]) -> Bool { return true; }\n"
#guard out deepSig "p" (depth := 4) == "(function root p)"
#guard out deepSig "p" (depth := 2) == "S015 1:1"
#guard out deepSig "(1, r)" (depth := 2) == "S015 1:5"
#guard out deepSig "q" (depth := 3) == "(function root q)"
#guard out deepSig "q" (depth := 2) == "S015 3:10"

/-!
A signature can name its own function, here as an argument of a call in a parameter type. Each
evaluation of a signature takes a nesting level. Thus the cycle ends with `S015` at a name in
the cycle. The cycle is direct (`r`) or goes through a second function (`a` and `b`).
-/
def selfSig : String :=
  "fn k(h: fn (UInt[1]) -> Bool) -> Nat { return 1; }\n" ++
  "fn r(x: UInt[k(r)]) -> Bool { return true; }\n" ++
  fnBody "let v = r; return true;"
#guard out selfSig "f()" == "S015 2:16"
#guard out selfSig "f()" (depth := 3) == "S015 2:16"
def mutualSig : String :=
  "fn k(h: fn (UInt[1]) -> Bool) -> Nat { return 1; }\n" ++
  "fn a(x: UInt[k(b)]) -> Bool { return true; }\n" ++
  "fn b(x: UInt[k(a)]) -> Bool { return true; }\n" ++
  fnBody "let v = a; return true;"
#guard out mutualSig "f()" == "S015 2:16"
#guard out mutualSig "f()" (depth := 3) == "S015 3:16"

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

/-!
A call through a function value evaluates its callee once, then runs as a call of its item. It
charges as a named call: the callee charges as an expression, and no function name charges.
Thus `f(5, 2)` and `two(5, 2)` charge the same units.
-/
#guard out (fnLet "let x = g; return x();") "f()" == "(bool true)"
def viaFns : String :=
  "fn id(x: Bool) -> Bool { return x; }\n" ++
  "fn two(a: Int, b: Int) -> Int { return a - b; }\n" ++
  "fn inc(mut x: Int) -> Int { x = x + 1; return x; }\n" ++
  "comptime fn c(x: Int) -> Int { return x + 1; }\n" ++
  "fn sf(mut h: fn (Bool) -> Bool) -> Bool { h = id; return true; }\n" ++
  "fn st(mut t: Type) -> Nat { t = Bool; return 0; }\n" ++
  "fn ap(h: fn (Bool) -> Bool, x: Bool) -> Bool { return h(x); }\n"
def callIn (s : String) : String := viaFns ++ s!"fn f() -> Int \{ {s} }"
#guard out (callIn "let f = two; return f(5, 2);") "f()" == "(int 3)"
#guard cost (callIn "let f = two; return f(5, 2);") "f()" ==
  cost (callIn "let f = two; return two(5, 2);") "f()"
#guard out viaFns "ap(id, false)" == "(bool false)"
#guard out (callIn "let fs = [two, two]; return fs[1](7, 1);") "f()" == "(int 6)"
#guard out viaFns "(two)(1, 1)" == "(int 0)"

/-!
The number of arguments is `S007` at the call, after the charge of the callee and before the
arguments: `error` does not run. The fuel 15 stops at the callee.
-/
#guard out (callIn "let f = two; return f(5);") "f()" == "S007 8:37"
#guard out (callIn "let f = two; return f(5, 2, error(\"x\"));") "f()" == "S007 8:37"
#guard out (callIn "let f = two; return f(5);") "f()" 16 == "S007 8:37"
#guard out (callIn "let f = two; return f(5);") "f()" 15 == "S015 8:37"

/-! A callee that is neither a function nor a type is `S010` at the call. -/
#guard out (callIn "let f = 3; return f(5);") "f()" == "S010 8:35"
#guard out (callIn "return (1)(5);") "f()" == "S010 8:24"

/-! The type rule of the arguments holds as at a named call. -/
#guard out (callIn "let f = two; return f(true, 1);") "f()" == "S010 8:37"

/-! A `comptime fn` runs through its value. -/
#guard out (callIn "let f = c; return f(5);") "f()" == "(int 6)"

/-!
The `mut` marks of the function type select the `mut` actuals. The write-back runs as at a named
call, with the same charges. A `mut` actual that is not a place is `S008` at the argument.
-/
#guard out (callIn "let f = inc; let mut a = 1; let r = f(a); return a * 10 + r;") "f()" ==
  "(int 22)"
#guard cost (callIn "let f = inc; let mut a = 1; let r = f(a); return a;") "f()" ==
  cost (callIn "let f = inc; let mut a = 1; let r = inc(a); return a;") "f()"
#guard out (callIn "let f = inc; return f(3);") "f()" == "S008 8:39"

/-!
The callee waits while the arguments evaluate. A write-back to the local of the callee thus
charges the size of the local: 1 for a function, 2 for `UInt[8]`. Another callee local `e`
or `S` is not held, so its call charges 1 or 2 less.
-/
#guard cost (callIn "let mut f = id; let b = f(sf(f)); return 0;") "f()" -
    cost (callIn "let mut f = id; let b = sf(f); return 0;") "f()" ==
  cost (callIn "let mut f = id; let mut e = id; let b = e(sf(f)); return 0;") "f()" -
    cost (callIn "let mut f = id; let mut e = id; let b = sf(f); return 0;") "f()" + 1
#guard cost (callIn "let mut T = UInt[8]; let v = T(st(T)); return 0;") "f()" -
    cost (callIn "let mut T = UInt[8]; let v = st(T); return 0;") "f()" ==
  cost (callIn "let mut T = UInt[8]; let mut S = UInt[8]; let v = S(st(T)); return 0;") "f()" -
    cost (callIn "let mut T = UInt[8]; let mut S = UInt[8]; let v = st(T); return 0;") "f()" + 2

/-!
`S008` at run time (section 9.1). The `mut` marks of a call through a function value are known
only in pass 5. A `mut` actual whose root is pending in a window of the same frame is `S008` at
the start of the actual. Pass 4 accepts each of these programs, so pass 5 gives the error.
Each call opens windows: `push`, `pop`, a receiver call, a named call, and a call through a
value. An assignment opens a window too. Each value `vX` has a name as long as its function
`mX`. A named call and a call through its value thus have the same positions.
-/
def windows (s : String) : String :=
  "fn mo(mut a: List[Int]) -> Int { return a.len(); }\n" ++
  "fn mt(mut a: List[Int], mut b: List[Int]) -> Int { return 0; }\n" ++
  "fn mp(mut a: List[Int], b: Int) -> Int { return b; }\n" ++
  "fn mu(mut a: List[Int], b: ()) -> Int { return 0; }\n" ++
  "fn mq(b: Int, mut a: List[Int]) -> Int { return b; }\n" ++
  "fn mr(mut a: List[Int]) -> Int { let h = mo; a.push(7); return h(a); }\n" ++
  "fn f() -> Int {\nlet mut xs = list(Int); xs.push(1); xs.push(2); let mut ys = list(Int);\n" ++
  "let vo = mo; let vt = mt; let vp = mp; let vu = mu; let vq = mq; let vr = mr;\n" ++
  s ++ "\nreturn xs.len() * 10 + ys.len();\n}"

/-! The value of `f()` without pass 4. Pass 5 alone then decides `S008`. -/
def late (src : String) : String :=
  let r : Except Error (Value × Nat) := do
    let items ← Parse.parseSource Lex.maxSyntaxDepth src
    let e ← Resolve.resolveExpr items (← Parse.parseExpr Lex.maxSyntaxDepth "f()")
    Eval.evalExpr {} (← Resolve.resolve items) e
  match r with
  | .ok (v, _) => v.serialize
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"

/-! `g(xs, xs.pop())` with `g` a value: the receiver of `pop` is the second `mut` actual. -/
#guard out (windows "vp(xs, xs.pop());") "f()" == "S008 10:8"
#guard out (windows "vp(xs, pop(xs));") "f()" == "S008 10:12"
#guard out (windows "vu(xs, xs.push(1));") "f()" == "S008 10:8"
#guard out (windows "vu(xs, push(xs, 1));") "f()" == "S008 10:13"
#guard out (windows "vt(xs, xs);") "f()" == "S008 10:8"

/-! A `push` or a named call opens a window, and a call through a value in it conflicts. -/
#guard out (windows "xs.push(vo(xs));") "f()" == "S008 10:12"
#guard out (windows "push(xs, vo(xs));") "f()" == "S008 10:13"
#guard out (windows "mp(xs, vo(xs));") "f()" == "S008 10:11"
#guard out (windows "mp(xs, mp(ys, vo(xs)));") "f()" == "S008 10:18"

/-! A call through a value opens a window, and a named call or `pop` in it conflicts. -/
#guard out (windows "vp(xs, mo(xs));") "f()" == "S008 10:11"
#guard out (windows "vp(xs, vp(ys, xs.pop()));") "f()" == "S008 10:15"

/-! An assignment opens a window for the indices of its place and its right side. -/
#guard out (windows "xs[vo(xs) - 1] = 5;") "f()" == "S008 10:7"
#guard out (windows "xs[0] = vo(xs);") "f()" == "S008 10:12"

/-!
A root is pending only in its window, and only in its frame. An argument before the `mut`
actual, a call that ends before it, a read, and another root do not conflict. The callee `mr`
changes its own `mut` formal while the root `xs` of the caller is pending.
-/
#guard out (windows "vp(xs, ys.pop());") "f()" == "S013 10:8"
#guard out (windows "ys.push(3); vp(xs, ys.pop());") "f()" == "(int 20)"
#guard out (windows "vq(xs.pop(), xs);") "f()" == "(int 10)"
#guard out (windows "let a = mo(ys) + vo(xs) + vp(xs, xs.len());") "f()" == "(int 20)"
#guard out (windows "vt(xs, ys); vt(ys, xs);") "f()" == "(int 20)"
#guard out (windows "let a = vp(xs, vr(ys));") "f()" == "(int 21)"
#guard out (windows "ys.push(vo(xs)); xs[vo(ys) - 1] = 5;") "f()" == "(int 21)"

/-! The counters have no charge: a call through a value charges as the named call. -/
#guard cost (windows "let a = vp(xs, 1);") "f()" == cost (windows "let a = mp(xs, 1);") "f()"

/-!
Pass 4 and pass 5 agree on the calls of function items. A program that pass 4 rejects gives the
same error in pass 5 alone (`late`). The call through the value of the function then gives it
too. A program that pass 4 accepts runs the same in pass 5 alone.
-/
def agree (named value : String) (want : String) : Bool :=
  out (windows named) "f()" == want && late (windows named) == want &&
    out (windows value) "f()" == want
#guard agree "mp(xs, xs.pop());" "vp(xs, xs.pop());" "S008 10:8"
#guard agree "mt(xs, xs);" "vt(xs, xs);" "S008 10:8"
#guard agree "mu(xs, push(xs, 1));" "vu(xs, push(xs, 1));" "S008 10:13"
#guard agree "mp(xs, mo(xs));" "vp(xs, vo(xs));" "S008 10:11"
#guard agree "mq(xs.pop(), xs);" "vq(xs.pop(), xs);" "(int 10)"
#guard agree "mt(xs, ys); mt(ys, xs);" "vt(xs, ys); vt(ys, xs);" "(int 20)"
#guard out (windows "xs.push(xs.pop());") "f()" == "S008 10:9"
#guard late (windows "xs.push(xs.pop());") == "S008 10:9"
#guard out (windows "xs[0] = xs.pop();") "f()" == "S008 10:9"
#guard late (windows "xs[0] = xs.pop();") == "S008 10:9"
#guard out (windows "xs[xs.pop()] = 1;") "f()" == "S008 10:4"
#guard late (windows "xs[xs.pop()] = 1;") == "S008 10:4"

/-!
A field and a function item are found by number, not by name. Names with a long common prefix
still select their own field and call their own function. A field selection works in a
constant, an alias, a result type, and the top expression. A struct with a function argument
specializes once for each function.
-/
def prefixed : String :=
  let x := String.ofList (List.replicate 200 'a')
  s!"struct R \{ {x}1: UInt[8], {x}2: Bool }
struct H(comptime F: fn () -> Bool) \{ }
fn {x}y() -> Bool \{ return true; }
fn {x}z() -> Bool \{ return false; }
struct N \{ {x}3: Nat }
const C: R = R(7, true);
const D: N = N(5);
const W: UInt[8] = C.{x}1;
type A = UInt[D.{x}3];
fn g() -> UInt[D.{x}3] \{ return 3; }
fn f() -> Bool \{ let h = {x}z; return h(); }
"
def pre : String := String.ofList (List.replicate 200 'a')
#guard out prefixed s!"C.{pre}2" == "(bool true)"
#guard out prefixed "W" == "(uint 8 7)"
#guard out prefixed "A" == "(type (uint 5))"
#guard out prefixed "g()" == "(uint 5 3)"
#guard out prefixed "f()" == "(bool false)"
#guard out prefixed s!"H[{pre}y] == H[{pre}z]" == "(bool false)"
#guard out prefixed s!"H[{pre}y] == H[{pre}y]" == "(bool true)"

/-!
The form of a hardware aggregate (section 5.1). A name or a child output has the size of a
finite value of its type: 4 for `UInt[256]` and 1 for `Bool`. A node adds the sizes of its
operands. A reference has the zero size of its type and the depth of its zero, from the
metadata.
-/
def at1 : Pos := ⟨1, 1⟩
def wideRef : Eval.Hw := Eval.Hw.mk at1 (.uint 256) (.ref ⟨"p", []⟩) []
#guard wideRef.size == 4
#guard (Eval.Hw.mk at1 .bool (.out ⟨"u", []⟩ ⟨"q", []⟩) []).size == 1
#guard (Eval.Hw.mk at1 (.uint 256) (.un .inv) [wideRef]).size == 5
def boolLeaf : Eval.Agg := .hw (Eval.Hw.mk at1 .bool (.ref ⟨"b", []⟩) [])
def arrayRef : Eval.Agg := .ref (.name ⟨"r", []⟩) (.array (.uint 8) 4)
#guard arrayRef.size == 5 && arrayRef.depth == 2

/-!
A container node stores its type, its size, and its depth. A record counts the depth of its
struct type, here 5. A container without a hardware leaf is a static value.
-/
def mixed : Eval.Agg :=
  .mkTuple #[.bool, .int, .array (.uint 8) 4] #[boolLeaf, .static (.int 3), arrayRef]
#guard mixed.size == 8 && mixed.depth == 3
#guard (Eval.Val.agg mixed).text == "hardware (Bool, Int, [UInt[8]; 4])"
#guard (Eval.Agg.mkRecord (.struct 0 "P" #[] ⟨8, 1, 2, 5, true, false, false⟩)
  #[boolLeaf]).depth == 6
#guard match Eval.Agg.mkArray .int #[.static (.int 1), .static (.int 2)] with
  | .static v => v.serialize == "(array int ((int 1) (int 2)))"
  | _ => false

/-!
The normal form. A reference without a hardware leaf charges the zero size of its type, then it
is the static zero. The charge comes first, so a huge empty part fails before any work. A
reference of a scalar type is a hardware value, and another reference stays lazy with no charge.
-/
def normal (a : Eval.Agg) (fuel : Nat := 100) : String :=
  match Eval.run { fuel } #[] (fun _ => Eval.normalize at1 a) with
  | .ok (.static v, used) => s!"{v.serialize} {used}"
  | .ok (.hw h, used) => s!"hardware {h.ty.text} {h.size} {used}"
  | .ok (v, used) => s!"{v.text} {v.size} {used}"
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
#guard normal (.ref (.name ⟨"r", []⟩) (.array .unit 3)) == "(array unit ((unit) (unit) (unit))) 4"
#guard normal (.ref (.name ⟨"r", []⟩) (.array .unit 3)) 3 == "S015 1:1"
#guard normal (.ref (.name ⟨"r", []⟩) (.array .unit (2 ^ 40))) == "S015 1:1"
#guard normal (.ref (.name ⟨"r", []⟩) (.tuple #[.unit, .array .bool 0])) ==
  "(tuple ((unit) (array bool ()))) 3"
#guard normal (.ref (.out ⟨"u", []⟩ "q" []) (.uint 256)) == "hardware UInt[256] 4 0"
#guard normal arrayRef == "hardware [UInt[8]; 4] 5 0"

/-!
The selection on a hardware aggregate (section 5.4, "References"). A chain of steps runs on the
local `x`. Step `k` has its node at `9:(k + 2)`, and its literal, field name, or index name at
`10:(k + 2)`. The local `h` is a hardware `UInt[2]`, the index of `hix`. The result shows the
part, whether it refers, and the units of the chain alone.
-/
inductive Step where
  | idx (k : Nat)
  | hix
  | dot (k : Nat)
  | fld (f : String)

def stepNode (k : Nat) : Pos := ⟨9, k + 2⟩
def stepArg (k : Nat) : Pos := ⟨10, k + 2⟩

def chainOf (steps : List Step) : Resolve.Expr :=
  steps.zipIdx.foldl (init := .name ⟨9, 1⟩ "x" (.local 0)) fun b (s, k) =>
    match s with
    | .idx i => .index (stepNode k) b [.num (stepArg k) i]
    | .hix => .index (stepNode k) b [.name (stepArg k) "h" (.local 1)]
    | .dot i => .select (stepNode k) b (stepArg k) i
    | .fld f => .field (stepNode k) b ⟨stepArg k, f⟩

def fieldsOf (steps : List Step) : List (Pos × String) :=
  steps.zipIdx.filterMap fun | (.fld f, k) => some (stepArg k, f) | _ => none

def opText : Eval.Op → String
  | .ref p => Names.encode p.name
  | .out i q => s!"{Names.encode i.name}.{Names.encode q}"
  | .word m o => s!"{Names.encode (m.push (.role .rdata)).name}@{o}"
  | _ => ""

/-!
A child output base keeps its fields in reverse order, and its leaf puts them in order once. Thus
the leaf of `u.q[1].a[0]` has the core name `u.q$1e$a$0e`.
-/
#guard opText ([Names.Field.elem 1, .user "a", .elem 0].foldl
  (fun b f => Eval.Base.sub (fun _ => none) .unit 0 f b) (.out ⟨"u", []⟩ "q" [])).op ==
  "u.q$1e$a$0e"

def describe : Eval.Val → String
  | .static v => v.serialize
  | .hw (.node _ t s op []) => s!"hw {t.text} {opText op} {s}"
  | .agg a@(.ref b t) => s!"ref {t.text} {opText b.op} {a.size}"
  | v => v.text

/-!
The result of the chain `steps` on `x`. `ty` is a type expression after the items of `src`.
`base` makes the value of `x` from the context and that type.
-/
def sel (src ty : String) (base : Eval.Ctx → Ty → Eval.Val) (steps : List Step)
    (fuel : Nat := 1000000) : String :=
  let e := chainOf steps
  let r : Except Error (String × Nat) := do
    let (items, checked) ← Cli.load 4096 src
    let te ← Resolve.resolveExpr items (← Parse.parseExpr 4096 ty)
    let ((d, used), _) ← Eval.run { fuel } checked (top := { fields := fieldsOf steps }) fun n =>
      withReader (fun c => { c with item := checked.size }) do
        let t ← match ← Eval.eval n te with
          | some ⟨.static (.type t), _, _⟩ => pure t
          | _ => Eval.fail .S010 ⟨0, 0⟩ "a type"
        Eval.bindLocal 0 ⟨none, false, base (← read) t⟩
        Eval.bindLocal 1 ⟨none, false, .hw (.mk ⟨0, 0⟩ (.uint 2) (.ref ⟨"h", []⟩) [])⟩
        let f0 := (← get).fuel
        let o ← Eval.need e (← Eval.eval n e)
        return (s!"{describe o.value} {o.ref}", f0 - (← get).fuel)
    return (d, used)
  match r with
  | .ok (d, used) => s!"{d} {used}"
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"

def shapes : String :=
  "struct P { a: UInt[8], z: [Unit; 1099511627776], t: (Bool, [UInt[4]; 3]), e: [Unit; 3] }\n" ++
  "struct Q { a: UInt[8], b: Int }\ntype T2 = (Bool, UInt[8]);\n" ++
  "type E = [([Unit; 2], Bool); 1099511627776];\n"

/-! A register `r` of the type `t`. -/
def regOf (t : Ty) : Eval.Val := .handle (.res .reg 0 t ⟨"r", []⟩)
def reg (_ : Eval.Ctx) (t : Ty) : Eval.Val := regOf t

/-!
An implicit read of an aggregate register gives a lazy reference with no charge. A scalar read
stays a hardware name. A name of a register without a step is the handle. Each step on a
reference gives a reference to the part with its leaf field: `.f` adds `f`, and an index or a
selector adds `<k>e`. The chain charges only its nodes and its literals: a name 1, a step 1,
and a literal 2. A reference has the zero size of its type.
-/
#guard sel shapes "P" reg [.fld "a"] == "hw UInt[8] r$a 1 true 2"
#guard sel shapes "P" reg [.fld "t"] == "ref (Bool, [UInt[4]; 3]) r$t 6 true 2"
#guard sel shapes "P" reg [.fld "t", .dot 1, .idx 2] == "hw UInt[4] r$t$1e$2e 1 true 6"
#guard sel shapes "P" reg [.fld "t", .idx 0] == "hw Bool r$t$0e 1 true 5"
#guard sel shapes "UInt[8]" reg [] == "a register true 1"
#guard sel shapes "UInt[8]" reg [.idx 0] == "S010 9:2"

/-!
A reference keeps its work in proportion to its steps. An index of a reference to a huge array
takes the units of an index of a small array, and it never expands the array. The length check
reads the type.
-/
#guard sel "" "[UInt[8]; 1099511627776]" reg [.idx 1099511627775] ==
  "hw UInt[8] r$1099511627775e 1 true 4"
#guard sel "" "[[UInt[8]; 1099511627776]; 1099511627776]" reg [.idx 7, .idx 9] ==
  "hw UInt[8] r$7e$9e 1 true 7"
#guard sel "" "[UInt[8]; 4]" reg [.idx 3] == "hw UInt[8] r$3e 1 true 4"
#guard sel "" "[UInt[8]; 1099511627776]" reg [.idx 1099511627776] == "S013 10:2"
#guard sel shapes "T2" reg [.dot 2] == "S013 10:2"
#guard sel shapes "T2" reg [.idx 1] == "hw UInt[8] r$1e 1 true 4"

/-!
A hardware index of a reference is `S011` at the index, before the container check. A field of
a reference to an array, or a selector of a reference to an array, is `S010`.
-/
#guard sel "" "[UInt[8]; 4]" reg [.hix] == "S011 10:2"
#guard sel "" "UInt[8]" reg [.hix] == "S011 10:2"
#guard sel "" "[UInt[8]; 4]" reg [.dot 0] == "S010 9:2"
#guard sel shapes "[UInt[8]; 4]" reg [.fld "a"] == "S010 9:2"
#guard sel shapes "P" reg [.fld "y"] == "S010 9:2"

/-!
A part without a hardware leaf is a new static value. It charges its zero size from the metadata
before it exists, so a huge empty part fails with `S015` at the step before any work. It does not
refer, so a binding of it is not a copy. A whole read of a register without a hardware leaf is
a static value too, so a huge empty register fails at its read.
-/
#guard sel shapes "P" reg [.fld "e"] == "(array unit ((unit) (unit) (unit))) false 6"
#guard sel shapes "P" reg [.fld "z"] == "S015 9:2"
#guard sel shapes "E" reg [.idx 5, .dot 0] == "(array unit ((unit) (unit))) false 8"
#guard sel "" "[[Unit; 2]; 1099511627776]" reg [.idx 5] == "S015 9:2"

/-!
A child output of an aggregate type is a reference to the output. Its parts append their leaf
fields to the port name.
-/
def child (c : Eval.Ctx) (t : Ty) : Eval.Val :=
  let k := (c.field (stepArg 0)).getD 0
  let ports := ({} : Std.HashMap Nat Eval.Port).insert k ⟨"q", k, false, t, ⟨1, 1⟩⟩
  .handle (.inst 0 ⟨"u", []⟩ ⟨⟨"C", []⟩, ports, 0, none⟩)
#guard sel shapes "P" child [.fld "q"] == "ref P u.q 1099511627789 true 2"
#guard sel shapes "P" child [.fld "q", .fld "t", .dot 1, .idx 2] ==
  "hw UInt[4] u.q$t$1e$2e 1 true 7"
#guard sel shapes "[Unit; 3]" child [.fld "q"] == "(array unit ((unit) (unit) (unit))) false 6"
#guard sel shapes "Bool" child [.fld "q"] == "hw Bool u.q 1 true 2"

/-!
A container node of an aggregate refers to its element, which keeps its normal form. A static
element stays static and refers.
-/
def node (_ : Eval.Ctx) (t : Ty) : Eval.Val :=
  match t with
  | .struct .. => .agg (.mkRecord t #[boolLeaf, .static (.int 3)])
  | _ => .agg (.mkTuple #[.bool, .int, .array (.uint 8) 4] #[boolLeaf, .static (.int 3), arrayRef])
#guard sel shapes "Q" node [.fld "a"] == "hw Bool b 1 true 2"
#guard sel shapes "Q" node [.fld "b"] == "(int 3) true 2"
#guard sel shapes "Q" node [.fld "c"] == "S010 9:2"
#guard sel "" "Bool" node [.dot 1] == "(int 3) true 2"
#guard sel "" "Bool" node [.idx 2, .idx 1] == "hw UInt[8] r$1e 1 true 7"
#guard sel "" "Bool" node [.dot 2] == "ref [UInt[8]; 4] r 5 true 2"
#guard sel "" "Bool" node [.dot 3] == "S013 10:2"
#guard sel "" "Bool" node [.idx 3] == "S013 10:2"

/-! `len` of a reference reads its type, so a huge array charges nothing. -/
def lenText (v : Eval.Val) : String :=
  match Eval.run {} #[] (fun _ => Eval.lenOf at1 [v]) with
  | .ok (v, used) => s!"{v.serialize} {used}"
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
#guard lenText (regOf (.array (.uint 8) (2 ^ 40))) == "(int 1099511627776) 0"
#guard lenText (.agg (.mkArray .bool #[boolLeaf, .static (.bool true)])) == "(int 2) 0"
#guard lenText (regOf (.tuple #[.bool, .bool])) == "S010 1:1"

/-!
The typed use of a hardware aggregate (section 5.4). A name of a leaf prints as its core name. A
part of a node prints in brackets.
-/
def nameText : Eval.Hw → String
  | .node _ _ _ (.ref p) [] => Names.encode p.name
  | .node _ t _ (.word m o) [] => s!"{opText (.word m o)}:{t.info.width}"
  | .node _ _ _ (.lit v) [] => v.serialize
  | .node _ t _ _ _ => s!"hardware {t.text}"

mutual
  def aggText : Eval.Agg → String
    | .static v => v.serialize
    | .hw h => nameText h
    | .ref b _ => s!"ref {opText b.op}"
    | .array _ ⟨xs⟩ | .tuple _ ⟨xs⟩ | .record _ ⟨xs⟩ => s!"[{aggTexts xs}]"

  def aggTexts : List Eval.Agg → String
    | [] => ""
    | [x] => aggText x
    | x :: xs => s!"{aggText x}, {aggTexts xs}"
end

def valText : Eval.Val → String
  | .agg a => aggText a
  | .hw h => nameText h
  | v => v.text

/-! The core `let` statements of the named bindings: each core name with its value. -/
def letsText (ls : Array Eval.Let) (shown : Eval.Hw → String := nameText) : String :=
  " ".intercalate (ls.toList.map fun l => s!"{Names.encode l.path.name}={shown l.value}")

def tupleAliases : String :=
  "type A = (Bool, UInt[4]);\ntype B = (Bool, Nat);\ntype C = (UInt[1], Nat);\n" ++
  "type D = (Nat, UInt[1]);\ntype E = (Bool, UInt[8]);\n" ++
  "type F = (Bool, [UInt[8]; 4], UInt[4]);\n" ++
  "struct Q { a: Bool }\n"

/-!
The typed use of `v` at the type expression `ty` after the items of `src`. The result shows the
value and the units of the typed use alone, with the fuel `fuel` for it.
-/
def typedUse (src ty : String) (v : Ty → Eval.Val) (fuel : Nat := 1000) : String :=
  let r : Except Error String := do
    let (items, checked) ← Cli.load 4096 src
    let te ← Resolve.resolveExpr items (← Parse.parseExpr 4096 ty)
    let ((d, used), _) ← Eval.run { fuel := fuel + 100 } checked fun n =>
      withReader (fun c => { c with item := checked.size }) do
        let t ← match ← Eval.eval n te with
          | some ⟨.static (.type t), _, _⟩ => pure t
          | _ => Eval.fail .S010 ⟨0, 0⟩ "a type"
        modify fun s => { s with fuel }
        let x ← Eval.conformVal at1 t (v t)
        return (valText x, fuel - (← get).fuel)
    return s!"{d} {used}"
  match r with
  | .ok s => s
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"

def refR (t : Ty) : Eval.Val := .agg (.ref (.name ⟨"r", []⟩) t)
def pair (t : Ty) (x : Value) : Eval.Val := .agg (.mkTuple #[.bool, t] #[boolLeaf, .static x])

/-!
A reference checks by its type in one step and never expands. Thus a typed use of a reference to
a huge array at its own type takes no unit, and another type is `S010` before any charge.
-/
#guard typedUse "" "[UInt[8]; 1099511627776]" refR 0 == "ref r 0"
#guard typedUse "" "[UInt[4]; 4]" (fun _ => refR (.array (.uint 8) 4)) 0 == "S010 1:1"

/-!
Another aggregate checks each part first: a hardware leaf needs the type of its position
(`S010`), and a static leaf its sign (`S012`). The first failing part in the walk order reports,
before the charge. Then the conversion charges the size of the value plus the size of the result,
here 3 + 3. Then a static leaf converts and checks its fit (`S012`), after the charge. A
reference part keeps its form and counts its zero size, here 5, in both sizes.
-/
#guard typedUse tupleAliases "A" (fun _ => pair .int (.int 3)) == "[b, (uint 4 3)] 6"
#guard typedUse tupleAliases "B" (fun _ => pair .int (.int (-1))) 0 == "S012 1:1"
#guard typedUse tupleAliases "C" (fun _ => pair .int (.int (-1))) 0 == "S010 1:1"
#guard typedUse tupleAliases "D"
  (fun _ => .agg (.mkTuple #[.int, .bool] #[.static (.int (-1)), boolLeaf])) 0 == "S012 1:1"
#guard typedUse tupleAliases "E" (fun _ => pair .int (.int 300)) == "S012 1:1"
#guard typedUse tupleAliases "E" (fun _ => pair .int (.int 300)) 5 == "S015 1:1"
#guard typedUse tupleAliases "F" (fun _ => .agg (.mkTuple #[.bool, .array (.uint 8) 4, .int]
  #[boolLeaf, .ref (.name ⟨"r", []⟩) (.array (.uint 8) 4), .static (.int 3)])) ==
  "[b, ref r, (uint 4 3)] 16"

/-! A record needs its own struct type, and it converts nothing. -/
#guard typedUse tupleAliases "Q" (fun t => .agg (.mkRecord t #[boolLeaf])) 0 == "[b] 0"
#guard typedUse tupleAliases "Q"
  (fun _ => .agg (.mkRecord (.struct 5 "R" #[] ⟨1, 1, 2, 2, true, false, false⟩) #[boolLeaf])) 0 ==
  "S010 1:1"

/-!
The copy of a register charges 1 for the handle. A read of an aggregate register is a reference,
so its copy also charges the zero size of its type. A huge one thus fails before any leaf exists.
A scalar read charges only the handle, as in slice 1. A read without a hardware leaf makes a new
static value with the charge of its zero size.
-/
def copyRead (t : Ty) (fuel : Nat := 100) : String :=
  match Eval.run { fuel } #[] (fun _ => Eval.copyUse at1 t true (regOf t)) with
  | .ok (v, used) => s!"{valText v} {used}"
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
#guard copyRead (.array (.uint 8) 4) == "ref r 6"
#guard copyRead (.array (.uint 8) (2 ^ 40)) == "S015 1:1"
#guard copyRead (.uint 256) == "r 1"
#guard copyRead (.array .unit 3) == "[Unit; 3] 5"

/-!
The body of the function `f` of `src`. Its first parameter `x` is a mutable local with the value
`base`, and it took its first core name, as a copy-in does. The result shows the core `let`
statements, the final value of `x`, and the units of the body alone.
-/
def runF (src : String) (base : Ty → Eval.Val) (fuel : Nat := 1000000)
    (shown : Eval.Hw → String := nameText) : String :=
  let r : Except Error String := do
    let (_, checked) ← Cli.load 4096 src
    let some i := checked.findIdx? fun | .fn _ _ u .. => u.name == "f" | _ => false
      | .error ⟨.S010, at1, "no function f"⟩
    let some (.fn _ _ _ (q :: _) _ ss) := checked[i]? | .error ⟨.S010, at1, "no parameter"⟩
    let ((d, used), _) ← Eval.run { fuel := fuel + 1000 } checked fun n =>
      withReader (fun c => { c with item := i, ret := some .bool }) do
        let t ← Eval.typeExpr n q.ty
        Eval.bindLocal q.name.id ⟨some t, true, base t⟩
        let _ ← Eval.fresh q.name.id q.name.name.name
        modify fun s => { s with fuel }
        for s in ss do
          if let some _ ← Eval.stmt n s then break
        let st ← get
        let x := (st.frame[q.name.id]?).map (valText ·.value)
        return (s!"{letsText st.naming.lets shown} | {x.getD "-"}", fuel - st.fuel)
    return s!"{d} | {used}"
  match r with
  | .ok s => s
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"

def refX (t : Ty) : Eval.Val := .agg (.ref (.name ⟨"x", []⟩) t)
def leafX (k : Nat) : Eval.Agg := .hw (.mk at1 (.uint 8) (.ref ⟨"x", [.elem k]⟩) [])
def assignIn (t : String) (s : String) : String :=
  s!"fn f(mut x: {t}) -> Bool \{\n  {s}\n  return true;\n}\n"

/-!
A place update can give a new root with a hardware leaf. It then binds each hardware leaf of the
root again, at the next version of the root (section 7.3). The static leaf `7` gets no core
name. The assignment charges 1, its step 1, the index 2, the value 2, and its conversion 2. The
rebind charges 5: the old size 5, minus the part 1, plus the new part 1. `return true;` charges
4.
-/
#guard runF (assignIn "[UInt[8]; 4]" "x[1] = 7;") refX ==
  "x$1v$0e=x$0e x$1v$2e=x$2e x$1v$3e=x$3e | [x$1v$0e, (uint 8 7), x$1v$2e, x$1v$3e] | 17"
#guard runF (assignIn "[UInt[8]; 4]" "x[1] = 7;") refX 12 == "S015 2:3"
#guard runF (assignIn "[UInt[8]; 4]" "x[1] = 7;") refX 13 == "S015 3:3"

/-!
The rebind charges from the stored sizes before the path copies and before the reference root
expands. Thus a huge root fails at the assignment before any work on its elements.
-/
#guard runF (assignIn "[UInt[8]; 1 << 40]" "x[5] = 7;") refX == "S015 2:3"

/-!
Only the references on the path expand, one level for each step. The part `x[0]` stays a
reference, and its binding refers to its new name.
-/
#guard runF (assignIn "[[UInt[8]; 2]; 2]" "x[1][0] = x[0][1];") refX ==
  "x$1v$0e$0e=x$0e$0e x$1v$0e$1e=x$0e$1e x$1v$1e$0e=x$0e$1e x$1v$1e$1e=x$1e$1e | " ++
  "[ref x$1v$0e, [x$1v$1e$0e, x$1v$1e$1e]] | 26"

/-!
A new root without a hardware leaf is a static value with no rebind charge. A static part of an
aggregate root takes a static value and keeps the other leaves. A static part that takes a
hardware value opens one level, and the root binds again.
-/
#guard runF (assignIn "(UInt[8], Int)" "x.0 = 5;")
  (fun _ => .agg (.mkTuple #[.uint 8, .int] #[leafX 0, .static (.int 3)])) ==
  " | (UInt[8], Int) | 10"
def staticPart (t : Ty) : Eval.Val :=
  .agg (.mkTuple #[.uint 8, t] #[leafX 0, .static (.array (.uint 8) #[.uint 8 1, .uint 8 2])])
#guard runF (assignIn "(UInt[8], [UInt[8]; 2])" "x.1[0] = 9;") staticPart ==
  "x$1v$0e=x$0e | [x$1v$0e, (array (uint 8) ((uint 8 9) (uint 8 2)))] | 18"
#guard runF (assignIn "(UInt[8], [UInt[8]; 2])" "x.1[0] = x.0;") staticPart ==
  "x$1v$0e=x$0e x$1v$1e$0e=x$0e | [x$1v$0e, [x$1v$1e$0e, (uint 8 2)]] | 17"

/-!
A new root without a hardware leaf makes the empty parts of each reference on the path static
values. The update charges the zero size of each such part from the type metadata, at the place
of the rebind charge, before the part exists. On `(UInt[8], [(); 3])`, `x.0 = 5;` charges 10, and
4 of it is the zero size of `[(); 3]`. `return true;` charges 4. On `(UInt[8], ())` the empty part
has the zero size 1, so the total is 11.
With 9 units the assignment fails, and with 10 the `return` fails. Each reference on a path of two
steps charges its own empty parts: 3 for `[(); 2]` and 4 for `[(); 3]`. A huge empty part fails
at the charge before any work on its elements.
-/
#guard runF (assignIn "(UInt[8], ())" "x.0 = 5;") refX == " | (UInt[8], Unit) | 11"
#guard runF (assignIn "(UInt[8], [(); 3])" "x.0 = 5;") refX == " | (UInt[8], [Unit; 3]) | 14"
#guard runF (assignIn "(UInt[8], [(); 3])" "x.0 = 5;") refX 9 == "S015 2:3"
#guard runF (assignIn "(UInt[8], [(); 3])" "x.0 = 5;") refX 10 == "S015 3:3"
#guard runF (assignIn "((UInt[8], [(); 3]), [(); 2])" "x.0.0 = 5;") refX ==
  " | ((UInt[8], [Unit; 3]), [Unit; 2]) | 18"
#guard runF (assignIn "(UInt[8], [(); 1 << 40])" "x.0 = 5;") refX == "S015 2:3"

/-!
A binding takes one version, and each hardware leaf gets one core `let`. A typed binding and an
assignment without a step read a reference by its leaves.
-/
#guard runF (assignIn "[UInt[8]; 2]" "let y: [UInt[8]; 2] = x;\n  x = y;") refX ==
  "y$0e=x$0e y$1e=x$1e x$1v$0e=y$0e x$1v$1e=y$1e | ref x$1v | 30"

/-!
An argument, a call result, and a `mut` write-back bind by leaf (section 7.3). The result puts
its role `0ret` in the place of a name, with no version, and the leaves follow it. A loop adds
its frame, so no two names are equal.
-/
def aggCalls : String :=
  "struct S { a: UInt[8], b: Bool }\nfn g(a: S) -> S {\n  return a;\n}\n" ++
  "fn f(mut x: S) -> Bool {\n  let y = g(x);\n  comptime for i in 0..2 {\n" ++
  "    let z = g(y);\n  }\n  return true;\n}\n"
#guard runF aggCalls refX ==
  "g$0c$a$a=x$a g$0c$a$b=x$b g$0c$0ret$a=g$0c$a$a g$0c$0ret$b=g$0c$a$b y$a=g$0c$0ret$a " ++
  "y$b=g$0c$0ret$b i$0$g$1c$a$a=y$a i$0$g$1c$a$b=y$b i$0$g$1c$0ret$a=i$0$g$1c$a$a " ++
  "i$0$g$1c$0ret$b=i$0$g$1c$a$b i$0$z$a=i$0$g$1c$0ret$a i$0$z$b=i$0$g$1c$0ret$b " ++
  "i$1$g$1c$a$a=y$a i$1$g$1c$a$b=y$b i$1$g$1c$0ret$a=i$1$g$1c$a$a " ++
  "i$1$g$1c$0ret$b=i$1$g$1c$a$b i$1$z$a=i$1$g$1c$0ret$a i$1$z$b=i$1$g$1c$0ret$b | ref x | 60"

/-! The `results` guard of `Test.Elab` for aggregate results: no version, and no two equal. -/
def callNames : List Names.Name :=
  ((runF aggCalls refX).splitOn " ").filterMap fun w => Names.decode ((w.splitOn "=").head!)
def retLeaves : List Names.Name := callNames.filter (·.rest.contains (.role .ret))
#guard retLeaves.length == 6
#guard retLeaves.all fun p => !p.rest.any fun | .version _ => true | _ => false
#guard retLeaves.all fun p => (p.rest.dropWhile (· != .role .ret)).length == 2
#guard callNames.eraseDups.length == callNames.length

/-!
A `mut` write-back binds the final value of the formal to the next version of the caller root.
The update of the formal rebinds it in the frame of the call first.
-/
#guard runF ("fn g(mut a: [UInt[8]; 2]) -> Bool {\n  a[0] = 1;\n  return true;\n}\n" ++
  "fn f(mut x: [UInt[8]; 2]) -> Bool {\n  let b = g(x);\n  return b;\n}\n") refX ==
  "g$0c$a$0e=x$0e g$0c$a$1e=x$1e g$0c$a$1v$1e=g$0c$a$1e x$1v$1e=g$0c$a$1v$1e | " ++
  "[(uint 8 1), x$1v$1e] | 45"

/-! A list holds no value with a hardware leaf: `push` of an aggregate is `S011` at the element. -/
#guard runF (assignIn "[UInt[8]; 2]" "let mut l = list([UInt[8]; 2]);\n  l.push(x);") refX ==
  "S011 3:10"
def listPart (_ : Ty) : Eval.Val :=
  .agg (.mkTuple #[.uint 8, .list (.uint 8)] #[leafX 0, .static (.list (.uint 8) #[])])
/-!
`push` into a static list part of an aggregate root keeps the names of its leaves. The change
refreshes each container node on the path. Thus `push` and `pop` charge the part count of each
node, after the element and before a held root (section 5.4). `x.1.push(5);` charges 11, and 2 of it
is the part count of the root. The root of width 3 charges 3 instead. A nested root charges 2 for
its root and 2 for its part, and its extra step charges 1. `return true;` charges 4.
-/
#guard runF (assignIn "(UInt[8], List[UInt[8]])" "x.1.push(5);") listPart ==
  " | [x$0e, (list (uint 8) ((uint 8 5)))] | 15"
def wideList (_ : Ty) : Eval.Val :=
  .agg (.mkTuple #[.uint 8, .bool, .list (.uint 8)]
    #[leafX 0, .static (.bool true), .static (.list (.uint 8) #[.uint 8 7])])
def nested (_ : Ty) : Eval.Val :=
  .agg (.mkTuple #[.tuple #[.uint 8, .list (.uint 8)], .bool]
    #[.mkTuple #[.uint 8, .list (.uint 8)] #[leafX 0, .static (.list (.uint 8) #[])],
      .static (.bool true)])
#guard runF (assignIn "(UInt[8], List[UInt[8]])" "x.1.push(5);") listPart 11 == "S015 3:3"
#guard runF (assignIn "(UInt[8], List[UInt[8]])" "x.1.push(5);") listPart 10 == "S015 2:3"
#guard runF (assignIn "(UInt[8], Bool, List[UInt[8]])" "x.2.push(5);") wideList ==
  " | [x$0e, (bool true), (list (uint 8) ((uint 8 7) (uint 8 5)))] | 16"
#guard runF (assignIn "(UInt[8], Bool, List[UInt[8]])" "x.2.push(5);") wideList 12 == "S015 3:3"
#guard runF (assignIn "(UInt[8], Bool, List[UInt[8]])" "x.2.push(5);") wideList 11 == "S015 2:3"
#guard runF (assignIn "(UInt[8], Bool, List[UInt[8]])" "let y = x.2.pop();") wideList ==
  " | [x$0e, (bool true), (list (uint 8) ())] | 12"
#guard runF (assignIn "((UInt[8], List[UInt[8]]), Bool)" "x.0.1.push(5);") nested ==
  " | [[x$0e, (list (uint 8) ((uint 8 5)))], (bool true)] | 18"
#guard runF (assignIn "((UInt[8], List[UInt[8]]), Bool)" "x.0.1.push(5);") nested 14 == "S015 3:3"
#guard runF (assignIn "((UInt[8], List[UInt[8]]), Bool)" "x.0.1.push(5);") nested 13 == "S015 2:3"
/-!
A `pop` of an element deeper than the element type of the list can lower the depth of the list. Then
the refresh finds each depth on the path again. Thus the `pop` also charges the size 11 of the root,
after the part count 2 (section 5.4). The first `pop` charges 4 for its statement, 6 for the
element, 2, and 11. The second element `UInt[8]` is not deeper than `Type`, so its `pop` charges
only 4, 2, and 2. After the deep `pop`, the stored depth of the root is exact, so `(t,)` runs at the
nesting depth 5. Without the `pop`, it goes above it.
-/
def typeList (_ : Ty) : Eval.Val :=
  .agg (.mkTuple #[.uint 8, .list .type]
    #[leafX 0, .static (.list .type #[.type (.uint 8), .type (.array (.array (.uint 8) 1) 1)])])
#guard runF (assignIn "(UInt[8], List[Type])" "let y = x.1.pop();") typeList ==
  " | [x$0e, (list type ((type (uint 8))))] | 27"
#guard runF (assignIn "(UInt[8], List[Type])" "let y = x.1.pop();") typeList 23 == "S015 3:3"
#guard runF (assignIn "(UInt[8], List[Type])" "let y = x.1.pop();") typeList 22 == "S015 2:11"
#guard runF (assignIn "(UInt[8], List[Type])" "let y = x.1.pop(); let z = x.1.pop();") typeList ==
  " | [x$0e, (list type ())] | 35"
def popDeep (pop : String) : String := s!"module M() domains() \{
    input a: UInt[8];
    output y: UInt[8];
    let mut t = (a, list(Type));
    t.1.push([[UInt[8]; 1]; 1]);
    {pop}
    let u = (t,);
    y := a;
}"
#guard top (popDeep "let k = t.1.pop();") "M()" (depth := 5) == "total 147\nM 119\n"
#guard top (popDeep "") "M()" (depth := 5) == "S015 7:13"
#guard top (popDeep "") "M()" (depth := 6) == "total 132\nM 104\n"

/-!
`==` and `!=` on a hardware aggregate (section 5.4). A hardware value prints as its tree: a name,
a constant, or an operator with its operands. `runEq` binds `y` to the expression `e` in the
body of `f` with the formal `x`. Its units count the statement and the operands too.
-/
mutual
  def hwTree : Eval.Hw → String
    | .node _ _ _ (.bin op) xs => s!"({op.text} {hwTrees xs})"
    | h => nameText h

  def hwTrees : List Eval.Hw → String
    | [] => ""
    | [x] => hwTree x
    | x :: xs => s!"{hwTree x} {hwTrees xs}"
end

def runEq (t e : String) (base : Ty → Eval.Val := refX) (fuel : Nat := 1000000) : String :=
  runF (assignIn t s!"let y = {e};") base fuel hwTree

/-!
The exact charges of `x == x`. The statement and the operands charge 4, the join 1, and the
root pair 1. Each leaf pair charges 1 plus 3 for its `icmp` node. The `and` node charges 3 after
the walk. `return true;` charges 4. `!=` adds the `xor` node last, 3 more. The chain charges
after the walk, so at the fuel 16 it fails at the operator, and at 17 only the `return` fails.
-/
#guard runEq "(UInt[8], Bool)" "x == x" ==
  "y=(& (== x$0e x$0e) (== x$1e x$1e)) | ref x | 21"
#guard runEq "(UInt[8], Bool)" "x != x" ==
  "y=(^ (& (== x$0e x$0e) (== x$1e x$1e)) (bool true)) | ref x | 24"
#guard runEq "(UInt[8], Bool)" "x == x" (fuel := 16) == "S015 2:11"
#guard runEq "(UInt[8], Bool)" "x == x" (fuel := 17) == "S015 3:3"

/-!
A reference pairs leaf by leaf through its type, also in nested containers and records. `()`
adds no pair to the chain. A reference against a literal: each static leaf converts to the type
of its pair with its conversion charge, here 2 for `3`, before its `icmp`. A `Bool` needs no
conversion.
-/
#guard runEq "[[UInt[8]; 2]; 2]" "x == x" ==
  "y=(& (& (& (== x$0e$0e x$0e$0e) (== x$0e$1e x$0e$1e)) (== x$1e$0e x$1e$0e)) " ++
  "(== x$1e$1e x$1e$1e)) | ref x | 38"
#guard runEq "(Bool, ())" "x == (true, ())" == "y=(== x$0e (bool true)) | ref x | 22"
#guard runEq "[UInt[8]; 2]" "x == [1, 2]" ==
  "y=(& (== x$0e (uint 8 1)) (== x$1e (uint 8 2))) | ref x | 32"
#guard runEq "(UInt[8], Bool)" "x == (3, true)" ==
  "y=(& (== x$0e (uint 8 3)) (== x$1e (bool true))) | ref x | 30"
#guard runF ("struct S { a: UInt[8], b: Bool }\n" ++ assignIn "S" "let y = x == S(1, true);")
  refX 1000000 hwTree == "y=(& (== x$a (uint 8 1)) (== x$b (bool true))) | ref x | 34"

/-!
Static and hardware parts mix. A static pair charges as a static equality, and its result goes
into `s`. Thus `E_0` is `(const 1 s)`. `s` is 0 when a static pair differs, also by the length of
a list. The operands can take either side.
-/
def mixedX (_ : Ty) : Eval.Val := .agg (.mkTuple #[.uint 8, .int, .list .int]
  #[leafX 0, .static (.int 3), .static (.list .int #[.int 1])])
#guard runEq "(UInt[8], Int, List[Int])" "x == (5, 3, x.2)" mixedX ==
  "y=(& (bool true) (== x$0e (uint 8 5))) | [x$0e, (int 3), (list int ((int 1)))] | 39"
#guard runEq "(UInt[8], Int, List[Int])" "x == (5, 4, x.2)" mixedX ==
  "y=(& (bool false) (== x$0e (uint 8 5))) | [x$0e, (int 3), (list int ((int 1)))] | 39"
#guard runEq "(UInt[8], Int, List[Int])" "x != (5, 3, list(Int))" mixedX ==
  "y=(^ (& (bool false) (== x$0e (uint 8 5))) (bool true)) | " ++
  "[x$0e, (int 3), (list int ((int 1)))] | 43"
#guard runEq "(UInt[8], Int, List[Int])" "(5, 3, list(Int)) == x" mixedX ==
  "y=(& (bool false) (== (uint 8 5) x$0e)) | [x$0e, (int 3), (list int ((int 1)))] | 40"

/-!
The order of the errors. The function flag comes first: with the fuel 42 the operands are done,
and the flag fails with no charge of the operator. The join comes next: it charges 1 for the
pair of arrays and fails, before any walk unit. The walk then visits the pairs in order: the
second pair fails its fit after its conversion charge, at the fuel 22.
-/
#guard runEq "(UInt[8], Bool)" "x == (1, f)" (fuel := 41) == "S015 2:16"
#guard runEq "(UInt[8], Bool)" "x == (1, f)" (fuel := 42) == "S010 2:11"
#guard runEq "[UInt[8]; 2]" "x == [1, 2, 3]" (fuel := 14) == "S015 2:11"
#guard runEq "[UInt[8]; 2]" "x == [1, 2, 3]" (fuel := 15) == "S010 2:11"
#guard runEq "(UInt[8], UInt[8])" "x == (3, 300)" (fuel := 21) == "S015 2:11"
#guard runEq "(UInt[8], UInt[8])" "x == (3, 300)" (fuel := 22) == "S012 2:11"
#guard runEq "(UInt[8], Bool)" "x == 3" == "S010 2:11"
#guard runEq "(UInt[8], Bool)" "x < x" == "S010 2:11"

/-!
The walk charges each pair before it visits it, and a reference never expands. Thus `==` of two
references to a huge array fails on the budget in the walk, before the chain exists.
-/
#guard runEq "[UInt[8]; 1 << 40]" "x == x" == "S015 2:11"

/-!
A hardware `if` by leaf (sections 5.4 and 7.4). `ifTree` prints a `mux` node and the mark
`share k` of a shared condition too. `runIf` binds `y` to the expression `e` in the body of `f`
with the formal `x`.
-/
mutual
  def ifTree : Eval.Hw → String
    | .node _ _ _ .mux xs => s!"(mux {ifTrees xs})"
    | .node _ _ _ (.share k) xs => s!"(share {k} {ifTrees xs})"
    | .node _ _ _ (.un op) xs => s!"({op.text} {ifTrees xs})"
    | .node _ _ _ (.bin op) xs => s!"({op.text} {ifTrees xs})"
    | h => nameText h

  def ifTrees : List Eval.Hw → String
    | [] => ""
    | [x] => ifTree x
    | x :: xs => s!"{ifTree x} {ifTrees xs}"
end

def runIf (t s : String) (base : Ty → Eval.Val := refX) (fuel : Nat := 1000000) : String :=
  runF (assignIn t s) base fuel ifTree

/-!
The exact charges of an `if` with array arms. The statement charges 1, the `if` node 1, and each
operand 2. The join charges 1 for the pair of arrays. The walk charges 1 for the root pair, and
each leaf pair charges 1 plus 4 for its `mux` node. `return true;` charges 4. The condition `x.0`
is a core name, so it gets no mark. `!x.0` gets the mark `share 0`, because the walk makes two
`mux` nodes. The mark charges the size 2 of `!x.0` once, before the walk. One `mux` node and a
`()` pair give no mark.
-/
def armsT : String := "(Bool, [UInt[8]; 2], [UInt[8]; 2])"
#guard runIf armsT "let y = if (x.0) { x.1 } else { x.2 };" ==
  "y$0e=(mux x$0e x$1e$0e x$2e$0e) y$1e=(mux x$0e x$1e$1e x$2e$1e) | ref x | 24"
#guard runIf armsT "let y = if (!x.0) { x.1 } else { x.2 };" ==
  "y$0e=(mux (share 0 (! x$0e)) x$1e$0e x$2e$0e) " ++
  "y$1e=(mux (share 0 (! x$0e)) x$1e$1e x$2e$1e) | ref x | 29"
#guard runIf armsT "let y = if (!x.0) { x.1 } else { x.2 };" (fuel := 22) == "S015 2:11"
#guard runIf armsT "let y = if (!x.0) { x.1 } else { x.2 };" (fuel := 24) == "S015 2:11"
#guard runIf armsT "let y = if (!x.0) { x.1 } else { x.2 };" (fuel := 25) == "S015 3:3"
#guard runIf "(Bool, (UInt[8], ()), (UInt[8], ()))" "let y = if (!x.0) { x.1 } else { x.2 };" ==
  "y$0e=(mux (! x$0e) x$1e$0e x$2e$0e) | ref x | 23"

/-!
Two static leaves of a data type are a leaf pair: they make a `mux` of constants, and each such
`mux` counts for the mark. A static list pair compares by the static equality of `==`, so `[1]`
equals the typed list `xs`, and the result has the joined type.
-/
#guard runIf armsT ("let a: [UInt[8]; 2] = [1, 2];\n  let y = if (!x.0) { a } else { [3, 4] };") ==
  "y$0e=(mux (share 0 (! x$0e)) (uint 8 1) (uint 8 3)) " ++
  "y$1e=(mux (share 0 (! x$0e)) (uint 8 2) (uint 8 4)) | ref x | 69"
def listArms (k : Nat) : String :=
  s!"let mut xs = list(UInt[8]);\n  push(xs, 1);\n  let mut ys = list(Int);\n  push(ys, {k});\n" ++
  "  let y = if (x.0) { ys } else { xs };"
#guard runIf armsT (listArms 1 ++ "\n  let z: List[UInt[8]] = y;") == " | ref x | 62"
#guard runIf armsT (listArms 2) == "S011 6:11"

/-!
Equal static sides without the joined type are `S011` at the `if`, in each arm order. Here the
lists of `(Int, UInt[8])` and `(UInt[8], Int)` join to a list of `(UInt[8], UInt[8])`, so no
side has the joined type. A list of `(UInt[8], UInt[8])` has the joined type, so it is the
result in each arm order.
-/
def crossArms (a b : String) : String :=
  "type A = (Int, UInt[8]);\ntype B = (UInt[8], Int);\ntype C = (UInt[8], UInt[8]);\n" ++
  assignIn armsT ("let mut xs = list(A);\n  xs.push((1, 2));\n  let mut ys = list(B);\n" ++
    "  ys.push((1, 2));\n  let mut zs = list(C);\n  zs.push((1, 2));\n" ++
    s!"  let y = if (x.0) \{ ({a}, x.0) } else \{ ({b}, x.0) };\n" ++
    "  let z: (List[C], Bool) = y;")
#guard runF (crossArms "xs" "ys") refX 1000000 ifTree == "S011 11:11"
#guard runF (crossArms "ys" "xs") refX 1000000 ifTree == "S011 11:11"
#guard runF (crossArms "xs" "zs") refX 1000000 ifTree ==
  "y$1e=(mux x$0e x$0e x$0e) z$1e=y$1e | ref x | 251"
#guard runF (crossArms "zs" "xs") refX 1000000 ifTree ==
  runF (crossArms "xs" "zs") refX 1000000 ifTree

/-! Each mark of one instantiation takes the next number. -/
#guard runIf armsT ("let y = if (!x.0) { x.1 } else { x.2 };\n" ++
  "  let z = if (!x.0) { x.2 } else { x.1 };") ==
  "y$0e=(mux (share 0 (! x$0e)) x$1e$0e x$2e$0e) " ++
  "y$1e=(mux (share 0 (! x$0e)) x$1e$1e x$2e$1e) " ++
  "z$0e=(mux (share 1 (! x$0e)) x$2e$0e x$1e$0e) " ++
  "z$1e=(mux (share 1 (! x$0e)) x$2e$1e x$1e$1e) | ref x | 54"

/-!
A record descends by its named fields. The join of two struct types charges as a type
equality, the sum of the two sizes 1 + 1, instead of 1.
-/
#guard runF ("struct S { a: UInt[8], b: Bool }\n" ++
  assignIn "(Bool, S, S)" "let y = if (!x.0) { x.1 } else { x.2 };") refX 1000000 ifTree ==
  "y$a=(mux (share 0 (! x$0e)) x$1e$a x$2e$a) y$b=(mux (share 0 (! x$0e)) x$1e$b x$2e$b) | " ++
  "ref x | 30"

/-!
Scalar arms keep the rule of slice 1: no join charge and no walk unit. Two arms of type `()`
give `()`. Two static arms of a type that is not hardware data are a static pair (F19). It
charges the sum of the sizes, here 1 + 1. Equal arms give the static value, and different arms
are `S011` at the `if`. An `Int` arm and a `Bool` arm have no join, so they are `S010`. The
assignment `x.1 = ...` binds the hardware leaf of `x` again, at the next version.
-/
def bitX : Eval.Agg := .hw (.mk at1 .bool (.ref ⟨"x", [.elem 0]⟩) [])
def intPart (_ : Ty) : Eval.Val := .agg (.mkTuple #[.bool, .int] #[bitX, .static (.int 0)])
#guard runIf "(Bool, UInt[8])" "let y = if (!x.0) { () } else { () };" == " | ref x | 15"
#guard runIf "(Bool, Int)" "x.1 = if (x.0) { 3 } else { 3 };" intPart ==
  "x$1v$0e=x$0e | [x$1v$0e, (int 3)] | 18"
#guard runIf "(Bool, Int)" "x.1 = if (x.0) { 3 } else { 3 };" intPart (fuel := 11) == "S015 2:3"
#guard runIf "(Bool, Int)" "x.1 = if (x.0) { 3 } else { 4 };" intPart (fuel := 10) == "S015 2:9"
#guard runIf "(Bool, Int)" "x.1 = if (x.0) { 3 } else { 4 };" intPart (fuel := 11) == "S011 2:9"
#guard runIf "(Bool, Int)" "let y = if (x.0) { \"a\" } else { \"a\" };" intPart ==
  " | [x$0e, (int 0)] | 18"
#guard runIf "(Bool, Int)" "let y = if (x.0) { \"a\" } else { \"b\" };" intPart == "S011 2:11"
#guard runIf "(Bool, Int)" "let y = if (x.0) { 3 } else { true };" intPart == "S010 2:11"
#guard runIf "(Bool, Int)" "let y = if (x.0) { () } else { 3 };" intPart == "S010 2:11"

/-!
A static pair in an aggregate. Equal sides give the value, and a hardware pair beside them makes
a `mux`. The first static pair whose sides differ is `S011` at the `if`, and the walk stops
there. The units up to that pair are 16. The statement, the `if`, and the three operands charge
8. The join of the tuples and the root pair charge 1 each. Each static pair charges 1 + 2. Thus
the fuel 16 gives `S011`, and the `mux` of the third pair never charges.
-/
def staticArms (u : Int) (_ : Ty) : Eval.Val :=
  let leaf (k : Nat) : Eval.Agg := .hw (.mk at1 (.uint 8) (.ref ⟨"x", [.elem 2, .elem k]⟩) [])
  let ts := #[Ty.int, .int, .uint 8]
  .agg (.mkTuple #[.bool, .tuple ts, .tuple ts] #[bitX,
    .mkTuple ts #[.static (.int 5), .static (.int 6), leaf 1],
    .mkTuple ts #[.static (.int 5), .static (.int u), leaf 2]])
def armsS : String := "(Bool, (Int, Int, UInt[8]), (Int, Int, UInt[8]))"
#guard runIf armsS "let y = if (!x.0) { x.1 } else { x.2 };" (staticArms 6) ==
  "y$2e=(mux (! x$0e) x$1e$2e x$2e$2e) | [x$0e, [(int 5), (int 6), x$1e$2e], " ++
  "[(int 5), (int 6), x$2e$2e]] | 28"
#guard runIf armsS "let y = if (x.0) { x.1 } else { x.2 };" (staticArms 7) == "S011 2:11"
#guard runIf armsS "let y = if (x.0) { x.1 } else { x.2 };" (staticArms 7) (fuel := 15) ==
  "S015 2:11"
#guard runIf armsS "let y = if (x.0) { x.1 } else { x.2 };" (staticArms 7) (fuel := 16) ==
  "S011 2:11"

/-!
The walk charges each pair before it visits it, and a reference never expands. Thus an `if`
with two references to a huge array fails on the budget in the walk.
-/
#guard runIf "(Bool, [UInt[8]; 1 << 40], [UInt[8]; 1 << 40])"
  "let y = if (x.0) { x.1 } else { x.2 };" == "S015 2:11"

/-!
A literal and a record constructor with a hardware part make an aggregate node. They charge as a
static literal: the elements, the conversions to the common type, then the size of the result.
`(x.0, 3)` charges the statement 1, the literal 1, `x.0` 2, `3` 2, and its size 3. A binding of
the new node is not a copy, and each hardware leaf gets a core `let`. A literal that waits takes
its type at a typed use, also with a hardware part.
-/
def sx : String := "struct S { a: UInt[8], b: Bool }\n"
#guard runF (assignIn "(UInt[8], Bool)" "let y = (x.0, 3);") refX == "y$0e=x$0e | ref x | 13"
#guard runF (assignIn "(UInt[8], Bool)" "let y = (x.0, 3);") refX 8 == "S015 2:11"
#guard runF (assignIn "(UInt[8], Bool)" "let y = [x.0, 1];") refX == "y$0e=x$0e | ref x | 15"
#guard runF (sx ++ assignIn "(UInt[8], Bool)" "let y = S(x.0, true);") refX ==
  "y$a=x$0e | ref x | 36"
#guard runF (assignIn "(UInt[8], Bool)" "let y: ([Bool; 0], UInt[8]) = ([], x.0);") refX ==
  "y$1e=x$0e | ref x | 48"
#guard runF (assignIn "(UInt[8], Bool)" "let y = [(x.0, 1), (2, 3)];") refX ==
  "y$0e$0e=x$0e | ref x | 36"
#guard runF (assignIn "(UInt[8], Bool)" "let y = [x, (2, true)];") refX ==
  "y$0e$0e=x$0e y$0e$1e=x$1e | ref x | 29"

/-! The elements need a common type, and each field its type. A static leaf checks its fit. -/
#guard runF (assignIn "(UInt[8], Bool)" "let y = [x.0, x.1];") refX == "S010 2:11"
#guard runF (assignIn "(UInt[8], Bool)" "let y = [x.0, 300];") refX == "S012 2:11"
#guard runF (sx ++ assignIn "(UInt[8], Bool)" "let y = S(x.1, true);") refX == "S010 3:11"

/-!
A list holds no value with a hardware leaf: `S011` at the value, also through a place with a
step after the list. A static root of a type with a hardware part takes a hardware value and
binds its leaves. A later update binds them again, and a root without a hardware leaf is static.
-/
def listIn (s : String) : String :=
  assignIn "(UInt[8], Bool)" ("let mut l = list([UInt[8]; 1]);\n  " ++ s)
#guard runF (listIn "l.push([5]);\n  l[0][0] = x.0;") refX == "S011 4:13"
#guard runF (listIn "l.push([5]);\n  l[0] = [x.0];") refX == "S011 4:10"
#guard runF (listIn "l.push([x.0]);") refX == "S011 3:10"
#guard runF (assignIn "(UInt[8], Bool)" "let mut t = (1, 2);\n  t.0 = x.0;") refX == "S010 3:3"
#guard runF (assignIn "(UInt[8], Bool)"
  "let mut t: (UInt[8], Int) = (1, 2);\n  t.0 = x.0;\n  t.1 = 4;") refX ==
  "t$0e=x$0e t$1v$0e=t$0e | ref x | 58"
#guard runF (assignIn "(UInt[8], Bool)"
  "let mut t: (UInt[8], Int) = (1, 2);\n  t.0 = x.0;\n  t.0 = 7;") refX ==
  "t$0e=x$0e | ref x | 57"

/-!
A held aggregate root charges its size 3 at the write-back, the last step before the change. The
waiting `x.1` costs as much as `0`, so the difference is the held charge. A `mut` actual that is
a part of an aggregate root writes back into that part, and the root binds again.
-/
def gx : String := "fn g(mut a: (Bool, Int)) -> Int {\n  a.1 = 5;\n  return 0;\n}\n"
def gb : String := "fn g(mut a: Bool) -> Int {\n  a = !a;\n  return 0;\n}\n"
#guard runF (gx ++ assignIn "(Bool, Int)" "let y = x.1 + g(x);") intPart ==
  "g$0c$a$0e=x$0e g$0c$a$1v$0e=g$0c$a$0e x$1v$0e=g$0c$a$1v$0e | [x$1v$0e, (int 5)] | 52"
#guard runF (gx ++ assignIn "(Bool, Int)" "let y = 0 + g(x);") intPart ==
  "g$0c$a$0e=x$0e g$0c$a$1v$0e=g$0c$a$0e x$1v$0e=g$0c$a$1v$0e | [x$1v$0e, (int 5)] | 49"
#guard runF (gb ++ assignIn "(Bool, Int)" "let y = g(x.0);") intPart ==
  "g$0c$a=x$0e g$0c$a$1v=hardware Bool x$1v$0e=g$0c$a$1v | [x$1v$0e, (int 0)] | 25"
#guard runF (gb ++ assignIn "(Bool, Int)" "let y = x.1 + g(x.0);") intPart ==
  "g$0c$a=x$0e g$0c$a$1v=hardware Bool x$1v$0e=g$0c$a$1v | [x$1v$0e, (int 0)] | 33"

/-! Each new aggregate node checks its depth at its node (`S015`). -/
#guard top (hw "  let t = [[x]];") "M(1)" (depth := 2) == "S015 5:11"
#guard top (hw "  let t = [[x]];") "M(1)" (depth := 3) == "total 148\nM$1 105\n"
#guard top (hw "  let t = ((x,),);") "M(1)" (depth := 2) == "S015 5:11"
#guard top (hw "  let t = ((x,),);") "M(1)" (depth := 3) == "total 148\nM$1 105\n"

/-!
The prelude struct `ReadResponse` acts as `struct ReadResponse(comptime T: Type) { data: T,
valid: Bool }`. A user `struct Bool` or `type Type` does not change it. A user struct
`ReadResponse` shadows the name and serializes with `root`.
-/
def userTypes : String := "struct Bool { x: UInt[2] }\ntype Type = UInt[3];"
def userResponse : String := "struct ReadResponse(comptime T: Type) { data: T, valid: Bool }"
#guard out "" "ReadResponse[UInt[8]]" ==
  "(type (struct prelude ReadResponse ((type (uint 8)))))"
#guard out userTypes "ReadResponse[UInt[8]]()" ==
  "(record (struct prelude ReadResponse ((type (uint 8)))) ((uint 8 0) (bool false)))"
#guard out userTypes "data_bits(ReadResponse[UInt[8]])" == "(int 9)"
#guard out "" "ReadResponse[UInt[8]](3, true).valid" == "(bool true)"
#guard out "" "ReadResponse[UInt[8]](3, true).data" == "(uint 8 3)"
#guard out userResponse "ReadResponse[UInt[8]]" ==
  "(type (struct root ReadResponse ((type (uint 8)))))"
#guard out userResponse "ReadResponse[UInt[8]](3, true)" ==
  "(record (struct root ReadResponse ((type (uint 8)))) ((uint 8 3) (bool true)))"
#guard out "" "ReadResponse[3]" == "S010 1:1"
#guard out "" "ReadResponse[Int]()" == "S010 1:1"

/-!
Each error in the work of the prelude struct reports at its use, also an `S015` in its field
types. No run gives the position `0:0` of the item.
-/
def useResponse : String := "module M() {\n  input a: UInt[8];\n  let t = ReadResponse[UInt[8]];\n}"
#guard top useResponse "M" (depth := 1) == "S015 3:11"
#guard (List.range 63).all fun f =>
  let r := top useResponse "M" (fuel := f)
  r.startsWith "S015 " && !r.startsWith "S015 0:"
#guard (List.range 13).all fun f => top useResponse "M" (fuel := 50 + f) == "S015 3:11"

/-! A user function `read_port` or `write_port` shadows the prelude function and runs as usual. -/
#guard out "comptime fn read_port(a: Nat, b: Nat) -> Nat { return a + b; }" "read_port(1, 2)" ==
  "(int 3)"
#guard out "const X: Int = 5;\nfn write_port(a: Int) -> Int { return a; }" "X.write_port()" ==
  "(int 5)"

/-!
The word reference of a memory response (section 7.6). The base `word` holds the memory `m` and
a bit offset. A leaf of a word is `Op.word`, shown as `m$0rdata@o` and with its width `:w`. It
has the size of a finite value of its type, as a name has.
-/
def memM : Names.Path := ⟨"m", []⟩
def word (_ : Eval.Ctx) (t : Ty) : Eval.Val := .agg (.ref (.word memM 0) t)
def wordX (t : Ty) : Eval.Val := .agg (.ref (.word memM 0) t)
#guard (Eval.Op.word memM 3).size (.uint 200) == 4
#guard (Eval.Hw.mk at1 (.uint 200) (.word memM 3) []).size == 4

/-!
The offset of a part: `k` times the element width for an array, and the widths of the earlier
parts for a tuple or a record. A table of fields can leave out a field without a leaf.
-/
#guard Eval.Ty.offset (fun _ => none) (.array (.uint 4) 8) 3 == 12
#guard Eval.Ty.offset (fun _ => none) (.tuple #[.bool, .uint 8, .uint 3]) 2 == 9
#guard Eval.Ty.offset (fun _ => some #[(0, .uint 8), (2, .uint 4)]) .unit 2 == 8
#guard Eval.Ty.offset (fun _ => some #[(0, .uint 8), (2, .uint 4)]) .unit 3 == 12

/-!
A word base takes each step that a name base takes, with the same charges. In `P`, `a` is at 0,
`z` has no bit, `t.0` is at 8, and `t.1[k]` is at `9 + 4k`. A scalar part is a leaf `Op.word`,
and an aggregate part is a reference with its offset. A part without a hardware leaf is a
static value, and a huge one is `S015` at the step, as for a name base.
-/
#guard sel shapes "P" word [.fld "a"] == "hw UInt[8] m$0rdata@0 1 true 2"
#guard sel shapes "P" word [.fld "t", .dot 1, .idx 2] == "hw UInt[4] m$0rdata@17 1 true 6"
#guard sel shapes "P" word [.fld "t"] == "ref (Bool, [UInt[4]; 3]) m$0rdata@8 6 true 2"
#guard sel shapes "P" word [.fld "t", .idx 0] == "hw Bool m$0rdata@8 1 true 5"
#guard sel shapes "P" word [.fld "e"] == "(array unit ((unit) (unit) (unit))) false 6"
#guard sel shapes "P" word [.fld "z"] == "S015 9:2"
#guard sel shapes "T2" word [.idx 1] == "hw UInt[8] m$0rdata@1 1 true 4"
#guard sel shapes "E" word [.idx 5, .dot 1] == "hw Bool m$0rdata@5 1 true 5"

/-! The offset of an index of a huge array is a product of the metadata, with no walk. -/
#guard sel "" "[UInt[8]; 1099511627776]" word [.idx 1099511627775] ==
  "hw UInt[8] m$0rdata@8796093022200 1 true 4"
#guard sel "" "[[UInt[8]; 1099511627776]; 1099511627776]" word [.idx 7, .idx 9] ==
  "hw UInt[8] m$0rdata@61572651155528 1 true 7"

/-!
The normal form of a word: a scalar word is a leaf at the offset 0, and an aggregate word stays a
reference. Neither charges.
-/
def wordNormal (t : Ty) : String :=
  match Eval.run {} #[] (fun _ => Eval.normalize at1 (.ref (.word memM 0) t)) with
  | .ok (v, used) => s!"{valText v} {used}"
  | .error e => s!"{e.code}"
#guard wordNormal (.uint 8) == "m$0rdata@0:8 0"
#guard wordNormal (.tuple #[.uint 8, .bool]) == "ref m$0rdata@0 0"

/-!
A binding of a word expands it into its leaves in packing order, each with its offset. Its
charges equal those of a name base. A place update expands one level on its path. `()` has no
bit, so `b` is at 8.
-/
def wordS : String := "struct S { a: UInt[8], u: (), b: (Bool, [UInt[4]; 2]) }\n"
#guard runF (wordS ++ assignIn "S" "let y = x;") wordX ==
  "y$a=m$0rdata@0:8 y$b$0e=m$0rdata@8:1 y$b$1e$0e=m$0rdata@9:4 y$b$1e$1e=m$0rdata@13:4 | " ++
  "ref m$0rdata@0 | 14"
#guard runF (wordS ++ assignIn "S" "let y = x;") refX ==
  "y$a=x$a y$b$0e=x$b$0e y$b$1e$0e=x$b$1e$0e y$b$1e$1e=x$b$1e$1e | ref x | 14"
#guard runF (wordS ++ assignIn "S" "x.a = 1;") wordX ==
  "x$1v$b$0e=m$0rdata@8:1 x$1v$b$1e$0e=m$0rdata@9:4 x$1v$b$1e$1e=m$0rdata@13:4 | " ++
  "[(uint 8 1), (unit), ref x$1v$b] | 18"
#guard runF (wordS ++ assignIn "S" "x.b.1[1] = 1;") wordX ==
  "x$1v$a=m$0rdata@0:8 x$1v$b$0e=m$0rdata@8:1 x$1v$b$1e$0e=m$0rdata@9:4 | " ++
  "[x$1v$a, (unit), [x$1v$b$0e, [x$1v$b$1e$0e, (uint 4 1)]]] | 22"

/-! The equality walk takes the leaves of a word by their offsets, with the charges of a name. -/
#guard runEq "(UInt[8], Bool)" "x == x" wordX ==
  "y=(& (== m$0rdata@0:8 m$0rdata@0:8) (== m$0rdata@8:1 m$0rdata@8:1)) | ref m$0rdata@0 | 21"
#guard runF ("struct S { a: UInt[8], b: Bool }\n" ++ assignIn "S" "let y = x == S(1, true);")
  wordX 1000000 hwTree ==
  "y=(& (== m$0rdata@0:8 (uint 8 1)) (== m$0rdata@8:1 (bool true))) | ref m$0rdata@0 | 34"

/-! The records of the static expression `expr` in the file scope of `src`. -/
def records (src expr : String) : List String :=
  match (do
      let (items, checked) ← Cli.load 4096 src
      let e ← Resolve.resolveExpr items (← Parse.parseExpr 4096 expr)
      Check.checkExpr checked e
      return (checked, e) : Except Error _) with
  | .ok (checked, e) => (Eval.observeExpr {} checked e).1.toList
  | .error _ => []

/-!
`diagnostic` under `eval` (section 8.2) charges as in a module, and its emitted name is `-`. The
call charges 10 units for its node, its name, its arguments, and their copies. Then it charges
1 for the measure of `1` and the 38 bytes of the record.
-/
#guard records "" "diagnostic(\"x\", 1)" == ["(record 1 1 - () (string \"x\") (int 1))"]
#guard exact "" "diagnostic(\"x\", 1)" (10 + 1 + 38)

/-!
The enums of slice 3. The first use of an enum charges as the first use of a struct specialization:
`Op` charges 69 units. They are the node 1, the size of the enum type 1, and the tag type `UInt[2]`
6. Then the variants `Add` 8, `Load` 18, and `Pair` 23 follow. Each variant charges its tag value
with its typed use at `UInt[2]` 4, and its payload types as type expressions. Then the sums of the
tuple of its payload types charge. The metadata of the enum then charges 12, the sums of the record
of `UInt[2]` and `UInt[8]`. A later use charges only its node.
-/
def ops : String :=
  "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n"

#guard out ops "1" == "(int 1)"
#guard out ops "Op" == "(type (enum root Op ()))"
#guard exact ops "Op" 69
#guard exact ops "[Op, Op]" (1 + 69 + 1 + 3)

/-!
`T()` of an enum gives the tag 0 and the payload 0, and it charges the zero size 3 from the
metadata. `data_bits(Op)` is `W + P`. An enum without payload has no payload part, and its tag can
have no variant.
-/
#guard out ops "Op()" == "(enum (enum root Op ()) 0 (uint 8 0))"
#guard exact ops "Op()" (1 + 69 + 3)
#guard out ops "data_bits(Op)" == "(int 10)"
#guard exact ops "data_bits(Op)" (2 + 69 + 1)
#guard out "enum E: UInt[3] { A = 5 }\n" "E()" == "(enum (enum root E ()) 0)"
#guard out "enum E: UInt[1] {}\n" "data_bits(E)" == "(int 1)"
#guard out ops "[Op(), Op()]" ==
  "(array (enum root Op ()) ((enum (enum root Op ()) 0 (uint 8 0)) " ++
    "(enum (enum root Op ()) 0 (uint 8 0))))"

/-!
The checks of section 5.6 run in their order, each error at its node. The tag type comes first
(`S010`). Then each variant checks its tag value at `UInt[W]` (`S010`, `S012`) and its payload types
(`S010`). The payload width `P` is at most 65536, `S012` at the `enum` keyword after all variants.
-/
#guard out "enum E: Bool { A = 0 }\n" "E" == "S010 1:9"
#guard out "enum E: UInt[1] { A = 2 }\n" "E" == "S012 1:23"
#guard out "enum E: UInt[1] { A = true }\n" "E" == "S010 1:23"
#guard out "enum E: UInt[1] { A = SInt[1](0) }\n" "E" == "S010 1:23"
#guard out "enum E: UInt[1] { A(Int) = 0 }\n" "E" == "S010 1:21"
#guard out "enum E: UInt[1] { A(Int) = 2 }\n" "E" == "S012 1:28"
#guard out "enum E: UInt[1] { A(UInt[65536], Bool) = 0, B(Int) = 1 }\n" "E" == "S010 1:47"
#guard out "enum E: UInt[1] { A(UInt[65536], Bool) = 0 }\n" "E" == "S012 1:1"
#guard msg "enum E: UInt[1] { A(UInt[65536], Bool) = 0 }\n" "E" ==
  "the payload of `E` has 65537 bits, above 65536; use smaller payloads"
#guard out "enum E: UInt[1] { A(UInt[65536]) = 0 }\n" "data_bits(E)" == "(int 65537)"

/-!
An enum whose payload names the enum, directly or through a struct, is `S019` at the use of the
enum in progress. The first use of an enum counts toward the nesting depth.
-/
#guard out "enum E: UInt[1] { A(E) = 0 }\n" "E" == "S019 1:21"
#guard msg "enum E: UInt[1] { A(E) = 0 }\n" "E" == "the enum `E` depends on itself"
#guard out "enum E: UInt[1] { A(S) = 0 }\nstruct S { e: E }\n" "E" == "S019 2:15"
#guard out "enum E: UInt[1] { A(S) = 0 }\nstruct S { e: E }\n" "S" == "S019 1:21"
#guard out "enum E: UInt[1] { A(S) = 0 }\nstruct S { a: Bool }\n" "E" (depth := 2) ==
  "(type (enum root E ()))"
#guard out "enum E: UInt[1] { A(S) = 0 }\nstruct S { a: Bool }\n" "E" (depth := 1) ==
  "S015 1:21"

/-!
A tag value is a structural context (section 9.4). A call there nests deeper, so it can change
its own locals.
-/
#guard out ("fn f() -> UInt[1] { let mut xs = list(Int); push(xs, 1); return 0; }\n" ++
  "enum E: UInt[1] { A = f() }\n") "E" == "(type (enum root E ()))"

/-!
`==` and `!=` on a type that holds an enum are `S010` at the operator, with the text of section
6.2. The check reads the enum flag after the function flag, before each join and each charge.
The text names the type of the first operand with the flag.
-/
def enumEq : String := "`Op` has no `==`; compare with `match (x) { E::V => true, _ => false }`"
#guard out ops "Op() == Op()" == "S010 1:1"
#guard msg ops "Op() == Op()" == enumEq
#guard msg ops "Op() != 1" == enumEq
#guard msg ops "1 == Op()" == enumEq
#guard msg ops "[Op()] != [Op()]" ==
  "`[Op; 1]` has no `==`; compare with `match (x) { E::V => true, _ => false }`"
#guard msg ops "(1, Op()) == (1, Op())" ==
  "`(Int, Op)` has no `==`; compare with `match (x) { E::V => true, _ => false }`"
#guard msg ops "Op == Op" == "no error"
#guard msg ops "(fn (Op) -> Bool) == (fn (Op) -> Bool)" == "no error"

/-!
A typed use at an enum type needs a value of exactly this enum type. It converts nothing, so it
charges no conversion. Two enum types join as a type equality, 1 plus 1, and two different enums
have no join (`S010`).
-/
def flags : String := ops ++ "enum Flag: UInt[1] { On = 1 }\n"
#guard out (ops ++ "fn f(x: Op) -> Op { return x; }\n") "f(Op())" ==
  "(enum (enum root Op ()) 0 (uint 8 0))"
#guard out (ops ++ "fn f(x: Op) -> Op { return x; }\n") "f(1)" == "S010 1:1"
#guard out (flags ++ "fn f(x: Op) -> Op { return x; }\n") "f(Flag())" == "S010 1:1"
#guard out (flags ++ "const C: Op = Flag();\n") "C" == "S010 3:1"
#guard out flags "[Op(), Op()]" != "S010 1:1"
#guard out flags "[Op(), Flag()]" == "S010 1:1"
#guard out flags "[Op(), 1]" == "S010 1:1"
/-! The literal charges its node, both zeros, the join 2 of the two enum types, and its size 7. -/
#guard exact flags "[Op(), Op()]" (1 + (1 + 69 + 3) + (1 + 1 + 3) + 2 + 7)

/-!
A field `.f` or a selector `.N` of an enum is `S010` at the selection node, with the text of
section 6.2: `tag` and `payload` are leaves, not fields. The text names `data_bits` of the enum.
-/
#guard out ops "Op().tag" == "S010 1:1"
#guard msg ops "Op().tag" == "`Op` is an enum and has no field `tag`; read a payload with " ++
  "`match`, or the bits with `reinterpret(UInt[10], e)`"
#guard msg ops "Op().0" == "`Op` is an enum and has no field `0`; read a payload with " ++
  "`match`, or the bits with `reinterpret(UInt[10], e)`"
#guard out (ops ++ "fn f() -> Int { let mut e = Op(); e.payload = 1; return 0; }\n") "f()" ==
  "S010 2:35"

/-!
A call of an enum type with arguments is `S010` at the call, with the text of section 6.2. The
check comes after the callee and before the arguments evaluate, so an argument with an error does
not run. `E()` stays the zero.
-/
#guard out ops "Op(1)" == "S010 1:1"
#guard msg ops "Op(1 / 0, 2)" == "`Op` is an enum, so `Op(...)` takes no arguments; construct " ++
  "a variant such as `Op::V(...)`, or write `Op()` for the zero"

/-!
A variant constructor (section 5.4) is one node, then a use of the enum. Then its payload values
evaluate, their copies charge, and each gets its typed use at its payload type. Then the size of
the result charges, 3 for a static `Op` value, and the static pack makes it. `Op::Add` charges
its node, the first use 68, and the size 3. `Op::Load(5)` adds the literal 2, its copy 1, and its
conversion to `UInt[8]` 2. `Op::Pair(true, 5)` adds two literals 4, two copies 2, and the
conversion of `5` 2; `true` converts nothing. A later use of the enum charges nothing more.
-/
#guard out ops "Op::Add" == "(enum (enum root Op ()) 0 (uint 8 0))"
#guard exact ops "Op::Add" (1 + 68 + 3)
#guard out ops "Op::Load(5)" == "(enum (enum root Op ()) 1 (uint 8 5))"
#guard exact ops "Op::Load(5)" (1 + 68 + 2 + 1 + 2 + 3)
#guard exact ops "Op::Pair(true, 5)" (1 + 68 + 4 + 2 + 2 + 3)
#guard exact ops "[Op::Add, Op::Add]" (1 + (1 + 68 + 3) + (1 + 3) + 2 + 7)

/-!
The payload packs its leaves in packing order, the first leaf in the low bits, with zero high
bits up to `P` (ADR 0025). `Pair(true, 5)` thus has the payload `1 + 5 * 2`. A nested enum packs
its tag, then its payload, and `()` adds no bit. A payload across several words of 64 bits packs
each leaf at its offset.
-/
#guard out ops "Op::Pair(true, 5)" == "(enum (enum root Op ()) 2 (uint 8 11))"
#guard out ops "Op::Pair(false, 15)" == "(enum (enum root Op ()) 2 (uint 8 30))"
def nestedEnums : String :=
  "enum F: UInt[1] { A = 0, B = 1 }\nenum E: UInt[2] { X(F, [UInt[3]; 2], ()) = 3 }\n"
#guard out nestedEnums "E::X(F::B, [5, 2], ())" == "(enum (enum root E ()) 3 (uint 7 43))"
def wideEnum : String := "enum E: UInt[1] { A(UInt[63], UInt[70], Bool) = 1, B = 0 }\n"
#guard out wideEnum "E::A(UInt[63](0) -% 1, UInt[70](0) -% 3, true)" ==
  s!"(enum (enum root E ()) 1 (uint 134 {(2 ^ 63 - 1) + (2 ^ 70 - 3) * 2 ^ 63 + 2 ^ 133}))"
#guard out "enum E: UInt[1] { A(SInt[4], Bool) = 1 }\n" "E::A(-1, true)" ==
  "(enum (enum root E ()) 1 (uint 5 31))"
#guard out "enum E: UInt[1] { A(UInt[64], UInt[64], Bool) = 1 }\n"
  "E::A(UInt[64](0) -% 1, 2, true)" ==
  s!"(enum (enum root E ()) 1 (uint 129 {2 ^ 64 - 1 + 2 * 2 ^ 64 + 2 ^ 128}))"
#guard out wideEnum "E::B" == "(enum (enum root E ()) 0 (uint 134 0))"
#guard out "enum E: UInt[1] { A(UInt[65536]) = 1 }\n" "E::A(UInt[65536](0) -% 1)" ==
  s!"(enum (enum root E ()) 1 (uint 65536 {2 ^ 65536 - 1}))"

/-!
The errors of a constructor come in its order. An error of a payload value comes first. Then
each typed use runs in order. A value of another type is `S010`, and a value that does not fit
is `S012`, each at the start of the path. The copies charge before the typed uses. Thus the fuel
of the node, the use, the values, and the copies reaches the conversion charge.
-/
#guard out ops "Op::Pair(1 / 0, 16)" == "S013 1:10"
#guard out ops "Op::Pair(1, 16)" == "S010 1:1"
#guard out ops "Op::Pair(true, 16)" == "S012 1:1"
#guard msg ops "Op::Pair(true, 16)" == "16 does not fit UInt[4]"
#guard out ops "Op::Load(5)" (1 + 68 + 2 + 1) == "S015 1:1"
#guard msg ops "Op::Load(256)" (1 + 68 + 2 + 1 + 2) == "256 does not fit UInt[8]"
#guard out (ops ++ "fn f(x: UInt[8]) -> Op { return Op::Load(x); }\n") "f(7)" ==
  "(enum (enum root Op ()) 1 (uint 8 7))"

/-!
`reinterpret` converts between an enum and exactly `UInt[W + P]` (F26): the tag in the low `W`
bits, then the payload. A static conversion charges the copies of its arguments, then the size
of its result. `reinterpret(UInt[10], Op::Pair(true, 5))` charges its node and name 2, the type
6, the constructor 80, the copies 5, and the result 1. `reinterpret(Op, UInt[10](45))` charges
its node and name 2, the use of `Op` 69, the constructor 12, the copies 2, and the result 3. The
result can have a tag without a variant. Another type on the other side is `S010` at the call.
-/
#guard out ops "reinterpret(UInt[10], Op::Pair(true, 5))" == "(uint 10 46)"
#guard exact ops "reinterpret(UInt[10], Op::Pair(true, 5))" (2 + 6 + 80 + 5 + 1)
#guard out ops "reinterpret(Op, UInt[10](45))" == "(enum (enum root Op ()) 1 (uint 8 11))"
#guard exact ops "reinterpret(Op, UInt[10](45))" (2 + 69 + 12 + 2 + 3)
#guard out ops "reinterpret(Op, UInt[10](1023))" == "(enum (enum root Op ()) 3 (uint 8 255))"
#guard out ops "reinterpret(Op, reinterpret(UInt[10], Op::Pair(true, 5)))" ==
  "(enum (enum root Op ()) 2 (uint 8 11))"
#guard out "enum E: UInt[3] { A = 5 }\n" "reinterpret(UInt[3], E::A)" == "(uint 3 5)"
#guard out "enum E: UInt[3] { A = 5 }\n" "reinterpret(E, UInt[3](2))" == "(enum (enum root E ()) 2)"
#guard out ops "reinterpret(Op, UInt[9](45))" == "S010 1:1"
#guard msg ops "reinterpret(Op, UInt[9](45))" ==
  "`reinterpret` makes Op only from UInt[10], not UInt[9]"
#guard out ops "reinterpret(Op, SInt[10](45))" == "S010 1:1"
#guard out ops "reinterpret(Op, 45)" == "S010 1:1"
#guard out ops "reinterpret(Op, true)" == "S010 1:1"
#guard out ops "reinterpret(UInt[9], Op::Add)" == "S010 1:1"
#guard msg ops "reinterpret(SInt[10], Op::Add)" ==
  "`reinterpret` gives the bits of Op only as UInt[10], not SInt[10]"
#guard out ops "reinterpret(Bool, Op::Add)" == "S010 1:1"
#guard out (ops ++ "enum F: UInt[10] { A = 0 }\n") "reinterpret(F, Op::Add)" == "S010 1:1"
#guard out ops "reinterpret(UInt[10], Op)" == "S010 1:1"

end Silicon.Source.Test.Eval
