-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Parse

/-!
These tests check the parser at its public boundary. They check the AST dump of each slice 1
construct, and precedence and associativity. They check the code and the position of each
error. They also check that the parser reads the text of the printer back to the same AST.
-/

namespace Silicon.Source.Test.Parse

open Silicon.Source Parse
open Silicon.Source.Lex (defaultSyntaxDepth)

def errorText (e : Error) : String := s!"error {e.code} {e.pos.line}:{e.pos.col}"

def dump (s : String) : String :=
  match parseSource defaultSyntaxDepth s with
  | .ok items => Print.dump items
  | .error e => errorText e

def fails (s : String) (code : ErrorCode) (line col : Nat)
    (depth : Nat := defaultSyntaxDepth) : Bool :=
  match parseSource depth s with
  | .error e => e.code == code && e.pos == ⟨line, col⟩
  | .ok _ => false

/-! The value of `const X: T = <s>;`. Its first token is at column 14. -/
def constValue (s : String) (depth : Nat := defaultSyntaxDepth) : Except Error Expr :=
  match parseSource depth ("const X: T = " ++ s ++ ";") with
  | .ok [.const _ _ _ v] => .ok v
  | .ok _ => .error ⟨.S001, ⟨0, 0⟩, "not one const"⟩
  | .error e => .error e

def ex (s : String) (depth : Nat := defaultSyntaxDepth) : String :=
  match constValue s depth with
  | .ok v => v.dump
  | .error e => errorText e

/-!
The body `s` of a `comptime fn`. The body starts on line 2. The parser accepts each statement
there. The pre-check rejects a resource in it.
-/
def ctBody (s : String) : String := "comptime fn f() -> T {\n" ++ s ++ "\n}"

/-! The dump of the one statement `s` in a function body. -/
def st (s : String) (depth : Nat := defaultSyntaxDepth) : String :=
  match parseSource depth (ctBody s) with
  | .ok [.fn _ _ _ _ _ [x]] => x.dump
  | .ok _ => "not one statement"
  | .error e => errorText e

/-! `S001` or `S004` in the body `s` of a function, which starts on line 2. -/
def stFails (s : String) (code : ErrorCode) (col : Nat)
    (depth : Nat := defaultSyntaxDepth) : Bool :=
  fails (ctBody s) code 2 col depth

def roundtrip (items : List Item) : Bool :=
  match parseSource defaultSyntaxDepth (Print.print items) with
  | .ok parsed => Print.dump parsed == Print.dump items
  | .error _ => false

/-! Items. -/
#guard dump "" == ""
#guard dump "const N: Nat = 3;" == "(const \"N\" (name \"Nat\") (num 3))\n"
#guard dump "fn inc(x: UInt[8],) -> UInt[8] { return x +% 1; }" ==
  "(fn false \"inc\" ((param none \"x\" (index (name \"UInt\") ((num 8))))) " ++
  "(index (name \"UInt\") ((num 8))) ((ret (some (binary addw (name \"x\") (num 1))))))\n"
#guard dump "comptime fn g(comptime n: Nat) -> Nat { return n; }" ==
  "(fn true \"g\" ((param comptime \"n\" (name \"Nat\"))) (name \"Nat\") " ++
  "((ret (some (name \"n\")))))\n"
#guard dump "module M() {}" == "(module \"M\" () none ())\n"
#guard dump "module M() domains() {}" == "(module \"M\" () (some ()) ())\n"
#guard dump "module M(comptime W: Nat, comptime B: Bool,) domains(clk,) {}" ==
  "(module \"M\" ((param comptime \"W\" (name \"Nat\")) (param comptime \"B\" (name \"Bool\"))) " ++
  "(some (\"clk\")) ())\n"
#guard dump "const A: T = 1;\nconst B: T = 2;" ==
  "(const \"A\" (name \"T\") (num 1))\n(const \"B\" (name \"T\") (num 2))\n"
#guard dump "const A: T[1][2] = 0;" ==
  "(const \"A\" (index (index (name \"T\") ((num 1))) ((num 2))) (num 0))\n"

/-! Statements. -/
#guard st "let x = 1;" == "(local false \"x\" none (num 1))"
#guard st "let mut x: Bool = true;" == "(local true \"x\" (some (name \"Bool\")) (bool true))"
#guard st "x = 1;" == "(assign (name \"x\") (num 1))"
#guard st "u.d := x;" == "(connect (field (name \"u\") \"d\") (name \"x\"))"
#guard st "reg r: UInt[4] = 0;" == "(reg \"r\" (index (name \"UInt\") ((num 4))) (num 0))"
#guard st "wire w: Bool;" == "(wire \"w\" (name \"Bool\"))"
#guard st "input i: Bool;" == "(input \"i\" none (name \"Bool\"))"
#guard st "output o: Bool;" == "(output \"o\" none (name \"Bool\"))"

/-! A family entry has one key expression in `[ ]`. `[]` and `[a, b]` are `S001`. -/
#guard st "input req[i]: T;" == "(input \"req\" (some (name \"i\")) (name \"T\"))"
#guard st "output g[N + 1]: T;" ==
  "(output \"g\" (some (binary add (name \"N\") (num 1))) (name \"T\"))"
#guard stFails "input req[]: T;" .S001 11
#guard stFails "input req[a, b]: T;" .S001 12
#guard stFails "input req[a: T;" .S001 12

/-!
An `as` key is one expression after the type (section 5.6). An indexed port with `as` is `S001`
at `as`, with the text "`as` on an indexed port" of section 6.2.
-/
#guard st "input pin: Bool as \"req_0\";" ==
  "(input \"pin\" (keyed (str \"req_0\")) (name \"Bool\"))"
#guard st "output o: T as PortKey(\"gnt\", true, i + 1);" ==
  "(output \"o\" (keyed (call (name \"PortKey\") ((str \"gnt\") (bool true) " ++
    "(binary add (name \"i\") (num 1))))) (name \"T\"))"
#guard stFails "output o[0]: T as k;" .S001 16
#guard stFails "input i: T as;" .S001 14
#guard stFails "input i: T as k as j;" .S001 17
#guard st "instance u = M(8, true);" == "(inst \"u\" \"M\" ((num 8) (bool true)))"
#guard st "instance u = M();" == "(inst \"u\" \"M\" ())"
#guard st "return;" == "(ret none)"
#guard st "return x;" == "(ret (some (name \"x\")))"
#guard st "comptime if (c) { return; }" == "(ctif (name \"c\") ((ret none)) none)"
#guard st "comptime if (c) {} else {}" == "(ctif (name \"c\") () (some ()))"
#guard st "comptime for i in 0 .. N + 1 {}" ==
  "(ctfor \"i\" (num 0) (binary add (name \"N\") (num 1)) ())"
#guard st "{ x; { } }" == "(block ((expr (name \"x\")) (block ())))"
#guard st "static_assert(N > 0, \"positive\");" ==
  "(expr (call (name \"static_assert\") ((binary gt (name \"N\") (num 0)) (str \"positive\"))))"
#guard st "x + 1;" == "(expr (binary add (name \"x\") (num 1)))"
#guard st "x.y.z;" == "(expr (field (field (name \"x\") \"y\") \"z\"))"

/-!
A place is a name, or a field, an index, or a selector of a place. A call is no place. An
index with two arguments parses: the type rules reject it.
-/
#guard st "a[i] = 1;" == "(assign (index (name \"a\") ((name \"i\"))) (num 1))"
#guard st "t.0 := x;" == "(connect (select (name \"t\") 0) (name \"x\"))"
#guard st "a[i].0x1.f[j] = 1;" ==
  "(assign (index (field (select (index (name \"a\") ((name \"i\"))) 1) \"f\") " ++
  "((name \"j\"))) (num 1))"
#guard st "a[i, j] = 1;" ==
  "(assign (index (name \"a\") ((name \"i\") (name \"j\"))) (num 1))"
#guard st "a[i] + 1;" == "(expr (binary add (index (name \"a\") ((name \"i\"))) (num 1)))"
#guard st "t.1;" == "(expr (select (name \"t\") 1))"
#guard st "(a, b);" == "(expr (tuple ((name \"a\") (name \"b\"))))"
#guard st "[a];" == "(expr (array ((name \"a\"))))"
#guard stFails "f(x)[0] = 1;" .S001 9
#guard stFails "a.0(x) = 1;" .S001 8
#guard stFails "(a,) = 1;" .S001 6
#guard stFails "[a][0] = 1;" .S001 8
#guard stFails "a[] = 1;" .S001 3
#guard stFails "a.x(1) = 1;" .S001 8
#guard stFails "x.f().g = 1;" .S001 9
#guard st "mem m: [T; 4];" == "(mem \"m\" (name \"T\") (num 4))"
#guard st "mem m: [UInt[8]; N + 1];" ==
  "(mem \"m\" (index (name \"UInt\") ((num 8))) (binary add (name \"N\") (num 1)))"
#guard stFails "mem m: T;" .S001 8
#guard stFails "mem m: [T; 4] = 0;" .S001 15
#guard st "[T; 4];" == "(expr (arraytype (name \"T\") (num 4)))"
#guard stFails "[T; 4] = 1;" .S001 8
#guard match parseSource defaultSyntaxDepth (ctBody "a.1[0] = x;") with
  | .ok [.fn _ _ _ _ _ [.assign p (.index q (.select r _ l 1) _) _]] =>
    p == ⟨2, 1⟩ && q == ⟨2, 1⟩ && r == ⟨2, 1⟩ && l == ⟨2, 3⟩
  | _ => false

/-! A statement that starts with `if` is an expression statement, and needs its `;`. -/
#guard st "if (c) { a } else { b };" == "(expr (cond (name \"c\") (name \"a\") (name \"b\")))"
#guard fails "fn f() -> T {\nif (c) { a } else { b }\n}" .S001 3 1
#guard stFails "if (c) { x = 1; } else { b };" .S001 12

/-! Expressions: each primary and postfix form. -/
#guard ex "42" == "(num 42)"
#guard ex "0x1F" == "(num 31)"
#guard ex "0b101" == "(num 5)"
#guard ex "123456789012345678901234567890" == "(num 123456789012345678901234567890)"
#guard ex "\"a\\n\"" == "(str \"a\\n\")"
#guard ex "false" == "(bool false)"
#guard ex "UInt[8](3)" == "(call (index (name \"UInt\") ((num 8))) ((num 3)))"
#guard ex "resize(UInt[A + B], a)" ==
  "(call (name \"resize\") ((index (name \"UInt\") ((binary add (name \"A\") (name \"B\")))) " ++
  "(name \"a\")))"
#guard ex "f(1,)" == "(call (name \"f\") ((num 1)))"
#guard ex "(f)(x)" == "(call (name \"f\") ((name \"x\")))"
#guard ex "if (c) { 1 } else { 2 }" == "(cond (name \"c\") (num 1) (num 2))"
#guard ex "(if (c) { 1 } else { 2 }) + 1" ==
  "(binary add (cond (name \"c\") (num 1) (num 2)) (num 1))"

/-!
The container forms. `(a)` groups, and `(a,)` is a tuple. A selector `.N` takes each number
literal. `t.0(x)` calls the element `t.0`.
-/
#guard ex "()" == "(unit)"
#guard ex "(a)" == "(name \"a\")"
#guard ex "(a,)" == "(tuple ((name \"a\")))"
#guard ex "(a, (b, c),)" == "(tuple ((name \"a\") (tuple ((name \"b\") (name \"c\")))))"
#guard ex "[]" == "(array ())"
#guard ex "[a, [], ()]" == "(array ((name \"a\") (array ()) (unit)))"
#guard ex "[if (c) { 1 } else { 2 },]" == "(array ((cond (name \"c\") (num 1) (num 2))))"
#guard ex "t.0" == "(select (name \"t\") 0)"
#guard ex "t.0x1.0b10" == "(select (select (name \"t\") 1) 2)"
#guard ex "(x, true).0" == "(select (tuple ((name \"x\") (bool true))) 0)"
#guard ex "t.0(x)" == "(call (select (name \"t\") 0) ((name \"x\")))"
#guard ex "a[0].1.f" == "(field (select (index (name \"a\") ((num 0))) 1) \"f\")"
#guard ex "-t.1" == "(unary neg (select (name \"t\") 1))"
#guard match constValue "(a, b).0x1" with
  | .ok (.select p (.tuple q _) l 1) => p == ⟨1, 14⟩ && q == ⟨1, 14⟩ && l == ⟨1, 21⟩
  | _ => false
#guard match constValue "[()]" with
  | .ok (.array p [.unit q]) => p == ⟨1, 14⟩ && q == ⟨1, 15⟩
  | _ => false

/-!
An array type `[T; N]` in an expression. Its element is a type, and its length is an
expression. A suffix can follow it.
-/
#guard ex "[UInt[8]; 4]" == "(arraytype (index (name \"UInt\") ((num 8))) (num 4))"
#guard ex "f(a, [T; 4])" == "(call (name \"f\") ((name \"a\") (arraytype (name \"T\") (num 4))))"
#guard ex "[[T; 2]; N + 1]" ==
  "(arraytype (array (name \"T\") (num 2)) (binary add (name \"N\") (num 1)))"
#guard ex "[(T, ()); 4]" == "(arraytype (tuple ((name \"T\") (unit))) (num 4))"
#guard ex "[(T); 4]" == "(arraytype (name \"T\") (num 4))"
#guard ex "[T; 4]()" == "(call (arraytype (name \"T\") (num 4)) ())"
#guard ex "[T; 4][1]" == "(index (arraytype (name \"T\") (num 4)) ((num 1)))"
#guard ex "[[T; 2], [U; 3]]" ==
  "(array ((arraytype (name \"T\") (num 2)) (arraytype (name \"U\") (num 3))))"
#guard match constValue "[UInt[8]; (n)]" with
  | .ok (.arrayType p (.index q (.name r _) [.num s 8]) (.name u _)) =>
    p == ⟨1, 14⟩ && q == ⟨1, 15⟩ && r == ⟨1, 15⟩ && s == ⟨1, 20⟩ && u == ⟨1, 25⟩
  | _ => false

/-!
`S001` at an array type in an expression. A `;` directly in the bracket makes an array type, so
the element is a type. The first token that is not part of a type is `S001`.
-/
#guard ex "[0; 4]" == "error S001 1:15"
#guard ex "[a, b; c]" == "error S001 1:16"
#guard ex "[a + b; 4]" == "error S001 1:17"
#guard ex "[a.b; 4]" == "error S001 1:16"
#guard ex "[[a, b]; 4]" == "error S001 1:17"
#guard ex "[[0; 2]; 4]" == "error S001 1:16"
#guard ex "[T $; 4]" == "error S001 1:17"
#guard ex "[$; 4]" == "error S001 1:15"
#guard ex "[T; ]" == "error S001 1:18"
#guard ex "[T; 4; 5]" == "error S001 1:19"
#guard ex "[(a; b)]" == "error S001 1:17"
#guard ex "[f(x); 4]" == "error S004 1:16"
#guard ex "[a.f(x); 4]" == "error S001 1:16"
#guard ex "[fn() -> T; 4]" == "(arraytype (fn () (name \"T\")) (num 4))"
#guard ex "[@TypeOf(x); 4]" == "error S004 1:15"
#guard ex "[a::T; 4]" == "error S004 1:16"

/-! `S001` and `S004` at the other container forms. -/
#guard ex "(T; 4)" == "error S001 1:16"
#guard ex "(,)" == "error S001 1:15"
#guard ex "(a b)" == "error S001 1:17"
#guard ex "(a,,)" == "error S001 1:17"
#guard ex "[,]" == "error S001 1:15"
#guard ex "[a b]" == "error S001 1:17"
#guard ex "t.\"s\"" == "error S001 1:16"

/-!
A receiver call `x.m(args)` is a `method` node at the position of the receiver. A suffix can
follow it. `(x.m)(args)` calls the field `x.m`, and `t.0(x)` calls the element `t.0`.
-/
#guard ex "t.f(x)" == "(method (name \"t\") \"f\" ((name \"x\")))"
#guard ex "t.0.f(x)" == "(method (select (name \"t\") 0) \"f\" ((name \"x\")))"
#guard ex "xs.push(1,)" == "(method (name \"xs\") \"push\" ((num 1)))"
#guard ex "x.f()" == "(method (name \"x\") \"f\" ())"
#guard ex "a.b.c(1).d" ==
  "(field (method (field (name \"a\") \"b\") \"c\" ((num 1))) \"d\")"
#guard ex "x.f(a)(b)" == "(call (method (name \"x\") \"f\" ((name \"a\"))) ((name \"b\")))"
#guard ex "x.f()[0].g(y.h())" ==
  "(method (index (method (name \"x\") \"f\" ()) ((num 0))) \"g\" " ++
  "((method (name \"y\") \"h\" ())))"
#guard ex "-x.f() + 1" == "(binary add (unary neg (method (name \"x\") \"f\" ())) (num 1))"
#guard ex "(x.f)(1)" == "(call (field (name \"x\") \"f\") ((num 1)))"
#guard ex "(a + b).f(c)" ==
  "(method (binary add (name \"a\") (name \"b\")) \"f\" ((name \"c\")))"
#guard match constValue "(a).f(x)" with
  | .ok (.method p (.name q _) m [.name r _]) =>
    p == ⟨1, 14⟩ && q == ⟨1, 15⟩ && m.pos == ⟨1, 18⟩ && r == ⟨1, 20⟩
  | _ => false
#guard match constValue "x.f().g()" with
  | .ok (.method p (.method q _ _ _) m []) => p == ⟨1, 14⟩ && q == ⟨1, 14⟩ && m.pos == ⟨1, 20⟩
  | _ => false
#guard st "xs.push(x);" == "(expr (method (name \"xs\") \"push\" ((name \"x\"))))"
#guard ex "x.f(" == "error S001 1:18"
#guard ex "x.f(a b)" == "error S001 1:20"
#guard ex "x.f(a,,)" == "error S001 1:20"

/-!
A function type `fn (T, mut U) -> V` is a type. Arrows bind right, and the result type takes
each suffix after it. A `,` can end the parameters. `(fn () -> T)[8]` is an index of a function
type: the parser accepts it, and pass 4 rejects it.
-/
#guard dump "const A: fn (fn () -> Bool) -> fn () -> UInt[8] = 0;" ==
  "(const \"A\" (fn ((fnparam false (fn () (name \"Bool\")))) " ++
  "(fn () (index (name \"UInt\") ((num 8))))) (num 0))\n"
#guard dump "const A: fn (T,) -> U = 0;" ==
  "(const \"A\" (fn ((fnparam false (name \"T\"))) (name \"U\")) (num 0))\n"
#guard dump "const A: fn (mut T, U) -> V = 0;" ==
  "(const \"A\" (fn ((fnparam true (name \"T\")) (fnparam false (name \"U\"))) " ++
  "(name \"V\")) (num 0))\n"
#guard dump "const A: List[fn () -> Bool] = 0;" ==
  "(const \"A\" (index (name \"List\") ((fntype () (name \"Bool\")))) (num 0))\n"
#guard dump "const A: (fn () -> UInt)[8] = 0;" ==
  "(const \"A\" (index (fn () (name \"UInt\")) ((num 8))) (num 0))\n"
#guard match parseSource defaultSyntaxDepth "const A: (fn (B) -> C)[8] = 0;" with
  | .ok [.const _ _ (.index p (.fn q [.mk false (.name r _)] _) _) _] =>
    p == ⟨1, 10⟩ && q == ⟨1, 11⟩ && r == ⟨1, 15⟩
  | _ => false

/-! In an expression, a function type is a unary operand. A suffix after it is on its result. -/
#guard ex "fn () -> UInt[8]" == "(fntype () (index (name \"UInt\") ((num 8))))"
#guard ex "-fn (A) -> B + 1" ==
  "(binary add (unary neg (fntype ((fnparam false (name \"A\"))) (name \"B\"))) (num 1))"
#guard ex "(fn () -> B)(x)" == "(call (fntype () (name \"B\")) ((name \"x\")))"
#guard ex "f(List[fn () -> Bool])" ==
  "(call (name \"f\") ((index (name \"List\") ((fntype () (name \"Bool\"))))))"
#guard st "fn () -> T;" == "(expr (fntype () (name \"T\")))"
#guard match constValue "fn (mut A) -> B" with
  | .ok (.fnType p [.mk true (.name q _)] (.name r _)) =>
    p == ⟨1, 14⟩ && q == ⟨1, 22⟩ && r == ⟨1, 28⟩
  | _ => false

/-! `S001` at a function type, and at a `comptime` mark on a parameter type. -/
#guard ex "fn () -> B.x" == "error S001 1:24"
#guard ex "fn (,) -> B" == "error S001 1:18"
#guard ex "fn (T U) -> B" == "error S001 1:20"
#guard ex "fn () B" == "error S001 1:20"
#guard ex "fn () -> fn" == "error S001 1:25"
#guard ex "fn () -> UInt(8)" == "error S004 1:27"
#guard fails "const A: fn (comptime T) -> V = 0;" .S001 1 14
#guard fails "const A: fn (T, comptime U) -> V = 0;" .S001 1 17
#guard fails "const A: fn (mut comptime U) -> V = 0;" .S001 1 18

/-! The container types. `(T)` groups, and a suffix can follow each type form. -/
#guard dump "const A: () = ();" == "(const \"A\" (unit) (unit))\n"
#guard dump "const A: (T) = 0;" == "(const \"A\" (name \"T\") (num 0))\n"
#guard dump "const A: (T,) = 0;" == "(const \"A\" (tuple ((name \"T\"))) (num 0))\n"
#guard dump "const A: (T, (), [U; N + 1],) = 0;" ==
  "(const \"A\" (tuple ((name \"T\") (unit) (array (name \"U\") " ++
  "(binary add (name \"N\") (num 1))))) (num 0))\n"
#guard dump "const A: [[Bool; 2]; 3] = 0;" ==
  "(const \"A\" (array (array (name \"Bool\") (num 2)) (num 3)) (num 0))\n"
#guard dump "const A: (T)[1] = 0;" ==
  "(const \"A\" (index (name \"T\") ((num 1))) (num 0))\n"
#guard fails "const A: (,) = 0;" .S001 1 11
#guard fails "const A: (T U) = 0;" .S001 1 13
#guard fails "const A: (T, U V) = 0;" .S001 1 16
#guard fails "const A: [] = 0;" .S001 1 11
#guard fails "const A: [T] = 0;" .S001 1 12
#guard fails "const A: [T, U] = 0;" .S001 1 12
#guard fails "const A: [T; ] = 0;" .S001 1 14
#guard dump "const A: (fn() -> T,) = 0;" == "(const \"A\" (tuple ((fn () (name \"T\")))) (num 0))\n"
#guard fails "const A: (T)(x) = 0;" .S004 1 13
#guard fails "const A: [T; 2](x) = 0;" .S004 1 16

/-! Precedence: each level binds tighter than the one before it. -/
#guard ex "a || b && c" == "(binary lor (name \"a\") (binary land (name \"b\") (name \"c\")))"
#guard ex "a && b | c" == "(binary land (name \"a\") (binary or (name \"b\") (name \"c\")))"
#guard ex "a | b ^ c" == "(binary or (name \"a\") (binary xor (name \"b\") (name \"c\")))"
#guard ex "a ^ b & c" == "(binary xor (name \"a\") (binary and (name \"b\") (name \"c\")))"
#guard ex "a & b == c" == "(binary and (name \"a\") (binary eq (name \"b\") (name \"c\")))"
#guard ex "a != b << c" == "(binary ne (name \"a\") (binary shl (name \"b\") (name \"c\")))"
#guard ex "a >> b +% c" == "(binary shr (name \"a\") (binary addw (name \"b\") (name \"c\")))"
#guard ex "a -% b *% c" == "(binary subw (name \"a\") (binary mulw (name \"b\") (name \"c\")))"
#guard ex "a / -b" == "(binary div (name \"a\") (unary neg (name \"b\")))"
#guard ex "!a.b" == "(unary not (field (name \"a\") \"b\"))"
#guard ex "~-x" == "(unary inv (unary neg (name \"x\")))"
#guard ex "a * b + c" == "(binary add (binary mul (name \"a\") (name \"b\")) (name \"c\"))"
#guard ex "a < b == c" == "error S001 1:20"
#guard ex "a <= b" == "(binary le (name \"a\") (name \"b\"))"
#guard ex "a >= b" == "(binary ge (name \"a\") (name \"b\"))"
#guard ex "a % b" == "(binary rem (name \"a\") (name \"b\"))"

/-! Each binary level is left-associative, except comparisons, which do not chain. -/
#guard ex "a - b - c" == "(binary sub (binary sub (name \"a\") (name \"b\")) (name \"c\"))"
#guard ex "a - (b - c)" == "(binary sub (name \"a\") (binary sub (name \"b\") (name \"c\")))"
#guard ex "a || b || c" == "(binary lor (binary lor (name \"a\") (name \"b\")) (name \"c\"))"
#guard ex "a < b < c" == "error S001 1:20"
#guard ex "(a < b) < c" == "(binary lt (binary lt (name \"a\") (name \"b\")) (name \"c\"))"
#guard ex "a == b & c == d" ==
  "(binary and (binary eq (name \"a\") (name \"b\")) (binary eq (name \"c\") (name \"d\")))"

/-! `if` is not an operand without parentheses. -/
#guard ex "a + if (c) { 1 } else { 2 }" == "error S001 1:18"

/-! A node is at its first token, also at a `(`. -/
#guard match constValue "(a + b) * c" with
  | .ok (.binary p .mul (.binary q .add ..) _) => p == ⟨1, 14⟩ && q == ⟨1, 15⟩
  | _ => false
#guard match constValue "x.f[1]" with
  | .ok (.index p (.field q _ f) _) => p == ⟨1, 14⟩ && q == ⟨1, 14⟩ && f.pos == ⟨1, 16⟩
  | _ => false

/-! `S004`: the syntax of a later slice, at the token of the module documentation. -/
#guard fails "import a as b;" .S004 1 1
#guard fails "pub const N: T = 1;" .S004 1 1
#guard fails "pub module M() {}" .S004 1 1
#guard fails "import a::b;" .S004 1 1
#guard fails "extern module M() = \"m\" {}" .S004 1 1
#guard fails "module M() conforms C() using D() {}" .S004 1 12
#guard fails "module M() domains(a, b) {}" .S004 1 23
#guard fails "fn f(x: a::T) -> T {}" .S004 1 10
#guard fails "fn f() -> @Struct(x) {}" .S004 1 11
#guard fails "fn f() -> @typeInfo(x) {}" .S004 1 11
#guard fails "fn f() -> @field(x, \"f\") {}" .S004 1 11
#guard fails "fn f() -> @ports(M) {}" .S004 1 11
#guard fails "fn f() -> a::T {}" .S004 1 12
#guard fails "fn f() -> T::U {}" .S004 1 12
#guard fails "fn f() -> @TypeOf(x) {}" .S004 1 11
#guard stFails "@TypeOf(x);" .S004 1
#guard stFails "@typeInfo(T);" .S004 1
#guard stFails "reg r: T in d = 0;" .S004 10
#guard stFails "wire w: T in d;" .S004 11
#guard stFails "mem m: [T; 4] in d;" .S004 15
#guard stFails "input i: T in d;" .S004 12
#guard stFails "input i[0]: T in d;" .S004 15
#guard stFails "instance u = M() with { clock = d };" .S004 18
#guard stFails "instance u = p::M();" .S004 15
#guard stFails "@field(a, \"i\") = 1;" .S004 1
#guard stFails "@field(a.b, \"c\") := 1;" .S004 1

/-! The message of the error of `s`, or the empty string. -/
def message (s : String) : String :=
  match parseSource defaultSyntaxDepth s with
  | .error e => e.msg
  | .ok _ => ""

/-! The text "`as` on an indexed port" names the family in its fix. -/
#guard message (ctBody "output o[0]: T as k;") == Parse.asIndexedText "o"
#guard Parse.asIndexedText "o" == "an indexed port takes no `as` key; declare a scalar port " ++
  "with `as PortKey(\"o\", true, k)`"

/-!
An enum (slice 3): the tag type, and each variant with its payload types and its tag value. A
`,` can end the variants and the payload types. `A` and `A()` give one variant. A variant
without a tag value is `S001`. An enum with parameters is `S004` at its `(`.
-/
#guard dump "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4],) = 2, }" ==
  "(enum \"Op\" (index (name \"UInt\") ((num 2))) ((variant \"Add\" () (num 0)) " ++
  "(variant \"Load\" ((index (name \"UInt\") ((num 8)))) (num 1)) " ++
  "(variant \"Pair\" ((name \"Bool\") (index (name \"UInt\") ((num 4)))) (num 2))))\n"
#guard dump "enum E: UInt[1] {}" == "(enum \"E\" (index (name \"UInt\") ((num 1))) ())\n"
#guard dump "enum E: T { A() = 0 }" == dump "enum E: T { A = 0 }"
#guard dump "enum E: T { A = N + 1 }" ==
  "(enum \"E\" (name \"T\") ((variant \"A\" () (binary add (name \"N\") (num 1)))))\n"
#guard fails "enum E: T { A }" .S001 1 15
#guard fails "enum E: T { A(B) }" .S001 1 18
#guard fails "enum E: T { A = 0 B = 1 }" .S001 1 19
#guard fails "enum E: T { A = 0,, }" .S001 1 19
#guard fails "enum E { A = 0 }" .S001 1 8
#guard fails "enum E: T { A(,) = 0 }" .S001 1 15
#guard fails "enum E(comptime W: Nat): T { A = 0 }" .S004 1 7
#guard fails "module M() {}\nenum E(): T {}" .S004 2 7
#guard message "enum E(T): U {}" == "an enum with parameters is not supported yet; remove " ++
  "the parameters, and give each payload a fixed type"

/-!
A variant path `E::V` is a primary, and `E::V(args)` is a call of it. A package path is
`S004` with one text: the second `::` of an expression path, and the `::` of a type or of the
module of an `instance`.
-/
#guard ex "Op::Add" == "(path \"Op\" \"Add\")"
#guard ex "Op::Load(x, 1)" == "(call (path \"Op\" \"Load\") ((name \"x\") (num 1)))"
#guard ex "Op::Load()" == "(call (path \"Op\" \"Load\") ())"
#guard ex "-a::b" == "(unary neg (path \"a\" \"b\"))"
#guard ex "x+a::f(1)" ==
  "(binary add (name \"x\") (call (path \"a\" \"f\") ((num 1))))"
#guard ex "a::b.c" == "(field (path \"a\" \"b\") \"c\")"
#guard ex "a::b == c::d" == "(binary eq (path \"a\" \"b\") (path \"c\" \"d\"))"
#guard ex "a::b::c" == "error S004 1:18"
#guard ex "a::b::" == "error S004 1:18"
#guard ex "a::(b)" == "error S001 1:17"
#guard ex "a::1" == "error S001 1:17"
#guard ex "a::" == "error S001 1:17"
#guard st "Op::Load(x);" == "(expr (call (path \"Op\" \"Load\") ((name \"x\"))))"
#guard st "let y = Op::Add;" == "(local false \"y\" none (path \"Op\" \"Add\"))"
#guard stFails "Op::Add = 1;" .S001 9
#guard stFails "Op::Add.x := 1;" .S001 11
#guard message "const X: T = a::b::c;" == Parse.packagePathText
#guard message "fn f() -> a::T {}" == Parse.packagePathText
#guard message "fn f(x: a::T) -> T {}" == Parse.packagePathText
#guard message (ctBody "instance u = p::M();") == Parse.packagePathText
#guard Parse.packagePathText == "a package path is not supported yet; in this slice, a path " ++
  "is a variant `E::V` of an enum `E`, in an expression or a pattern"

/-!
A `match` (slice 3) is an expression at the level of `if`, also as an argument. Each pattern
kind, a negative literal, binders with `_`, and a trailing `,`. `E::V()` is the pattern `E::V`.
A `match` can have zero arms. An operand of an operator needs parentheses around it.
-/
#guard ex ("match (x) { 0 => 1, -3 => 2, true => a, false => b, Op::Add => 3, " ++
    "Op::Load(v) => v, Op::Pair(a, _,) => a, _ => 2, }") ==
  "(match (name \"x\") ((arm (int false 0) (num 1)) (arm (int true 3) (num 2)) " ++
  "(arm (bool true) (name \"a\")) (arm (bool false) (name \"b\")) " ++
  "(arm (variant \"Op\" \"Add\" ()) (num 3)) " ++
  "(arm (variant \"Op\" \"Load\" ((some \"v\"))) (name \"v\")) " ++
  "(arm (variant \"Op\" \"Pair\" ((some \"a\") none)) (name \"a\")) (arm (wild) (num 2))))"
#guard ex "match (x) { Op::Add() => 1 }" == ex "match (x) { Op::Add => 1 }"
#guard ex "match (x) {}" == "(match (name \"x\") ())"
#guard ex "match (x) { _ => match (y) { _ => 1 } }" ==
  "(match (name \"x\") ((arm (wild) (match (name \"y\") ((arm (wild) (num 1)))))))"
#guard ex "if (match (x) { _ => c }) { 1 } else { 2 }" ==
  "(cond (match (name \"x\") ((arm (wild) (name \"c\")))) (num 1) (num 2))"
#guard ex "f(match (x) { _ => 1 })" ==
  "(call (name \"f\") ((match (name \"x\") ((arm (wild) (num 1))))))"
#guard ex "a + (match (x) { _ => 1 })" ==
  "(binary add (name \"a\") (match (name \"x\") ((arm (wild) (num 1)))))"
#guard st "return match (x) { _ => 0 };" ==
  "(ret (some (match (name \"x\") ((arm (wild) (num 0))))))"
#guard st "match (x) { _ => 0 };" == "(expr (match (name \"x\") ((arm (wild) (num 0)))))"
#guard stFails "let match = 1;" .S001 5
#guard ex "a + match (x) { _ => 1 }" == "error S001 1:18"
#guard ex "match (x) { _ => 1 } + 1" == "error S001 1:35"
#guard ex "a => b" == "error S001 1:16"
#guard ex "match x { _ => 1 }" == "error S001 1:20"
#guard ex "match (x) { 1 => 1 2 => 3 }" == "error S001 1:33"
#guard ex "match (x) { 1 => 1,, }" == "error S001 1:33"
#guard ex "match (x) { _ => 1 " == "error S001 1:33"

/-!
`S001` in a pattern is at the first token that is not valid, with the text of section 6.2.
These are a bare name, a nested pattern, an expression, a range, `|`, and a `-` without a
number. The variant name `_` has its own text. A third part of a path is `S004` with the text of
a package path.
-/
#guard ex "match (x) { a => 1 }" == "error S001 1:28"
#guard ex "match (x) { E::V(F::W) => 1 }" == "error S001 1:32"
#guard ex "match (x) { E::V(1) => 1 }" == "error S001 1:31"
#guard ex "match (x) { E::V(a b) => 1 }" == "error S001 1:33"
#guard ex "match (x) { E::1 => 1 }" == "error S001 1:29"
#guard ex "match (x) { (1) => 1 }" == "error S001 1:26"
#guard ex "match (x) { 1 + 2 => 1 }" == "error S001 1:28"
#guard ex "match (x) { 1..3 => 1 }" == "error S001 1:27"
#guard ex "match (x) { 1 | 2 => 1 }" == "error S001 1:28"
#guard ex "match (x) { - x => 1 }" == "error S001 1:28"
#guard ex "match (x) { _::V => 1 }" == "error S001 1:27"
#guard ex "match (x) { E::V::W => 1 }" == "error S004 1:30"
#guard ex "match (x) { E::_ => 1 }" == "error S001 1:29"
#guard ex "match (x) { E::_(a) => 1 }" == "error S001 1:29"
#guard message "const X: T = match (x) { E::_ => 1 };" == Parse.variantWildText
#guard Parse.variantWildText == "a variant pattern names a variant, not `_`; write `_` alone " ++
  "to match each other value"
#guard message "const X: T = match (x) { a => 1 };" == Parse.patternText
#guard message "const X: T = match (x) { E::V::W => 1 };" == Parse.packagePathText
#guard Parse.patternText == "expected a pattern: an integer, `true`, `false`, `E::V(..)`, " ++
  "or `_`; compare with a constant in an `if`"

/-!
A `fn` without `comptime` parses a port (F37), also in a nested block, and each other statement:
a resource, an instance, and a `:=`.
-/
def plainBody (s : String) : String := "fn f() -> T {\n" ++ s ++ "\n}"
#guard (parseSource defaultSyntaxDepth
  (plainBody "input i: Bool;\noutput o: Bool as \"q\";")).toBool
#guard (parseSource defaultSyntaxDepth
  (plainBody "let x = 1;\n{\ncomptime if (c) { input i[0]: Bool; }\n}")).toBool
#guard (parseSource defaultSyntaxDepth
  (plainBody "comptime for i in 0..2 {\noutput o: Bool as \"o\" + str(i);\n}")).toBool
#guard (parseSource defaultSyntaxDepth (plainBody "let x = 1;\nx = 2;\nreturn x;")).toBool
#guard (parseSource defaultSyntaxDepth (plainBody
  "reg r: Bool = false;\nwire w: Bool;\nmem m: [Bool; 4];\ninstance u = M();\nw := r;")).toBool
#guard (parseSource defaultSyntaxDepth (plainBody
  "let x = 1;\n{\ncomptime if (c) { wire w: Bool; }\n}")).toBool
#guard (parseSource defaultSyntaxDepth (plainBody
  "comptime for i in 0..2 {\nreg r: Bool = false;\n}")).toBool
#guard (parseSource defaultSyntaxDepth (ctBody "input i: Bool;\nreturn 1;")).toBool
#guard (parseSource defaultSyntaxDepth (ctBody "wire w: Bool;\nreturn 1;")).toBool
#guard (parseSource defaultSyntaxDepth "module M() {\nwire w: Bool;\n}").toBool
#guard (parseSource defaultSyntaxDepth "module M() {\nmem m: [Bool; 4];\n}").toBool
#guard stFails "@field(a, \"0\") = 1;" .S004 1
#guard stFails "@field(a, b) = 1;" .S004 1
#guard stFails "@field(x, \"f\") = 1;" .S004 1
#guard ex "@typeInfo(a, b)" == "error S004 1:14"
#guard ex "@TypeOf(a.b, c)" == "error S004 1:14"
#guard ex "(f(a, b))" == "(call (name \"f\") ((name \"a\") (name \"b\")))"
#guard ex "@Struct(T)" == "error S004 1:14"
#guard ex "@ports(M)" == "error S004 1:14"
#guard ex "@field(x, \"f\")" == "error S004 1:14"
#guard ex "@TypeOf(x)" == "error S004 1:14"
#guard ex "@TypeOf(f(a, b), (c)), d)" == "error S004 1:14"

/-!
A struct, with and without parameters, and a `type` alias at an item and at a statement. A
struct without parentheses and a struct with `()` have no parameters. A `,` can end the fields.
-/
#guard dump "struct P(comptime W: Nat) { a: UInt[W], b: Bool, }" ==
  "(struct \"P\" ((param comptime \"W\" (name \"Nat\"))) ((structfield \"a\" " ++
  "(index (name \"UInt\") ((name \"W\")))) (structfield \"b\" (name \"Bool\"))))\n"
#guard dump "struct P {}" == "(struct \"P\" () ())\n"
#guard dump "struct P() {}" == "(struct \"P\" () ())\n"
#guard dump "struct P(comptime A: Nat, comptime B: Type,) { a: [T; A] }" ==
  "(struct \"P\" ((param comptime \"A\" (name \"Nat\")) (param comptime \"B\" (name \"Type\"))) " ++
  "((structfield \"a\" (array (name \"T\") (name \"A\")))))\n"
#guard dump "type A = [UInt[8]; 4];" ==
  "(alias \"A\" (array (index (name \"UInt\") ((num 8))) (num 4)))\n"
#guard st "type A = (T, U);" == "(alias \"A\" (tuple ((name \"T\") (name \"U\"))))"
#guard dump "fn f() -> T { type A = T; }" ==
  "(fn false \"f\" () (name \"T\") ((alias \"A\" (name \"T\"))))\n"
#guard match parseSource defaultSyntaxDepth "struct P(comptime W: Nat) {\n  a: T,\n}" with
  | .ok [.struct p n [q] [f]] =>
    p == ⟨1, 1⟩ && n.pos == ⟨1, 8⟩ && q.pos == ⟨1, 10⟩ && q.name.pos == ⟨1, 19⟩ &&
      f.name.pos == ⟨2, 3⟩
  | _ => false
#guard match parseSource defaultSyntaxDepth "\ntype A = T;" with
  | .ok [.alias p n (.name q _)] => p == ⟨2, 1⟩ && n.pos == ⟨2, 6⟩ && q == ⟨2, 10⟩
  | _ => false
#guard match parseSource defaultSyntaxDepth (ctBody "  type A = T;") with
  | .ok [.fn _ _ _ _ _ [.alias p n _]] => p == ⟨2, 3⟩ && n.pos == ⟨2, 8⟩
  | _ => false

/-!
A function parameter has the mode none, `comptime`, or `mut`. A `comptime fn` can have a `mut`
parameter.
-/
#guard dump "fn f(mut xs: L, comptime T: Type, x: T) -> T {}" ==
  "(fn false \"f\" ((param mut \"xs\" (name \"L\")) (param comptime \"T\" (name \"Type\")) " ++
  "(param none \"x\" (name \"T\"))) (name \"T\") ())\n"
#guard dump "comptime fn g(mut n: Nat) -> () {}" ==
  "(fn true \"g\" ((param mut \"n\" (name \"Nat\"))) (unit) ())\n"
#guard match parseSource defaultSyntaxDepth "fn f(x: T,\n  mut y: T) -> T {}" with
  | .ok [.fn _ _ _ [_, q] _ _] => q.pos == ⟨2, 3⟩ && q.name.pos == ⟨2, 7⟩
  | _ => false

/-!
`S001` at the second mark of a parameter, and at `mut` of a module or a struct parameter. The
parser expects the name after the first mark.
-/
#guard fails "fn f(comptime mut x: T) -> T {}" .S001 1 15
#guard fails "fn f(mut comptime x: T) -> T {}" .S001 1 10
#guard fails "fn f(mut mut x: T) -> T {}" .S001 1 10
#guard fails "fn f(comptime comptime x: T) -> T {}" .S001 1 15
#guard fails "fn f(x: T, mut: T) -> T {}" .S001 1 15
#guard fails "comptime fn f(comptime mut x: T) -> T {}" .S001 1 24
#guard fails "module M(comptime mut W: Nat) {}" .S001 1 19
#guard fails "struct P(comptime mut W: Nat) {}" .S001 1 19

/-!
`S001` at a struct and at an alias. A struct parameter without `comptime` is `S001` at its
name, and with `mut` it is `S001` at `mut`, as at a module.
-/
#guard fails "struct P(W: Nat) {}" .S001 1 10
#guard fails "struct P(mut W: Nat) {}" .S001 1 10
#guard fails "struct P(comptime W: Nat, V: Nat) {}" .S001 1 27
#guard fails "struct P(comptime W: Nat {}" .S001 1 26
#guard fails "struct P { a: T b: U }" .S001 1 17
#guard fails "struct P { a T }" .S001 1 14
#guard fails "struct P { a: T,, }" .S001 1 17
#guard fails "struct P { , }" .S001 1 12
#guard fails "struct P;" .S001 1 9
#guard fails "struct { }" .S001 1 8
#guard fails "struct P { a: T" .S001 1 16
#guard fails "type A = ;" .S001 1 10
#guard fails "type A: T;" .S001 1 7
#guard fails "type A = T" .S001 1 11
#guard fails "type A = 1;" .S001 1 10
#guard stFails "type A = T U;" .S001 12
#guard fails "struct P { a: T(x) }" .S004 1 16
#guard fails "pub struct P {}" .S004 1 1
#guard fails "pub type A = T;" .S004 1 1

/-! `S001`: the first token that does not match, a lexical error, or the end of the file. -/
#guard fails "x" .S001 1 1
#guard fails "comptime module M() {}" .S001 1 10
#guard fails "const N: T = ;" .S001 1 14
#guard fails "const N: T = 1" .S001 1 15
#guard fails "const N: T = 1\n" .S001 2 1
#guard fails "module M() {\n" .S001 2 1
#guard fails "module M(W: Nat) {}" .S001 1 10
#guard fails "module M(mut W: Nat) {}" .S001 1 10
#guard fails "module M() domains(a,,) {}" .S001 1 22
#guard fails "fn f() {}" .S001 1 8
#guard fails "const N: T[] = 1;" .S001 1 12
#guard fails "const N: T = @foo(1);" .S001 1 15
#guard fails "const N: T = f(1 2);" .S001 1 18
#guard fails "const N: T = 1 $ 2;" .S001 1 16
#guard stFails "f(x) = 1;" .S001 6
#guard stFails "(a) = 1;" .S001 5
#guard stFails "a + b = 1;" .S001 7
#guard stFails "comptime while (c) {}" .S001 10
#guard stFails "comptime if (c) {} else comptime if (d) {}" .S001 25

/-! The first error in position order: an `S004` before a lexical error, and back. -/
#guard fails "import x $" .S004 1 1
#guard fails "pub \"open" .S004 1 1
#guard fails "const N: T = $; import x;" .S001 1 14
#guard ex "@TypeOf(a, $)" == "error S004 1:14"
#guard fails ("import x " ++ "".pushn '9' 20000) .S004 1 1
#guard fails ("const N: T = " ++ "".pushn '9' 20000 ++ " 1;") .S001 1 14

/-!
A small syntax depth of 64. Brackets nest at most 64 deep, and the 65th is `S001` at that
bracket. An outermost expression or type of height 65 is `S001` at its first token.
-/
def parens (n : Nat) : String := "".pushn '(' n ++ "x" ++ "".pushn ')' n
def negs (n : Nat) : String := "".pushn '-' n ++ "x"
def chain (n : Nat) : String := " + ".intercalate (List.replicate n "a")
def calls (n : Nat) : String := String.join (List.replicate n "f(") ++ "x" ++ "".pushn ')' n
def fields (n : Nat) : String := "x" ++ String.join (List.replicate n ".f")
def blocks (n : Nat) : String := "".pushn '{' n ++ "".pushn '}' n
def methods (n : Nat) : String := "x" ++ String.join (List.replicate n ".f()")
def fnChain (n : Nat) : String := String.join (List.replicate n "fn () -> ") ++ "T"

#guard (constValue (parens 64) 64).toBool
#guard ex (parens 65) 64 == "error S001 1:78"
#guard ex (parens 1000) 64 == "error S001 1:78"
#guard !((st (blocks 63) 64).startsWith "error")
#guard stFails (blocks 64) .S001 64 64
#guard stFails ("comptime if (c) " ++ blocks 64) .S001 80 64
#guard fails ("module M() " ++ blocks 64 ++ "\n" ++ "x") .S001 2 1 64
#guard !((st ("{ x[" ++ parens 61 ++ "]; }") 64).startsWith "error")
#guard stFails ("{ x[" ++ parens 62 ++ "]; }") .S001 66 64

#guard (constValue (negs 63) 64).toBool
#guard ex (negs 64) 64 == "error S001 1:14"
#guard (constValue (chain 64) 64).toBool
#guard ex (chain 65) 64 == "error S001 1:14"
#guard (constValue (calls 63) 64).toBool
#guard (constValue (methods 63) 64).toBool
#guard ex (methods 64) 64 == "error S001 1:14"
#guard stFails (methods 64 ++ ";") .S001 1 64
#guard (constValue (fnChain 63) 64).toBool
#guard ex (fnChain 64) 64 == "error S001 1:14"
#guard fails ("const A: " ++ fnChain 64 ++ " = 0;") .S001 1 10 64
#guard ex (calls 64) 64 == "error S001 1:14"
#guard ex ("y + " ++ negs 63) 64 == "error S001 1:14"
#guard ex ("g(" ++ chain 65 ++ ")") 64 == "error S001 1:14"
#guard fails ("const N: T[" ++ chain 65 ++ "] = 1;") .S001 1 10 64
#guard stFails ("y + " ++ negs 63 ++ ";") .S001 1 64
#guard stFails ("x.a = " ++ negs 64 ++ ";") .S001 7 64
#guard stFails (fields 64 ++ " = 1;") .S001 1 64
#guard stFails ("instance u = M(a, " ++ negs 64 ++ ");") .S001 19 64
#guard stFails ("let x: T[" ++ chain 65 ++ "] = 1;") .S001 8 64

/-!
The height check runs only after a parse without another error. Thus an earlier and a later
syntax error both win over a height error.
-/
def high : String := "const B: T = " ++ chain 65 ++ ";"
#guard fails ("const A: T = ;\n" ++ high) .S001 1 14 64
#guard fails (high ++ "\nconst A: T = ;") .S001 2 14 64
#guard fails (high ++ "\nconst A: T = $;") .S001 2 14 64
#guard fails (high ++ "\nconst A: T = " ++ parens 65 ++ ";") .S001 2 78 64
#guard fails (high ++ "\nimport x;") .S004 2 1 64
#guard fails (high ++ "\n" ++ high) .S001 1 14 64

/-! The message of the first parse error. A message of the syntax depth names its flag. -/
def parseMsg (s : String) (depth : Nat) : String :=
  match parseSource depth s with
  | .error e => e.msg
  | .ok _ => "no error"

#guard parseMsg high 64 == "an expression or a type is higher than 64 levels; raise --syntax-depth"
#guard parseMsg ("const A: T = " ++ parens 65 ++ ";") 64 ==
  "brackets nest deeper than 64 levels; raise --syntax-depth"

/-! The default syntax depth: depth and height 4096 pass, and 4097 fails. -/
def elifs (n : Nat) : String :=
  String.join (List.replicate n "if (c) { x } else { ") ++ "x" ++ "".pushn '}' n
#guard (constValue (parens 4096)).toBool
#guard ex (parens 4097) == "error S001 1:4110"
#guard !((st (blocks 4095)).startsWith "error")
#guard stFails (blocks 4096) .S001 4096
#guard (constValue (chain 4096)).toBool
#guard ex (chain 4097) == "error S001 1:14"
#guard ex (chain 5000) == "error S001 1:14"
#guard (constValue (negs 4095)).toBool
#guard ex (negs 5000) == "error S001 1:14"
#guard (constValue (elifs 4095)).toBool
#guard ex (elifs 4096) == "error S001 1:14"
#guard (constValue (fields 4095)).toBool
#guard ex (fields 4096) == "error S001 1:14"
#guard (constValue (methods 4095)).toBool
#guard ex (methods 4096) == "error S001 1:14"
#guard (constValue (fnChain 4095)).toBool
#guard ex (fnChain 4096) == "error S001 1:14"

/-! A raised syntax depth accepts a deeper input. -/
#guard (constValue (parens 10000) 20000).toBool
#guard (constValue (chain 10000) 20000).toBool

/-!
The parse is linear. A quadratic look ahead makes these inputs too slow for the build. Each
statement starts with a name or a `(`.
-/
def body (n : Nat) (s : String) : String :=
  "fn f() -> T {\n" ++ String.join (List.replicate n s) ++ "}"
#guard (parseSource defaultSyntaxDepth (body 20000 "x;\n")).toBool
#guard (parseSource defaultSyntaxDepth (body 20000 "(x);\n")).toBool
#guard (parseSource defaultSyntaxDepth (body 10000 "x.a = (f(y, z));\n")).toBool
#guard (parseSource defaultSyntaxDepth (body 10000 "x[i].0 = ((y,), [z, ()]);\n")).toBool
#guard (parseSource defaultSyntaxDepth (body 10000 "x = [[(T, U); 2]; 3]();\n")).toBool
#guard (parseSource defaultSyntaxDepth (body 10000 "x.f(y).g(z.h());\n")).toBool
#guard ex ("".pushn '[' 4000 ++ "0" ++ String.join (List.replicate 4000 "; 1]")) ==
  "error S001 1:4014"

/-! The parser reads the text of the printer back to the same AST. -/
def p : Pos := ⟨1, 1⟩
def nm (s : String) : Ident := ⟨p, s⟩
def n (v : Nat) : Expr := .num p v
def v (s : String) : Expr := .name p s
def t (s : String) : TypeExpr := .name p s
def bin (op : BinOp) (l r : Expr) : Expr := .binary p op l r
def uint (w : Expr) : TypeExpr := .index p (t "UInt") [w]

def exprs : List Expr :=
  [bin .sub (bin .sub (v "a") (v "b")) (v "c"), bin .sub (v "a") (bin .sub (v "b") (v "c")),
   bin .lt (bin .lt (v "a") (v "b")) (v "c"), bin .eq (v "a") (bin .shl (v "b") (n 1)),
   bin .mul (bin .add (v "a") (v "b")) (.unary p .neg (.unary p .neg (v "x"))),
   bin .addw (v "a") (.cond p (.cond p (v "c") (v "d") (v "e")) (v "x") (v "y")),
   .unary p .not (bin .lor (v "a") (bin .land (v "b") (v "c"))),
   .call p (.index p (v "UInt") [n 8, v "W"]) [.str p "q\"\n", .bool p false],
   .field p (.unary p .inv (v "x")) (nm "y"), .index p (bin .add (v "a") (v "b")) [n 0]]

def counter : Item :=
  .module p (nm "Counter") [⟨p, .comptime, nm "W", t "Nat"⟩] (some [nm "clk"])
    [.input p (nm "en") .scalar (t "Bool"), .output p (nm "q") .scalar (uint (v "W")),
     .reg p (nm "r") (uint (v "W")) (n 0), .wire p (nm "w") (t "Bool"),
     .connect p (v "q") (v "r"), .connect p (.field p (v "u") (nm "d")) (v "w"),
     .inst p (nm "u") (nm "Child") [bin .add (v "W") (n 1)],
     .expr p (.cond p (v "en") (n 1) (n 0)),
     .ctFor p (nm "i") (n 0) (v "W") [.block p [], .ctIf p (v "c") [] (some [])]]

def helper : Item :=
  .fn p true (nm "g") [⟨p, .comptime, nm "n", t "Nat"⟩, ⟨p, .none, nm "x", uint (n 8)⟩] (t "Nat")
    [.local p true (nm "y") (some (t "Nat")) (v "n"), .local p false (nm "z") none (n 1),
     .assign p (v "y") (bin .add (v "y") (v "z")),
     .ctIf p (v "b") [.ret p (some (v "y"))] none, .ret p none]

#guard exprs.all fun e => roundtrip [.const p (nm "X") (t "T") e]
#guard roundtrip [counter, helper, .const p (nm "N") (uint (n 4)) (n 3)]
#guard roundtrip [.module p (nm "C") [] (some []) [], .module p (nm "D") [] none []]
#guard roundtrip
  [.module p (nm "M") [] none [.mem p (nm "m") (uint (n 8)) (bin .add (v "N") (n 1))]]
#guard roundtrip []

/-! Parse, print, and parse again. The second parse gives the AST of the first. -/
def reparse (s : String) : Bool :=
  match parseSource defaultSyntaxDepth s with
  | .ok items => roundtrip items
  | .error _ => false

#guard reparse "const X: T = (a.b)(x);"
#guard reparse "const X: T = ((a.b)(x).c)(y)[0];"
#guard reparse "fn f() -> T { (a.b)(x); return -(a.b)(x).c; }"
#guard reparse "const X: T = 1.f + --x - -(if (c) { a } else { b }).g + (\"s\".h)(1)[2];"
#guard reparse "fn f() -> T { x.a.b = y; comptime for i in a.b .. c {} (x)(y); }"
#guard reparse "fn f() -> T { x[i].0.b = (y,); t.1[f(())] := [[], (a, b)]; t.0(x); }"
#guard reparse "const X: ((T,), [U[2]; 3], ()) = 0;"
#guard reparse "struct P(comptime W: Nat,) { a: UInt[W], b: [(T, ()); W + 1], } struct Q() {}"
#guard reparse "type A = [UInt[8]; 4]; fn f() -> T { type B = (A,); return [[A; 2]; 3](); }"
#guard reparse "const X: T = f([T; 4], [(U); (n)][0], -[V; 1]().0);"
#guard reparse "fn f(mut xs: L, comptime T: Type) -> T { xs.push(x.f(1).g()); return (a + b).h(); }"
#guard reparse "comptime fn g(mut n: Nat, x: T) -> T { (x.f)(t.0.m()); return -x.f()[0]; }"
#guard reparse ("const X: (fn (mut A, fn () -> B) -> fn () -> C)[1] = " ++
  "(fn () -> UInt)[8] + -fn () -> D;")
#guard reparse ("fn f(g: fn (mut L,) -> ()) -> fn () -> T { fn () -> T; " ++
  "let h: List[fn () -> Bool] = g; return (fn () -> T)(x).y; }")
#guard reparse ("enum Op: UInt[2] { Add = 0, Load(UInt[8],) = 1, Pair(Bool, (T,)) = -x, }" ++
  "enum E: UInt[1] {} enum F: T { A() = if (c) { 1 } else { 2 } }")
#guard reparse "fn f() -> Op { Op::Load(x); return -Op::Add + E::V(a::b).c[0]; }"
#guard reparse ("fn f() -> T { match (x) { _ => 0 }; return match (match (y) {}) { -0 => a, " ++
  "1 => if (c) { b } else { match (z) { true => 1, false => 2, } }, E::V(a, _) => a, " ++
  "E::W() => (match (q) { _ => 1 }) + 1, _ => f(match (r) { E::X => 1 }), }; }")

/-!
The edge cases of the printer for `parse_print`. Each pair of operators nests in both
operands, and a prefix operator is on each operand.
-/
def constRoundtrip (e : Expr) : Bool := roundtrip [.const p (nm "X") (t "T") e]
def fnRoundtrip (ss : List Stmt) : Bool := roundtrip [.fn p false (nm "f") [] (t "T") ss]
def unOps : List UnOp := [.neg, .not, .inv]

#guard allBinOps.all fun o => allBinOps.all fun q =>
  constRoundtrip (bin o (bin q (v "a") (v "b")) (v "c")) &&
    constRoundtrip (bin o (v "a") (bin q (v "b") (v "c")))
#guard allBinOps.all fun o => allBinOps.all fun q => unOps.all fun u =>
  constRoundtrip (bin o (.unary p u (v "a")) (bin q (.unary p u (v "b")) (.unary p u (n 1))))
#guard unOps.all fun u => unOps.all fun w => constRoundtrip (.unary p u (.unary p w (v "x")))
#guard constRoundtrip (.call p (.field p (v "a") (nm "f")) [v "x"])
#guard constRoundtrip (.field p (n 5) (nm "f")) && constRoundtrip (.field p (n 0) (nm "x"))
#guard constRoundtrip (.str p "a\nb\rc\td\"e\\f") && constRoundtrip (.str p "")
#guard constRoundtrip (n (2 ^ 65536 - 1)) && !constRoundtrip (n (2 ^ 65536))
#guard fnRoundtrip [.expr p (.cond p (v "c") (v "a") (v "b")),
  .expr p (bin .add (.cond p (v "c") (v "a") (v "b")) (n 1)),
  .ctIf p (v "c") [] (some []), .ctIf p (v "c") [] none, .block p [],
  .ctFor p (nm "i") (.field p (n 0) (nm "x")) (n 5) [],
  .expr p (.index p (v "x") [n 1]), .expr p (bin .eq (.field p (v "x") (nm "y")) (v "y")),
  .assign p (.field p (.field p (v "a") (nm "b")) (nm "c")) (v "d")]

/-!
The printer and the parser agree on the container forms. A tuple with no element prints as
`()`, which is the unit value, so a tuple needs an element.
-/
def tupT (ts : List TypeExpr) : TypeExpr := .tuple p ts
#guard constRoundtrip (.unit p) && constRoundtrip (.tuple p [v "a"])
#guard constRoundtrip (.tuple p [.tuple p [n 1, .unit p], .array p []])
#guard !constRoundtrip (.tuple p [])
#guard constRoundtrip (.array p [.array p [n 0], .select p (v "t") p 2])
#guard constRoundtrip (.call p (.select p (.select p (v "t") p 0) p 1) [])
#guard constRoundtrip (.unary p .neg (.select p (.index p (v "a") [n 0]) p 0))
#guard constRoundtrip (.select p (bin .add (v "a") (v "b")) p 3)
#guard [TypeExpr.unit p, tupT [t "T"], tupT [t "T", .unit p], .array p (tupT [t "T"]) (n 4),
  .index p (tupT [t "T"]) [n 1], .array p (.array p (t "T") (v "N")) (bin .add (n 1) (n 2))].all
  fun ty => roundtrip [.const p (nm "X") ty (n 0)]
#guard constRoundtrip (.arrayType p (.array p (uint (n 8)) (n 2)) (bin .add (v "N") (n 1)))
#guard constRoundtrip (.call p (.arrayType p (tupT [t "T", .unit p]) (n 4)) [])
#guard constRoundtrip (.array p [.arrayType p (.index p (tupT [t "T"]) [n 1]) (n 0)])
#guard roundtrip [.struct p (nm "P") [⟨p, .comptime, nm "W", t "Nat"⟩]
    [⟨nm "a", uint (v "W")⟩, ⟨nm "b", .array p (t "Bool") (n 2)⟩],
  .struct p (nm "Q") [] [], .alias p (nm "A") (tupT [t "T"]),
  .fn p false (nm "f") [] (t "T") [.alias p (nm "B") (.array p (t "A") (n 3))]]
#guard fnRoundtrip [.assign p (.index p (v "a") [n 0]) (n 1),
  .connect p (.select p (.field p (v "u") (nm "d")) p 1) (v "x"),
  .assign p (.field p (.index p (.select p (v "t") p 0) [v "i", v "j"]) (nm "f")) (v "y")]

/-! The printer and the parser agree on function types, in a type and in an expression. -/
def fnT (ps : List FnParam) (r : TypeExpr) : TypeExpr := .fn p ps r
#guard [fnT [] (t "T"), fnT [.mk true (t "A"), .mk false (fnT [] (t "B"))] (fnT [] (uint (n 8))),
  .index p (fnT [] (t "T")) [n 8], tupT [fnT [] (t "T")], .array p (fnT [] (t "T")) (n 2),
  .index p (t "List") [.fnType p [] (t "Bool")]].all
  fun ty => roundtrip [.const p (nm "X") ty (n 0)]
#guard constRoundtrip (.fnType p [.mk true (fnT [] (t "A"))] (fnT [] (t "B")))
#guard constRoundtrip (.call p (.fnType p [] (t "T")) [v "x"])
#guard constRoundtrip (.index p (.fnType p [] (t "T")) [n 1])
#guard constRoundtrip (.unary p .neg (.fnType p [] (t "T")))
#guard constRoundtrip (bin .add (.fnType p [] (t "T")) (.fnType p [] (t "U")))
#guard fnRoundtrip [.expr p (.fnType p [] (t "T"))]

/-!
The printer and the parser agree on a `match`. The tests cover each pattern kind, a binder `_`,
and zero arms. They also cover a `match` as an operand, as a scrutinee, and as an arm.
-/
def mat (s : Expr) (arms : List (Pattern × Expr)) : Expr :=
  .match p s (arms.map fun a => .mk a.1 a.2)
def pv (ty w : String) (bs : List (Option String)) : Pattern :=
  .variant p (nm ty) (nm w) (bs.map (·.map nm))
#guard constRoundtrip (mat (v "x") [(.int p false 0, n 1), (.int p true 0, n 2),
  (.int p true 7, n 3), (.bool p true, v "a"), (.bool p false, v "b"),
  (pv "E" "V" [], n 4), (pv "E" "W" [some "a", none, some "b"], v "a"), (.wild p, n 5)])
#guard constRoundtrip (mat (mat (v "x") []) [(.wild p, mat (v "y") [(.wild p, n 1)])])
#guard constRoundtrip (bin .add (mat (v "x") [(.wild p, n 1)]) (.unary p .neg (mat (v "y") [])))
#guard constRoundtrip (.field p (mat (v "x") [(.wild p, .cond p (v "c") (n 1) (n 2))]) (nm "f"))
#guard fnRoundtrip [.expr p (mat (v "x") [(.wild p, n 0)]), .ret p (some (mat (n 1) []))]

end Silicon.Source.Test.Parse
