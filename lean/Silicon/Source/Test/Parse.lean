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
  "(fn false \"inc\" ((param false \"x\" (index (name \"UInt\") ((num 8))))) " ++
  "(index (name \"UInt\") ((num 8))) ((ret (some (binary addw (name \"x\") (num 1))))))\n"
#guard dump "comptime fn g(comptime n: Nat) -> Nat { return n; }" ==
  "(fn true \"g\" ((param true \"n\" (name \"Nat\"))) (name \"Nat\") " ++
  "((ret (some (name \"n\")))))\n"
#guard dump "module M() {}" == "(module \"M\" () none ())\n"
#guard dump "module M() domains() {}" == "(module \"M\" () (some ()) ())\n"
#guard dump "module M(comptime W: Nat, comptime B: Bool,) domains(clk,) {}" ==
  "(module \"M\" ((param true \"W\" (name \"Nat\")) (param true \"B\" (name \"Bool\"))) " ++
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
#guard st "input i: Bool;" == "(input \"i\" (name \"Bool\"))"
#guard st "output o: Bool;" == "(output \"o\" (name \"Bool\"))"
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
#guard stFails "a.x(1) = 1;" .S004 4
#guard stFails "mem m: [T; 4];" .S004 1
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
`S001` at an array type in an expression. An element that is no type, or no `;` after it, is
`S001` at the first token that neither an array type nor an array literal accepts. For an
element that is an expression, this is the `;`. An `S004` in the element stops the parse.
-/
#guard ex "[0; 4]" == "error S001 1:16"
#guard ex "[a, b; c]" == "error S001 1:19"
#guard ex "[a + b; 4]" == "error S001 1:20"
#guard ex "[a.b; 4]" == "error S001 1:18"
#guard ex "[[a, b]; 4]" == "error S001 1:21"
#guard ex "[[0; 2]; 4]" == "error S001 1:17"
#guard ex "[T $; 4]" == "error S001 1:17"
#guard ex "[$; 4]" == "error S001 1:15"
#guard ex "[T; ]" == "error S001 1:18"
#guard ex "[T; 4; 5]" == "error S001 1:19"
#guard ex "[(a; b)]" == "error S001 1:17"
#guard ex "[f(x); 4]" == "error S004 1:16"
#guard ex "[a.f(x); 4]" == "error S004 1:18"
#guard ex "[fn() -> T; 4]" == "error S004 1:15"
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
#guard ex "t.f(x)" == "error S004 1:17"
#guard ex "t.0.f(x)" == "error S004 1:19"

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
#guard fails "const A: (fn() -> T,) = 0;" .S004 1 11
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
#guard stFails "input i: T in d;" .S004 12
#guard stFails "input i[0]: T;" .S004 8
#guard stFails "output o: T as k;" .S004 13
#guard stFails "instance u = M() with { clock = d };" .S004 18
#guard stFails "instance u = p::M();" .S004 15
#guard stFails "@field(a, \"i\") = 1;" .S004 1
#guard stFails "@field(a.b, \"c\") := 1;" .S004 1

/-!
`S004`: a `fn` without `comptime` declares no port, resource, or instance. The position is the
keyword, also in a nested block. A `comptime fn` and a module parse these statements.
-/
def plainBody (s : String) : String := "fn f() -> T {\n" ++ s ++ "\n}"
#guard fails (plainBody "input i: Bool;") .S004 2 1
#guard fails (plainBody "output o: Bool;") .S004 2 1
#guard fails (plainBody "reg r: Bool = false;") .S004 2 1
#guard fails (plainBody "wire w: Bool;") .S004 2 1
#guard fails (plainBody "instance u = M();") .S004 2 1
#guard fails (plainBody "let x = 1;\n{\ncomptime if (c) { wire w: Bool; }\n}") .S004 4 19
#guard fails (plainBody "comptime for i in 0..2 {\nreg r: Bool = false;\n}") .S004 3 1
#guard (parseSource defaultSyntaxDepth (plainBody "let x = 1;\nx = 2;\nreturn x;")).toBool
#guard (parseSource defaultSyntaxDepth (ctBody "wire w: Bool;\nreturn 1;")).toBool
#guard (parseSource defaultSyntaxDepth "module M() {\nwire w: Bool;\n}").toBool
#guard stFails "@field(a, \"0\") = 1;" .S004 1
#guard stFails "@field(a, b) = 1;" .S004 1
#guard stFails "@field(x, \"f\") = 1;" .S004 1
#guard ex "@typeInfo(a, b)" == "error S004 1:14"
#guard ex "@TypeOf(a.b, c)" == "error S004 1:14"
#guard ex "(f(a, b))" == "(call (name \"f\") ((name \"a\") (name \"b\")))"
#guard ex "@Struct(T)" == "error S004 1:14"
#guard ex "@ports(M)" == "error S004 1:14"
#guard ex "@field(x, \"f\")" == "error S004 1:14"
#guard ex "-a::b" == "error S004 1:16"
#guard ex "x+a::f(1)" == "error S004 1:17"
#guard ex "a::b" == "error S004 1:15"
#guard ex "@TypeOf(x)" == "error S004 1:14"
#guard ex "@TypeOf(f(a, b), (c)), d)" == "error S004 1:14"

/-!
A struct, with and without parameters, and a `type` alias at an item and at a statement. A
struct without parentheses and a struct with `()` have no parameters. A `,` can end the fields.
-/
#guard dump "struct P(comptime W: Nat) { a: UInt[W], b: Bool, }" ==
  "(struct \"P\" ((param true \"W\" (name \"Nat\"))) ((structfield \"a\" " ++
  "(index (name \"UInt\") ((name \"W\")))) (structfield \"b\" (name \"Bool\"))))\n"
#guard dump "struct P {}" == "(struct \"P\" () ())\n"
#guard dump "struct P() {}" == "(struct \"P\" () ())\n"
#guard dump "struct P(comptime A: Nat, comptime B: Type,) { a: [T; A] }" ==
  "(struct \"P\" ((param true \"A\" (name \"Nat\")) (param true \"B\" (name \"Type\"))) " ++
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
  .module p (nm "Counter") [⟨p, true, nm "W", t "Nat"⟩] (some [nm "clk"])
    [.input p (nm "en") (t "Bool"), .output p (nm "q") (uint (v "W")),
     .reg p (nm "r") (uint (v "W")) (n 0), .wire p (nm "w") (t "Bool"),
     .connect p (v "q") (v "r"), .connect p (.field p (v "u") (nm "d")) (v "w"),
     .inst p (nm "u") (nm "Child") [bin .add (v "W") (n 1)],
     .expr p (.cond p (v "en") (n 1) (n 0)),
     .ctFor p (nm "i") (n 0) (v "W") [.block p [], .ctIf p (v "c") [] (some [])]]

def helper : Item :=
  .fn p true (nm "g") [⟨p, true, nm "n", t "Nat"⟩, ⟨p, false, nm "x", uint (n 8)⟩] (t "Nat")
    [.local p true (nm "y") (some (t "Nat")) (v "n"), .local p false (nm "z") none (n 1),
     .assign p (v "y") (bin .add (v "y") (v "z")),
     .ctIf p (v "b") [.ret p (some (v "y"))] none, .ret p none]

#guard exprs.all fun e => roundtrip [.const p (nm "X") (t "T") e]
#guard roundtrip [counter, helper, .const p (nm "N") (uint (n 4)) (n 3)]
#guard roundtrip [.module p (nm "C") [] (some []) [], .module p (nm "D") [] none []]
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
#guard roundtrip [.struct p (nm "P") [⟨p, true, nm "W", t "Nat"⟩]
    [⟨nm "a", uint (v "W")⟩, ⟨nm "b", .array p (t "Bool") (n 2)⟩],
  .struct p (nm "Q") [] [], .alias p (nm "A") (tupT [t "T"]),
  .fn p false (nm "f") [] (t "T") [.alias p (nm "B") (.array p (t "A") (n 3))]]
#guard fnRoundtrip [.assign p (.index p (v "a") [n 0]) (n 1),
  .connect p (.select p (.field p (v "u") (nm "d")) p 1) (v "x"),
  .assign p (.field p (.index p (.select p (v "t") p 0) [v "i", v "j"]) (nm "f")) (v "y")]

end Silicon.Source.Test.Parse
