import Silicon.Source.Parse

/-!
These tests check the parser at its public boundary. They check the AST dump of each slice 1
construct, and precedence and associativity. They check the code and the position of each
error. They also check that the parser reads the text of the printer back to the same AST.
-/

namespace Silicon.Source.Test.Parse

open Silicon.Source Parse

def errorText (e : Error) : String := s!"error {e.code} {e.pos.line}:{e.pos.col}"

def dump (s : String) : String :=
  match parseSource s with
  | .ok items => Print.dump items
  | .error e => errorText e

def fails (s : String) (code : ErrorCode) (line col : Nat) : Bool :=
  match parseSource s with
  | .error e => e.code == code && e.pos == ⟨line, col⟩
  | .ok _ => false

/-! The value of `const X: T = <s>;`. Its first token is at column 14. -/
def constValue (s : String) : Except Error Expr :=
  match parseSource ("const X: T = " ++ s ++ ";") with
  | .ok [.const _ _ _ v] => .ok v
  | .ok _ => .error ⟨.S001, ⟨0, 0⟩, "not one const"⟩
  | .error e => .error e

def ex (s : String) : String :=
  match constValue s with
  | .ok v => v.dump
  | .error e => errorText e

/-! The dump of the one statement `s` in a function body. -/
def st (s : String) : String :=
  match parseSource ("fn f() -> T {\n" ++ s ++ "\n}") with
  | .ok [.fn _ _ _ _ _ [x]] => x.dump
  | .ok _ => "not one statement"
  | .error e => errorText e

/-! `S001` or `S004` in the body `s` of a function, which starts on line 2. -/
def stFails (s : String) (code : ErrorCode) (col : Nat) : Bool :=
  fails ("fn f() -> T {\n" ++ s ++ "\n}") code 2 col

def roundtrip (items : List Item) : Bool :=
  match parseSource (Print.print items) with
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
#guard fails "type T = UInt[8];" .S004 1 1
#guard fails "struct S {}" .S004 1 1
#guard fails "extern module M() = \"m\" {}" .S004 1 1
#guard fails "module M() conforms C() using D() {}" .S004 1 12
#guard fails "module M() domains(a, b) {}" .S004 1 23
#guard fails "fn f(mut x: T) -> T {}" .S004 1 6
#guard fails "fn f() -> fn () -> T {}" .S004 1 11
#guard fails "fn f() -> (T, T) {}" .S004 1 11
#guard fails "fn f() -> () {}" .S004 1 11
#guard fails "fn f() -> [T; 4] {}" .S004 1 11
#guard fails "fn f() -> a::T {}" .S004 1 12
#guard fails "fn f() -> T(1) {}" .S004 1 12
#guard fails "fn f() -> @TypeOf(x) {}" .S004 1 11
#guard stFails "type T = Bool;" .S004 1
#guard stFails "mem m: [T; 4];" .S004 1
#guard stFails "reg r: T in d = 0;" .S004 10
#guard stFails "wire w: T in d;" .S004 11
#guard stFails "input i: T in d;" .S004 12
#guard stFails "input i[0]: T;" .S004 8
#guard stFails "output o: T as k;" .S004 13
#guard stFails "instance u = M() with { clock = d };" .S004 18
#guard stFails "instance u = p::M();" .S004 15
#guard stFails "a[0] = 1;" .S004 1
#guard stFails "a.b[0] := 1;" .S004 1
#guard stFails "a.0 = 1;" .S004 1
#guard stFails "a[b.0] = 1;" .S004 1
#guard stFails "@field(x, \"f\") = 1;" .S004 1
#guard ex "(a, b)" == "error S004 1:14"
#guard ex "(a.0, b)" == "error S004 1:14"
#guard ex "(f(a, b))" == "(call (name \"f\") ((name \"a\") (name \"b\")))"
#guard ex "()" == "error S004 1:14"
#guard ex "[a, b]" == "error S004 1:14"
#guard ex "[T; 4]" == "error S004 1:14"
#guard ex "x.0" == "error S004 1:16"
#guard ex "x.f(1)" == "error S004 1:17"
#guard ex "a::b" == "error S004 1:15"
#guard ex "@TypeOf(x)" == "error S004 1:14"
#guard ex "fn (T) -> T" == "error S004 1:14"

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
#guard ex "(a, $)" == "error S004 1:14"

/-! The nesting limit: height 64 passes, and height 65 fails at the first token of its form. -/
def parens (n : Nat) : String := "".pushn '(' n ++ "x" ++ "".pushn ')' n
def negs (n : Nat) : String := "".pushn '-' n ++ "x"
def chain (n : Nat) : String := " + ".intercalate (List.replicate n "a")
def calls (n : Nat) : String := String.join (List.replicate n "f(") ++ "x" ++ "".pushn ')' n

#guard (constValue (parens 63)).toBool
#guard ex (parens 64) == "error S001 1:14"
#guard ex ("y + " ++ parens 64) == "error S001 1:18"
#guard (constValue (negs 63)).toBool
#guard ex (negs 64) == "error S001 1:14"
#guard (constValue (chain 64)).toBool
#guard ex (chain 65) == "error S001 1:14"
#guard (constValue (calls 63)).toBool
#guard ex (calls 64) == "error S001 1:14"
#guard ex ("g(" ++ chain 65 ++ ")") == "error S001 1:16"
#guard fails ("const N: T[" ++ chain 65 ++ "] = 1;") .S001 1 12
#guard ex (parens 1000) == "error S001 1:950"

/-! Statements have no nesting limit. -/
#guard !((st ("".pushn '{' 200 ++ "".pushn '}' 200)).startsWith "error")

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

end Silicon.Source.Test.Parse
