import Silicon.Source.Parse
import Silicon.Source.Resolve
import Silicon.Source.Check

/-!
These tests check the generic pre-check at its public boundary. They check the code and the
position of each `S005`, `S006`, and `S007` rule, an item that no instantiation uses, and the
pass order.
-/

namespace Silicon.Source.Test.Check

open Silicon.Source
open Silicon.Source.Lex (defaultSyntaxDepth)

def run (s : String) : Except Error (Array Resolve.Item) := do
  let items ← Parse.parseSource defaultSyntaxDepth s
  Check.check (← Resolve.resolve items)

def ok (s : String) : Bool := (run s).toBool

def fails (s : String) (code : ErrorCode) (line col : Nat) : Bool :=
  match run s with
  | .error e => e.code == code && e.pos == ⟨line, col⟩
  | .ok _ => false

def message (s : String) : String :=
  match run s with
  | .error e => e.msg
  | .ok _ => ""

/-! The body `s` of a function. The body starts on line 2. -/
def fnBody (s : String) : String := "fn f(p: Bool) -> Bool {\n" ++ s ++ "\n}"

/-! The body `s` of a module. The body starts on line 2. -/
def modBody (s : String) : String := "module M(comptime W: Nat) {\n" ++ s ++ "\n}"

/-! A file without an error passes, and the check gives the resolved AST. -/
#guard ok ""
#guard ok ("module Counter(comptime W: Nat) {\ninput enable: Bool;\noutput value: UInt[W];\n" ++
  "output full: Bool;\nreg count: UInt[W] = 0;\n" ++
  "count := if (enable) { count +% 1 } else { count };\nvalue := count;\n" ++
  "full := count == UInt[W]((1 << W) - 1);\n}\n" ++
  "module Main() {\ninput enable: Bool;\noutput value: UInt[4];\n" ++
  "instance counter = Counter(4);\ncounter.enable := enable;\nvalue := counter.value;\n}")
#guard ok "comptime fn g(n: Nat) -> Nat {\ncomptime if (n == 0) { return 1; }\nreturn g(n - 1);\n}"
#guard (run "const A: Nat = 1;\nfn f() -> Nat { return A; }").toOption.map (·.size) == some 2

/-! A hardware value outside a static position passes. -/
#guard ok (modBody ("input a: UInt[W];\noutput b: UInt[W];\nreg r: UInt[W] = 0;\n" ++
  "r := a +% r;\nb := resize(UInt[W], r);\nlet x = reinterpret(SInt[W], a);"))
#guard ok ("fn g(comptime N: Nat, x: Bool) -> Bool { return x; }\n" ++
  "module M() {\ninput a: Bool;\nlet y = g(1, a);\n}")
#guard ok (modBody "input a: Bool;\nlet y = if (a) { 1 } else { 2 };")

/-! The dynamic stage rule is for `Elab`: an alias and a domain name pass this check. -/
#guard ok (modBody "input a: Bool;\nlet x = a;\ncomptime if (x) {}")
#guard ok "module M() {\ncomptime if (clock) {}\n}"

/-! `S005`: a static position names a resource. The position is the name. -/
#guard fails (modBody "reg r: UInt[W] = 0;\ncomptime if (r == 0) {}") .S005 3 14
#guard message (modBody "reg r: UInt[W] = 0;\ncomptime if (r == 0) {}") ==
  "`r` is a register; a static position needs a static value"
#guard fails "module A(comptime N: Nat) {\ninput a: UInt[8];\ninstance u = A(a);\n}" .S005 3 16
#guard fails (modBody "wire w: Bool;\nlet x: UInt[w] = 0;") .S005 3 13
#guard fails (modBody "input a: Bool;\nreg r: Bool = a;") .S005 3 15
#guard fails (modBody "wire w: Bool;\ncomptime for i in 0..w {}") .S005 3 22
#guard fails (modBody "reg r: Bool = false;\nlet x = r(1);") .S005 3 9
#guard fails ("fn g(comptime N: Nat, x: Bool) -> Bool { return x; }\n" ++
  "module M() {\ninput a: Bool;\nlet y = g(a, a);\n}") .S005 4 11
#guard fails ("comptime fn g(x: Nat) -> Nat { return x; }\n" ++
  "module M() {\ninput a: Bool;\nlet y = g(a);\n}") .S005 4 11
#guard fails (modBody "input a: UInt[W];\nlet y = resize(a, a);") .S005 3 16
#guard fails (modBody "input a: Bool;\nstatic_assert(a, \"m\");") .S005 3 15
#guard fails (modBody "input a: UInt[W];\nlet y = UInt[W](a);") .S005 3 17
#guard fails (modBody "output b: Bool;\nlet y = Bool(b);") .S005 3 14
#guard fails (modBody "instance u = M(1);\ncomptime if (u.x == 1) {}") .S005 3 14
#guard message (modBody "instance u = M(1);\ncomptime if (u.x == 1) {}") ==
  "`u` is an instance; a static position needs a static value"

/-! `S005`: each part of a static expression is static, also an arm that is not selected. -/
#guard fails (modBody "input a: UInt[W];\nlet y = UInt[W](if (true) { 1 } else { a });")
  .S005 3 40
#guard fails (modBody "input a: UInt[W];\nlet y = UInt[W](resize(UInt[W], a));") .S005 3 33

/-! `S006`: a module body has no `return`, also in a nested block. -/
#guard fails (modBody "return;") .S006 2 1
#guard fails (modBody "comptime if (true) {\n{ return; }\n}") .S006 3 3
#guard message (modBody "return;") == "a module body has no `return`"
#guard ok (fnBody "comptime if (p) { return p; }\nreturn p;")

/-! `S006`: a `comptime fn` declares no port, resource, or instance, and has no `:=`. -/
#guard fails "comptime fn g() -> Nat {\nreg r: Bool = false;\nreturn 1;\n}" .S006 2 1
#guard fails "comptime fn g() -> Nat {\nwire w: Bool;\nreturn 1;\n}" .S006 2 1
#guard fails "comptime fn g() -> Nat {\ninput a: Bool;\nreturn 1;\n}" .S006 2 1
#guard fails "comptime fn g() -> Nat {\noutput a: Bool;\nreturn 1;\n}" .S006 2 1
#guard fails "module A() {}\ncomptime fn g() -> Nat {\n{ instance u = A(); }\nreturn 1;\n}"
  .S006 3 3
#guard fails "comptime fn g(x: Nat) -> Nat {\nx := 1;\nreturn x;\n}" .S006 2 1
#guard message "comptime fn g(x: Nat) -> Nat {\nx := 1;\nreturn x;\n}" ==
  "a `comptime fn` has no `:=`"
#guard ok "comptime fn g(x: Nat) -> Nat {\nlet mut y = x;\ny = 1;\nreturn y;\n}"

/-! `S007`: a call has the number of arguments of its declaration. The position is the call. -/
#guard fails "fn g(x: Nat) -> Nat { return x; }\nconst N: Nat = g(1, 2);" .S007 2 16
#guard fails "fn g(x: Nat) -> Nat { return x; }\nconst N: Nat = g();" .S007 2 16
#guard message "fn g(x: Nat) -> Nat { return x; }\nconst N: Nat = g();" ==
  "`g` takes 1 argument(s), but it has 0"
#guard fails (fnBody "return resize(UInt[8]);") .S007 2 8
#guard fails (fnBody "return reinterpret(UInt[8], p, p);") .S007 2 8
#guard fails (fnBody "static_assert(p);\nreturn p;") .S007 2 1
#guard fails (fnBody "error();\nreturn p;") .S007 2 1
#guard fails (fnBody "error(\"a\", \"b\");\nreturn p;") .S007 2 1

/-! `S007`: a call through a local or a `const` has no known arity here. -/
#guard ok (fnBody "let g = p;\nreturn g(1, 2);")
#guard ok "const N: Nat = 1;\nconst M: Nat = N(1, 2);"

/-! `S007`: a constructor `T(n)` has one argument. -/
#guard fails (fnBody "return Bool(true, false);") .S007 2 8
#guard fails (fnBody "return UInt[8]();") .S007 2 8
#guard ok (fnBody "return Bool(true);")

/-! `S007`: an `instance` has one argument for each parameter. The position is the statement. -/
#guard fails "module A(comptime N: Nat) {}\nmodule B() {\ninstance u = A();\n}" .S007 3 1
#guard fails "module A(comptime N: Nat) {}\nmodule B() {\ninstance u = A(1, 2);\n}" .S007 3 1
#guard ok ("module A(comptime N: Nat, comptime B: Bool) {}\n" ++
  "module B() {\ninstance u = A(1, true);\n}")

/-! `S007`: a type family has its index arguments, in a type and in an expression. -/
#guard fails "const A: UInt = 0;" .S007 1 10
#guard fails "const A: SInt[1, 2] = 0;" .S007 1 10
#guard fails "const A: Bool[1] = true;" .S007 1 10
#guard fails "const A: UInt[8][2] = 0;" .S007 1 10
#guard message "const A: UInt[8][2] = 0;" == "a complete type takes 0 argument(s), but it has 1"
#guard fails "fn g(x: Nat) -> UInt { return 0; }" .S007 1 17
#guard fails (fnBody "return resize(SInt, p);") .S007 2 15
#guard fails (fnBody "return UInt(3);") .S007 2 8
#guard fails (fnBody "return resize(Nat[1], p);") .S007 2 15
#guard fails (fnBody "return resize(UInt[8][1], p);") .S007 2 15
#guard ok (fnBody "let x: Nat = 1;\nreturn resize(Bool, p);")

/-! The check runs on each item, also on an item that no instantiation uses. -/
#guard fails "module Top() {}\nmodule Unused() {\nreturn;\n}" .S006 3 1
#guard fails "module Top() {}\ncomptime fn unused() -> Nat {\nwire w: Bool;\nreturn 1;\n}"
  .S006 3 1
#guard fails "fn unused(x: Nat) -> Nat { return unused(); }" .S007 1 35

/-! The check runs on both branches of a `comptime if`. -/
#guard fails (modBody "comptime if (true) {} else {\nreturn;\n}") .S006 3 1
#guard fails (modBody "comptime if (false) {\nlet x = resize(1);\n}") .S007 3 9

/-! Pass 2 and pass 3 come first: an `S002` or an `S003` wins over an earlier `S005`. -/
#guard fails "module M() {\ninput a: Bool;\ncomptime if (a) {}\nlet x = q;\n}" .S003 4 9
#guard fails "module M() {\ninput a: Bool;\ncomptime if (a) {}\nlet x = 1;\nlet x = 2;\n}"
  .S002 5 5
#guard fails "module M() {\nreturn;\nlet x = resize(q);\n}" .S003 3 16

/-! `S005` to `S007` compete by position. -/
#guard fails (modBody "return;\ninput a: Bool;\ncomptime if (a) {}") .S006 2 1
#guard fails (modBody "input a: Bool;\ncomptime if (a) {}\nreturn;") .S005 3 14
#guard fails (modBody "let x = resize(1);\nreturn;") .S007 2 9
#guard fails (modBody "input a: Bool;\nlet x = resize(1, 2, 3) + UInt[W](a);") .S007 3 9
#guard fails (modBody "input a: Bool;\nlet x = UInt[W](a) + resize(1, 2, 3);") .S005 3 17
#guard fails ("comptime fn g() -> Nat {\nreturn 1;\n}\nmodule M() {\nreturn;\n}\n" ++
  "fn h() -> Nat { return g(1); }") .S006 5 1

/-!
The walk is linear and its stack follows the syntax depth. These inputs are at the default
syntax depth or hold many statements in one scope.
-/
def regs (n : Nat) : String :=
  String.join ((List.range n).map fun i => s!"reg r{i}: UInt[W] = 0;\nr{i} := r{i};\n")
def blocks (n : Nat) : String :=
  "".pushn '{' n ++ "comptime if (W > 0) {}" ++ "".pushn '}' n
def chain (n : Nat) : String := " + ".intercalate (List.replicate n "W")

#guard ok (modBody (regs 10000))
#guard fails (modBody (regs 10000 ++ "comptime if (r9999 == 0) {}")) .S005 20002 14
#guard ok (modBody (blocks 4094))
#guard ok (modBody ("comptime if (" ++ chain 4095 ++ " > 0) {}"))
#guard ok (modBody (String.join (List.replicate 20000 "{ let a = W; }\n")))

end Silicon.Source.Test.Check
