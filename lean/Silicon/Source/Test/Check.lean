-- SPDX-License-Identifier: Apache-2.0
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
#guard (run "const A: Nat = 1;\nfn f() -> Nat { return A; }").toOption.map (·.size) ==
  some (2 + Resolve.preludeCount)

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

/-!
`S005`: a static position names a memory: an index, the length of `[T; N]`, the condition of a
`comptime if`, an `instance` argument, and the depth of a `mem`. The position is the name.
-/
#guard ok (modBody "mem m: [UInt[W]; W + 1];
let x = m;")
#guard fails (modBody "mem m: [Bool; 4];
let x: [Bool; m] = 0;") .S005 3 15
#guard fails (modBody "mem m: [Bool; 4];
let x = [Bool; m]();") .S005 3 16
#guard fails (modBody "mem m: [Bool; 4];
let x: UInt[m] = 0;") .S005 3 13
#guard fails (modBody "mem m: [Bool; 4];
comptime if (m) {}") .S005 3 14
#guard fails (modBody "mem m: [Bool; 4];
instance u = M(m);") .S005 3 16
#guard fails (modBody "wire w: UInt[8];
mem m: [Bool; w];") .S005 3 15
#guard fails (modBody "mem m: [Bool; 4];
mem k: [UInt[m]; 4];") .S005 3 14
#guard message (modBody "mem m: [Bool; 4];
comptime if (m) {}") ==
  "`m` is a memory; a static position needs a static value"

/-! `S006`: a `comptime fn` has no `mem`, also in a nested block. -/
#guard fails "comptime fn g() -> Nat {
mem m: [Bool; 4];
return 1;
}" .S006 2 1
#guard fails "comptime fn g() -> Nat {
{ mem m: [Bool; 4]; }
return 1;
}" .S006 2 3
#guard message "comptime fn g() -> Nat {
mem m: [Bool; 4];
return 1;
}" ==
  "a `comptime fn` has no memory"
#guard fails "comptime fn g() -> Nat {
mem m: [Bool; 4];
comptime if (m) {}
return 1;
}"
  .S006 2 1

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
#guard fails (fnBody "diagnostic(\"a\");\nreturn p;") .S007 2 1
#guard fails (fnBody "diagnostic(\"a\", 1, 2);\nreturn p;") .S007 2 1
#guard message (fnBody "diagnostic(\"a\");\nreturn p;") ==
  "`diagnostic` takes 2 argument(s), but it has 1"
#guard ok (fnBody "diagnostic(\"a\", p);\nreturn p;")

/-! `S007`: a call through a local or a `const` has no known arity here. -/
#guard ok (fnBody "let g = p;\nreturn g(1, 2);")
#guard ok "const N: Nat = 1;\nconst M: Nat = N(1, 2);"

/-! `S007`: a constructor `T(n)` has one argument, and the zero `T()` has none. -/
#guard fails (fnBody "return Bool(true, false);") .S007 2 8
#guard message (fnBody "return Bool(true, false);") ==
  "a constructor takes 0 or 1 argument(s), but it has 2"
#guard ok (fnBody "return UInt[8]();")
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
#guard message "const A: UInt = 0;" == "`UInt` takes 1 argument(s), but it has 0; write `UInt[W]`"
#guard message "const A: SInt[1, 2] = 0;" ==
  "`SInt` takes 1 argument(s), but it has 2; write `SInt[W]`"
#guard message "const A: List = 0;" == "`List` takes 1 argument(s), but it has 0; write `List[T]`"
#guard message "const A: Bool[1] = true;" == "`Bool` takes 0 argument(s), but it has 1"

/-!
`S007`: the handle type families of slice 3 (section 5.6). `Reg`, `Wire`, and `Input` take one
argument, and `Mem` takes two. `Instance` takes its module and one argument for each parameter
of the module. A bare family is `S007` at its name, in a type and in an expression. The text ends
with the signature of the family.
-/
def counter : String := "module C(comptime W: Nat, comptime B: Bool) {}\n"
#guard ok (modBody ("type T = (Reg[UInt[W]], Wire[Bool], Input[UInt[8]]);\n" ++
  "let m = Mem[UInt[8], 16];"))
#guard ok (counter ++ "const T: Type = Instance[C, 8, true];\n" ++
  "fn f(x: Instance[C, 8, true]) -> Bool { return true; }")
#guard ok "module D() {}\nconst T: Type = Instance[D];"
#guard fails "const A: Reg = 0;" .S007 1 10
#guard message "const A: Reg = 0;" == "`Reg` takes 1 argument(s), but it has 0; write `Reg[T]`"
#guard fails (fnBody "let t = Wire[Bool, Bool];\nreturn p;") .S007 2 9
#guard message (fnBody "let t = Wire[Bool, Bool];\nreturn p;") ==
  "`Wire` takes 1 argument(s), but it has 2; write `Wire[T]`"
#guard message "const A: Input = 0;" ==
  "`Input` takes 1 argument(s), but it has 0; write `Input[T]`"
#guard fails "const A: Mem[UInt[8]] = 0;" .S007 1 10
#guard message "const A: Mem[UInt[8]] = 0;" ==
  "`Mem` takes 2 argument(s), but it has 1; write `Mem[T, N]`"
#guard fails "const A: Instance = 0;" .S007 1 10
#guard message "const A: Instance = 0;" ==
  "`Instance` takes 1 argument(s), but it has 0; write `Instance[M, args]`"
#guard fails (fnBody "let t = Instance;\nreturn p;") .S007 2 9
#guard fails (counter ++ "const T: Type = Instance[C, 8];") .S007 2 17
#guard message (counter ++ "const T: Type = Instance[C, 8];") ==
  "`Instance` takes 3 argument(s), but it has 2; write `Instance[M, args]`"
#guard message (counter ++ "fn f(x: Instance[C, 8, true, 1]) -> Bool { return true; }") ==
  "`Instance` takes 3 argument(s), but it has 4; write `Instance[M, args]`"
#guard fails "module D() {}\nconst T: Type = Instance[D, 1];" .S007 2 17

/-!
`S005`: each argument of a handle type is a static position, in a type and in an expression.
-/
#guard fails (modBody "reg r: UInt[W] = 0;\nlet t = Reg[r];") .S005 3 13
#guard message (modBody "reg r: UInt[W] = 0;\nlet t = Reg[r];") ==
  "`r` is a register; a static position needs a static value"
#guard fails (modBody "wire w: Bool;\nlet t = Mem[UInt[8], w];") .S005 3 22
#guard fails (counter ++ "module M() {\ninput a: UInt[8];\nlet t: Instance[C, a, true] = 0;\n}")
  .S005 4 20
#guard ok (modBody "reg r: UInt[W] = 0;\nlet t = Reg[UInt[W]];\nlet x: UInt[W] = r;")

/-!
`S007`: `read` has one argument (section 5.6), also in the receiver form. A user function `read`
shadows it.
-/
#guard ok (modBody "reg r: UInt[W] = 0;\nlet x = read(r);\nlet y = r.read();")
#guard fails (fnBody "return read();") .S007 2 8
#guard message (fnBody "return read(p, p);") ==
  "`read` takes 1 argument(s), but it has 2; write `read(h)` with one register or wire"
#guard message (fnBody "return p.read(p);") ==
  "`read` takes 1 argument(s), but it has 2; write `read(h)` with one register or wire"
#guard message (fnBody "return read();") ==
  "`read` takes 1 argument(s), but it has 0; write `read(h)` with one register or wire"
#guard fails (fnBody "return p.read(p);") .S007 2 8
#guard ok ("fn read(a: Bool, b: Bool) -> Bool { return a; }\n" ++ fnBody "return read(p, p);")
#guard message ("fn read(a: Bool) -> Bool { return a; }\n" ++ fnBody "return read(p, p);") ==
  "`read` takes 1 argument(s), but it has 2"

/-! `S007`: `len` has one argument. The position is the call. -/
#guard fails (fnBody "return len();") .S007 2 8
#guard fails (fnBody "return len([p], [p]);") .S007 2 8
#guard message (fnBody "return len([p], [p]);") == "`len` takes 1 argument(s), but it has 2"
#guard ok (fnBody "let n = len([p, p]);\nreturn p;")

/-! `S007`: `Unit`, `()`, a tuple type, and an array type take no index. -/
#guard fails "const A: Unit[1] = ();" .S007 1 10
#guard fails (fnBody "return Unit[1];") .S007 2 8
#guard fails "const A: [Bool; 2][1] = [true, true];" .S007 1 10
#guard fails "const A: (Bool,)[0] = (true,);" .S007 1 10
#guard message "const A: (Bool,)[0] = (true,);" ==
  "a complete type takes 0 argument(s), but it has 1"
#guard ok "const A: Unit = ();\nconst B: ((), [Unit; 0]) = ((), []);"

/-! `S007`: a part of a container type or a container expression has its index arguments. -/
#guard fails "const A: (UInt, Bool) = (0, true);" .S007 1 11
#guard fails "const A: [UInt; 2] = [0, 0];" .S007 1 11
#guard fails "const A: [[Bool; 1][1]; 2] = [];" .S007 1 11
#guard fails (fnBody "return (p, SInt);") .S007 2 12
#guard fails (fnBody "return [resize(p)].0;") .S007 2 9

/-! The struct `P` with one parameter and two fields, and the struct `S` without parameters. -/
def structs : String :=
  "\nstruct P(comptime W: Nat) { a: UInt[W], b: Bool }\nstruct S { a: Bool }\nstruct E {}"

/-!
A struct specialization, a struct constructor, the zero `T()`, a `type` item, `Type`, and
`data_bits` pass this check.
-/
#guard ok ("const A: P[8] = P[8](1, true);\nconst B: S = S(true);\nconst C: P[2] = P[2]();" ++
  "\nconst D: E = E();\nconst N: Nat = data_bits(P[8]);" ++ structs)
#guard ok "type A = UInt[8];\nconst B: A = A(3);\nconst C: Type = A;\nconst D: A = A();"
#guard ok (fnBody "type T = (Bool, [UInt[8]; 2]);\nlet x: T = T();\nreturn p;")
#guard ok "fn f(comptime T: Type, x: T) -> T { return T(x); }"

/-!
`S007`: a struct specialization has one argument for each parameter, in a type and in an
expression.
-/
#guard fails ("const A: P[8, 9] = 0;" ++ structs) .S007 1 10
#guard fails ("const A: S[1] = 0;" ++ structs) .S007 1 10
#guard message ("const A: S[1] = 0;" ++ structs) ==
  "`S` takes 0 argument(s), but it has 1; pass one argument for each `comptime` parameter of `S`"
#guard fails ("const A: P[8][1] = 0;" ++ structs) .S007 1 10
#guard fails (fnBody "let t = P[1, 2];\nreturn p;" ++ structs) .S007 2 9
#guard fails (fnBody "let t = E[0];\nreturn p;" ++ structs) .S007 2 9

/-!
`S007`: a struct with parameters is not used without its arguments: as a type, as a value, and
as the callee of a constructor. The position is the name.
-/
#guard fails ("const A: P = 0;" ++ structs) .S007 1 10
#guard message ("const A: P = 0;" ++ structs) ==
  "`P` takes 1 argument(s), but it has 0; pass one argument for each `comptime` parameter of `P`"
#guard fails (fnBody "let t = P;\nreturn p;" ++ structs) .S007 2 9
#guard fails (fnBody "let t = P(1, true);\nreturn p;" ++ structs) .S007 2 9
#guard fails (fnBody "let t = P();\nreturn p;" ++ structs) .S007 2 9
#guard fails ("struct Q(comptime W: Nat) { a: Q }") .S007 1 32

/-!
`S007`: a struct constructor has one argument for each field, or none for the zero. The position
is the call.
-/
#guard fails (fnBody "let t = S(true, false);\nreturn p;" ++ structs) .S007 2 9
#guard fails (fnBody "let t = P[8](1);\nreturn p;" ++ structs) .S007 2 9
#guard message (fnBody "let t = P[8](1);\nreturn p;" ++ structs) ==
  "a struct constructor takes 0 or 2 argument(s), but it has 1; pass one value for each " ++
    "field, or none for the zero"
#guard fails (fnBody "let t = E(1);\nreturn p;" ++ structs) .S007 2 9

/-!
`S007`: `Type` and a `type` item are complete types, so they take no index. `Elab` checks the
constructor of a `type` item, because only `Elab` knows its type. `data_bits` has one argument.
-/
#guard fails "const A: Type[1] = Bool;" .S007 1 10
#guard fails "type A = UInt[8];\nconst B: A[2] = 0;" .S007 2 10
#guard fails "type A = UInt[8];\nconst B: Nat = A[2];" .S007 2 16
#guard ok "type A = UInt[8];\nconst B: Nat = A(1, 2);"
#guard fails (fnBody "return data_bits();") .S007 2 8
#guard fails (fnBody "return data_bits(Bool, Bool);") .S007 2 8

/-!
`S007` in the parts of the type forms: a parameter type, a field type, a `type` item, a `type`
statement, and an array type in an expression.
-/
#guard fails "struct Q(comptime W: UInt) { a: Bool }" .S007 1 22
#guard fails "struct Q { a: UInt }" .S007 1 15
#guard fails "type A = SInt;" .S007 1 10
#guard fails (fnBody "type T = UInt;\nreturn p;") .S007 2 10
#guard fails (fnBody "let t = [UInt; 2];\nreturn p;") .S007 2 10
#guard fails (fnBody "let t = [Bool; 2][1];\nreturn p;") .S007 2 9
#guard fails (fnBody "let t = [Bool; 2](true, false);\nreturn p;") .S007 2 9
#guard ok (fnBody "let t = [Bool; 2]();\nlet u = [Bool; 2]([p, p]);\nreturn p;")

/-!
`S005`: each argument of a struct specialization and the length of an array type in an
expression are static positions. The arguments of a struct constructor are not.
-/
#guard fails (modBody "input a: Nat;\nlet x: P[a] = 0;" ++ structs) .S005 3 10
#guard fails (modBody "input a: Nat;\nlet t = P[a];" ++ structs) .S005 3 11
#guard fails (modBody "wire w: Nat;\nlet t = [Bool; w];") .S005 3 16
#guard fails (modBody "wire w: Nat;\ntype T = [Bool; w];") .S005 3 17
#guard fails (modBody "input a: Bool;\nlet t = Bool(a);") .S005 3 14
#guard ok (modBody "input a: Bool;\nlet t = S(a);\nlet u = P[W](0, a);" ++ structs)

/-!
`S005`: a part of a container in a static position, the length of an array type, and the index
of a container are static positions.
-/
#guard fails (modBody "reg r: UInt[W] = 0;\ncomptime if ((r, 1).0 == 0) {}") .S005 3 15
#guard fails (modBody "reg r: UInt[W] = 0;\ncomptime if ([r][0] == 0) {}") .S005 3 15
#guard fails (modBody "wire w: Nat;\nlet x: [Bool; w] = [];") .S005 3 15
#guard fails (modBody "input a: UInt[W];\nlet y = [1, 2][a];") .S005 3 16
#guard fails (modBody "input a: UInt[W];\nlet y = (1, 2)[a];") .S005 3 16

/-!
A hardware element and a hardware argument of `len` pass this check. The rules of the
containers that need static values are for `Elab`: an index with two arguments, `<` on
containers, and `==` on containers without a common type.
-/
#guard ok (modBody "input a: Bool;\nlet t = (a, ());\nlet n = len([a, a]);\nlet x = t.0;")
#guard ok (fnBody "let t = (1, 2);\nlet x = t[0, 1];\nlet y = t < t;\nreturn [1] == [1, 2];")

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

/-!
The helpers of the tests of receiver calls and `mut` actuals. The body `s` of `f` starts on line
6. `xs` is a `let mut` local, `ys` a `mut` formal, and `zs` a formal without a mark.
-/
def lists (s : String) : String :=
  "fn helper(comptime n: Int, mut xs: List[Int]) -> () {}\n" ++
  "fn two(mut a: List[Int], mut b: List[Int]) -> () {}\n" ++
  "fn pair(a: Int, b: Int) -> Int { return a; }\n" ++
  "fn f(zs: List[Int], mut ys: List[Int]) -> () {\n" ++
  "let mut xs = list(Int);\n" ++ s ++ "\n}"

/-! A receiver call binds its receiver to the first parameter without `comptime`. -/
#guard ok (lists "xs.push(1);\nlet n = xs.pop() + xs.len();\nlet s = n.str();")
#guard ok (lists "xs.helper(1);\nys.helper(2);\nxs.two(ys);")
#guard ok (lists "let a = 1.resize(UInt[8]);\nlet b = a.reinterpret(SInt[8]);")
#guard ok (lists "let c = (1 == 1).static_assert(\"m\");\n\"m\".error();")
#guard ok "comptime fn h(x: Nat, comptime y: Nat) -> Nat { return x; }\nconst A: Nat = 1.h(2);"
#guard ok (lists "let t = Int.data_bits();")

/-! `S007` at the start of a receiver call: no parameter without `comptime`, or the arity. -/
#guard fails (lists "let t = Int.list();") .S007 6 9
#guard message (lists "let t = Int.list();") ==
  "`list` has no parameter without `comptime` for the receiver"
#guard fails ("fn c(comptime n: Nat) -> Nat { return n; }\n" ++
  "fn g(k: Nat) -> Nat { return k.c(); }") .S007 2 30
#guard fails (lists "xs.push();") .S007 6 1
#guard message (lists "xs.push();") == "`push` takes 2 argument(s), but it has 1"
#guard fails (lists "let a = xs.pop(1);") .S007 6 9
#guard fails (lists "let a = xs.len(1);") .S007 6 9
#guard fails (lists "xs.helper();") .S007 6 1
#guard fails (lists "xs.helper(1, 2);") .S007 6 1
#guard fails (lists "let a = 1.pair(2, 3);") .S007 6 9
#guard fails (lists "push(xs);") .S007 6 1
#guard fails (lists "let a = str(1, 2);") .S007 6 9
#guard fails (lists "let t = list();") .S007 6 9
#guard fails "const L: List = 1;" .S007 1 10
#guard fails "const S: String[1] = 1;" .S007 1 10

/-!
A `comptime` parameter is a static position, also for an argument of a receiver call. The
receiver binds to a parameter without `comptime`. Each parameter of a `comptime fn` is static,
also the one of the receiver. The `T` of `list(T)` is static. The argument of `str` is not.
-/
def regs2 (s : String) : String :=
  "fn g(comptime n: Nat, x: Bool) -> Bool { return x; }\n" ++
  "comptime fn h(x: Nat) -> Nat { return x; }\n" ++
  "module M() {\ninput a: Bool;\nreg r: UInt[4] = 0;\n" ++ s ++ "\n}"
#guard ok (regs2 "let y = a.g(1);\nlet z = str(r);\nlet w = r.resize(UInt[8]);")
#guard fails (regs2 "let y = a.g(r);") .S005 6 13
#guard fails (regs2 "let y = a.h();") .S005 6 9
#guard fails (regs2 "let y = a.resize(r);") .S005 6 18
#guard fails (regs2 "let l = list(r);") .S005 6 14

/-!
`S008`: a `mut` actual is a place with a mutable root, a `let mut` local or a `mut` formal. The
position is the start of the actual.
-/
#guard ok (lists "push(xs, 1);\npush(ys, 2);\nlet mut t = (list(Int), 1);\nt.0.push(1);")
#guard ok (lists "let mut a = [list(Int)];\na[0].push(1);\nhelper(1, a[0]);")
#guard fails (lists "zs.push(1);") .S008 6 1
#guard message (lists "zs.push(1);") ==
  "a `mut` actual has a `let mut` local or a `mut` formal as its root"
#guard fails (lists "push(zs, 1);") .S008 6 6
#guard fails (lists "let l = list(Int);\nl.push(1);") .S008 7 1
#guard fails (lists "list(Int).push(1);") .S008 6 1
#guard message (lists "list(Int).push(1);") == "a `mut` actual is a place"
#guard fails (lists "helper(1, list(Int));") .S008 6 11
#guard fails ("const L: List[Int] = list(Int);\n" ++ lists "L.push(1);") .S008 7 1
#guard fails (lists "let a = (xs.pop() + 1).str();\npush(xs.len(), 1);") .S008 7 6

/-!
`S008`: no mutation of a pending root in its window. The window of a `mut` actual holds its own
indices and each later argument. The receiver comes first. The window of an assignment holds the
indices of its place and its value. The position is the second `mut` actual with the root.
-/
#guard fails (lists "xs.helper(xs.pop());") .S008 6 11
#guard message (lists "xs.helper(xs.pop());") ==
  "the root of this `mut` actual is pending in its window"
#guard fails (lists "xs[0] = xs.pop();") .S008 6 9
#guard fails (lists "xs.push(xs.pop());") .S008 6 9
#guard fails (lists "push(xs, xs.pop());") .S008 6 10
#guard fails (lists "xs.push(pair(1, xs.pop()));") .S008 6 17
#guard fails (lists "two(xs, xs);") .S008 6 9
#guard fails (lists "xs.two(xs);") .S008 6 8
#guard fails (lists "ys.two(ys);") .S008 6 8
#guard fails (lists "xs[xs.pop()] = 1;") .S008 6 4
#guard fails (lists "let mut a = [list(Int)];\na[a[0].pop()].push(1);") .S008 7 3
#guard fails (lists "let mut t = (list(Int), 1);\nt.0.push(t.0.pop());") .S008 7 10

/-!
A root is pending only in its window. An argument before the `mut` actual and a call that ends
before it do not conflict. A read of a pending root is not a mutation.
-/
#guard ok (lists "helper(xs.pop(), xs);")
#guard ok (lists "let a = pair(xs.pop(), xs.pop());")
#guard ok (lists "xs.push(xs.len());")
#guard ok (lists "xs[0] = xs.len();")
#guard ok (lists "xs.push(ys.pop());\nys.push(xs.pop());")
#guard ok (lists "xs.two(ys);\nys.two(xs);")
#guard ok (lists "push(xs, 1);\npush(xs, 2);")
#guard ok (lists "let mut a = [list(Int)];\na[a.len()].push(1);")
#guard ok (lists "let h = push;\nh(zs, 1);")

/-!
`S007`: a function type takes no index, in a type and in an expression. The position is the
index, the start of its base. A postfix after a function type belongs to its result type.
-/
#guard fails (fnBody "let h = (fn () -> UInt)[8];\nreturn p;") .S007 2 9
#guard message (fnBody "let h = (fn () -> UInt)[8];\nreturn p;") ==
  "a function type takes 0 argument(s), but it has 1"
#guard fails "const A: (fn () -> UInt)[8] = 1;" .S007 1 10
#guard fails (fnBody "let h = (fn () -> Bool)[1][2];\nreturn p;") .S007 2 9
#guard ok (fnBody "let h = fn () -> UInt[8];\nreturn p;")
#guard ok "const A: fn () -> UInt[8] = 1;"

/-! The parameter types and the result type of a function type follow the rules of a type. -/
#guard fails "const A: fn (UInt) -> Bool = 1;" .S007 1 14
#guard fails "const A: fn () -> UInt = 1;" .S007 1 19
#guard fails (fnBody "let h = fn (Bool, UInt) -> Bool;\nreturn p;") .S007 2 19
#guard fails (fnBody "let h = fn () -> UInt;\nreturn p;") .S007 2 18
#guard fails (modBody "reg r: UInt[8] = 0;\nlet h = fn (UInt[r]) -> Bool;") .S005 3 18
#guard fails (modBody "reg r: UInt[8] = 0;\nlet h: fn () -> UInt[r] = 1;") .S005 3 22
#guard fails (modBody "reg r: UInt[8] = 0;\ncomptime if (fn () -> UInt[r] == r) {}") .S005 3 28

/-!
Pass 5 decides the other rules of the function types and the function values. These are a call
through a function value (`S007` and `S008`) and the constructor of a function type. They are
also a generic function or a builtin as a value, a unary operator on a type, and `==` on
functions (`S010`).
-/
#guard ok "fn g(mut x: Bool) -> Bool { return x; }\nfn f() -> Bool { let h = g; return h(true); }"
#guard ok (fnBody "let h = f;\nreturn h(1, 2, 3);")
#guard ok (fnBody "let h = (fn () -> Bool)(1, 2, 3);\nreturn p;")
#guard ok "fn f() -> Nat { let h = g; return 1; }\nfn g(comptime N: Nat) -> Nat { return N; }"
#guard ok (fnBody "let h = len;\nreturn p;")
#guard ok (fnBody "let h = -fn () -> Bool;\nreturn p;")
#guard ok (fnBody "let h = f == f;\nreturn p;")
#guard ok (fnBody "return p == (fn () -> Bool == f);")

/-! `S005` to `S007` compete by position. -/
#guard fails (modBody "return;\ninput a: Bool;\ncomptime if (a) {}") .S006 2 1
#guard fails (modBody "input a: Bool;\ncomptime if (a) {}\nreturn;") .S005 3 14
#guard fails (modBody "let x = resize(1);\nreturn;") .S007 2 9
#guard fails (modBody "input a: Bool;\nlet x = resize(1, 2, 3) + UInt[W](a);") .S007 3 9
#guard fails (modBody "input a: Bool;\nlet x = UInt[W](a) + resize(1, 2, 3);") .S005 3 17
#guard fails ("comptime fn g() -> Nat {\nreturn 1;\n}\nmodule M() {\nreturn;\n}\n" ++
  "fn h() -> Nat { return g(1); }") .S006 5 1

/-!
`S006`: a `comptime fn` has no call of `read_port` or `write_port`, also in the receiver form.
The position is the call. The rule comes before an `S007` of the call at that position.
-/
def ctBody (s : String) : String := "comptime fn f(x: Nat) -> Nat {\n" ++ s ++ "\nreturn x;\n}"
#guard fails (ctBody "let r = read_port(x, 1, true);") .S006 2 9
#guard fails (ctBody "x.write_port(1, 2, true);") .S006 2 1
#guard fails (ctBody "let r = read_port(x, 1);") .S006 2 9
#guard fails (ctBody "x.write_port(1, 2);") .S006 2 1
#guard message (ctBody "x.write_port(1, 2);") == "a `comptime fn` has no memory port call"
#guard ok (modBody
  "mem m: [UInt[8]; 4];\nlet r = read_port(m, 0, true);\nm.write_port(0, 1, true);")
#guard ok (fnBody "return read_port(p, p, p).valid;")

/-!
A user function `read_port` or `write_port` shadows the prelude function, so its call gets no
memory rule. The check reads the resolved callee, never the name.
-/
#guard ok (ctBody "let r = read_port(x);" ++ "\ncomptime fn read_port(a: Nat) -> Nat { return a; }")
#guard ok (ctBody "let r = x.write_port();" ++ "\nfn write_port(a: Nat) -> Nat { return a; }")
#guard fails (ctBody "let r = x.write_port(1);" ++ "\nfn write_port(a: Nat) -> Nat { return a; }")
  .S007 2 9

/-!
`S007`: `read_port` has three arguments and `write_port` four, also in the receiver form. The
position is the call, which starts at the receiver in the receiver form.
-/
#guard fails (modBody "mem m: [UInt[8]; 4];\nlet r = read_port(m, 0);") .S007 3 9
#guard message (modBody "mem m: [UInt[8]; 4];\nlet r = read_port(m, 0);") ==
  "`read_port` takes 3 argument(s), but it has 2"
#guard fails (modBody "mem m: [UInt[8]; 4];\nwrite_port(m, 0, 1, true, 4);") .S007 3 1
#guard fails (modBody "mem m: [UInt[8]; 4];\nlet r = m.read_port(0, true, 1);") .S007 3 9
#guard fails (modBody "mem m: [UInt[8]; 4];\nm.write_port(0, true);") .S007 3 1

/-!
`S007`: the prelude struct `ReadResponse` has one index argument, and its constructor two
arguments or none. The position is the type name, the index, or the call.
-/
#guard ok (fnBody "let r: ReadResponse[Bool] = ReadResponse[Bool](p, p);\nreturn r.valid;")
#guard ok (fnBody "return ReadResponse[Bool]().valid;")
#guard fails (fnBody "let r: ReadResponse = p;\nreturn p;") .S007 2 8
#guard fails (fnBody "let r = ReadResponse;\nreturn p;") .S007 2 9
#guard fails (fnBody "let r: ReadResponse[Bool, Bool] = p;\nreturn p;") .S007 2 8
#guard fails (fnBody "let r = ReadResponse[Bool, Bool];\nreturn p;") .S007 2 9
#guard fails (fnBody "let r = ReadResponse[Bool](p);\nreturn p;") .S007 2 9
#guard message (fnBody "let r = ReadResponse[Bool](p);\nreturn p;") ==
  "a struct constructor takes 0 or 2 argument(s), but it has 1; pass one value for each " ++
    "field, or none for the zero"
#guard fails (fnBody "let r = TypeInfo(p);\nreturn p;") .S007 2 9
#guard message (fnBody "let r = TypeInfo(p);\nreturn p;") ==
  "a struct constructor takes 0 or 6 argument(s), but it has 1; pass one value for each " ++
    "field, or none for the zero"
#guard fails (fnBody "let r = PortKey[Bool]();\nreturn p;") .S007 2 9
#guard message (fnBody "let r = PortKey[Bool]();\nreturn p;") ==
  "`PortKey` takes 0 argument(s), but it has 1; pass one argument for each `comptime` " ++
    "parameter of `PortKey`"
#guard fails (fnBody "let r = ReadResponse(p, p);\nreturn p;") .S007 2 9

/-!
The walk skips the prelude struct, because it has no source position. Its errors would be at
`0:0` and win over each user error. A user struct with the same forms gets the error.
-/
def badStruct (pre : Bool) : Resolve.Item :=
  .struct ⟨0, 0⟩ ⟨⟨0, 0⟩, "ReadResponse"⟩ [] [⟨⟨⟨0, 0⟩, "data"⟩, .name ⟨0, 0⟩ "UInt" (.type .uint)⟩]
    pre
#guard (Check.check #[badStruct true]).toBool
#guard match Check.check #[badStruct false] with
  | .error e => e.code == .S007 && e.pos == ⟨0, 0⟩
  | .ok _ => false
#guard (Check.check (Resolve.preludeStructs 0).toArray).toBool

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

/-!
`S007` of a variant constructor (slice 3, section 5.6): one payload value for each payload type
of the variant, at the start of the path. A path without a call has no payload value. An enum
has no parameters, so its name takes no index. A call `E(args)` of the enum type is for `Elab`.
-/
def ops : String := "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n"

#guard ok (ops ++ "fn f(x: UInt[8]) -> Op { let a = Op::Add(); return Op::Load(x); }")
#guard ok (ops ++ "fn f(x: UInt[8]) -> Op { return Op(x); }")
#guard fails (ops ++ "fn f(x: UInt[8]) -> Op { return Op::Load(x, x); }") .S007 2 33
#guard message (ops ++ "fn f(x: UInt[8]) -> Op { return Op::Load(x, x); }") ==
  "the variant `Op::Load` has 1 payload value(s), but the constructor has 2; pass one value " ++
  "for each payload type"
#guard fails (ops ++ "fn f() -> Op { return Op::Load; }") .S007 2 23
#guard fails (ops ++ "fn f() -> Op { return Op::Add(1); }") .S007 2 23
#guard fails (ops ++ "fn f() -> Op[1] { return Op(); }") .S007 2 11
#guard fails "enum E: UInt[1] { A = 0 }\nconst C: E = E::A(E::A);" .S007 2 14

/-! The payload values of a constructor in a static position are static positions too. -/
#guard fails (ops ++ "module M() {\ninput a: UInt[8];\nreg q: Op = Op::Load(a);\n}") .S005 4 22
#guard ok (ops ++ "module M() {\ninput a: UInt[8];\nlet q = Op::Load(a);\n}")

/-! The check reads the tag value of a variant as a static position, also in an unused enum. -/
#guard fails "enum E: UInt[2] { A = UInt[2][1] }" .S007 1 23

/-!
`S007` of a variant pattern (slice 3, section 5.6): one binder or `_` for each payload value of
the variant, at the start of the path. `Op::Add()` has no binder. `arms s` puts the arms `s` on
line 3, from column 20.
-/
def pair : String := "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n"
def arms (s : String) : String :=
  pair ++ "fn f(x: Op) -> UInt[8] {\nreturn match (x) { " ++ s ++ " };\n}"

#guard ok (arms "Op::Add() => 0, Op::Load(_) => 0, Op::Pair(b, w) => 0, _ => 0")
#guard fails (arms "Op::Add => 0, Op::Pair(a) => 0, _ => 0") .S007 3 34
#guard message (arms "Op::Add => 0, Op::Pair(a) => 0, _ => 0") ==
  "the variant `Pair` has 2 payload value(s), but the pattern has 1; write one binder or `_` " ++
  "for each payload value"
#guard fails (arms "Op::Load => 0, _ => 0") .S007 3 20
#guard fails (arms "Op::Add(_) => 0, _ => 0") .S007 3 20
#guard message (arms "Op::Add(_) => 0, _ => 0") ==
  "the variant `Add` has 0 payload value(s), but the pattern has 1; write one binder or `_` " ++
  "for each payload value"

/-! The first error by position wins: a pattern before an error in an earlier arm value. -/
#guard fails (arms "Op::Load => Op::Add(1), _ => 0") .S007 3 20
#guard fails (arms "Op::Add => Op::Add(1), Op::Load => 0") .S007 3 31

/-!
A `match` in a static position: its scrutinee and its arm values are static positions. A binder
is a plain local, not a resource, so a static position can name it. It is not a mutable root.
-/
#guard ok (pair ++ "module M() {\nreg r: UInt[8] = " ++
  "match (Op::Load(1)) { Op::Load(v) => v, _ => 0 };\n}")
#guard fails (pair ++ "module M() {\ninput a: Op;\nreg r: UInt[8] = match (a) { _ => 0 };\n}")
  .S005 4 25
#guard fails (pair ++ "module M() {\ninput a: UInt[8];\n" ++
  "reg r: UInt[8] = match (Op::Add) { _ => a };\n}")
  .S005 4 41
#guard ok (pair ++ "module M() {\ninput a: Op;\nlet r = match (a) { Op::Load(v) => v, _ => 0 };\n}")
#guard fails (pair ++ "fn g(mut y: UInt[8]) -> UInt[8] { return y; }\n" ++
  "fn f(x: Op) -> UInt[8] { return match (x) { Op::Load(v) => g(v), _ => 0 }; }") .S008 3 62

/-!
The walk visits each index base once. A chain of indices at the default syntax depth, in an
unused function, thus stays linear.
-/
def indices (n : Nat) : String := String.join (List.replicate n "[0]")
def unusedFns (k : Nat) : String :=
  String.join ((List.range k).map fun i =>
    s!"fn f{i}(x: Nat) -> Nat \{ return x{indices 4095}; }\n")
#guard ok (unusedFns 8)
#guard fails ("fn unused(x: Nat) -> Nat { return UInt[8]" ++ indices 4094 ++ "; }") .S007 1 35

/-!
Port families (section 5.6). A family key is a static position, so a resource there is `S005`.
A family names ports: its name in a static position is `S005`, also before its declaration, and
it is no mutable root (`S008`).
-/
#guard ok (modBody ("comptime for i in 0..2 {\ninput req[i]: Bool;\n}\noutput o: Bool;\n" ++
  "o := req[1];"))
#guard fails (modBody "wire w: Bool;\ninput req[w]: Bool;") .S005 3 11
#guard message (modBody "wire w: Bool;\ninput req[w]: Bool;") ==
  "`w` is a wire; a static position needs a static value"
#guard fails (modBody "input a: Bool;\noutput g[a]: Bool;") .S005 3 10
#guard fails (modBody "input req[0]: Bool;\ninput a: Bool;\nlet y = req[a];") .S005 4 13
#guard fails (modBody "input req[0]: Bool;\ncomptime if (req[0]) {}") .S005 3 14
#guard message (modBody "input req[0]: Bool;\ncomptime if (req[0]) {}") ==
  "`req` is a port; a static position needs a static value"
#guard fails (modBody "let x: UInt[req[0]] = 0;\ninput req[0]: Bool;") .S005 2 13
#guard fails (modBody "input req[0]: Bool;\npush(req, 1);") .S008 3 6
#guard message (modBody "input req[0]: Bool;\npush(req, 1);") ==
  "a `mut` actual has a `let mut` local or a `mut` formal as its root"
#guard fails (modBody "push(req[0], 1);\ninput req[0]: Bool;") .S008 2 6
#guard fails "comptime fn g() -> Nat {\ninput req[0]: Bool;\nreturn 1;\n}" .S006 2 1

/-!
The builtins (section 9.2, G11). The operand of `@TypeOf` is no static position, also in a static
position, but its indices and keys are. The key of `@field` is a static position, and its base
takes the position of the `@field`.
-/
#guard ok (modBody "reg r: UInt[8] = 0;\nlet x: UInt[data_bits(@TypeOf(r))] = 0;")
#guard ok (modBody "reg r: Bool = false;\ncomptime if (@TypeOf(r) == Reg[Bool]) {}")
#guard ok (modBody "reg r: Bool = false;\nlet y = @field(r, 0);")
#guard fails (modBody ("reg rs: [Bool; 2] = [false, false];\nwire w: UInt[1];\n" ++
  "let t = @TypeOf(rs[w]);")) .S005 4 20
#guard fails (modBody "wire w: Bool;\nlet p = 1;\nlet y = @field(p, w);") .S005 4 19
#guard message (modBody "wire w: Bool;\nlet p = 1;\nlet y = @field(p, w);") ==
  "`w` is a wire; a static position needs a static value"
#guard fails (modBody "reg r: Bool = false;\nlet y: UInt[@field(r, 0)] = 0;") .S005 3 20
#guard fails (modBody "reg r: Bool = false;\nwire w: Bool;\nlet t = @TypeOf(@field(r, w));")
  .S005 4 27

/-! A `mut` actual through `@field` has the root of its base (`S008`). -/
def mutFns (s : String) : String :=
  "fn g(mut a: Nat) -> Nat { return 1; }\nfn h(mut a: Nat, mut b: Nat) -> Nat { return 1; }\n" ++
    fnBody s
#guard ok (mutFns "let mut y = 1;\nlet mut z = 1;\nlet r = h(@field(y, 0), @field(z.a, 1));")
#guard fails (mutFns "let y = 1;\nlet r = g(@field(y, 0));") .S008 5 11
#guard message (mutFns "let y = 1;\nlet r = g(@field(y, 0));") ==
  "a `mut` actual has a `let mut` local or a `mut` formal as its root"
#guard fails (mutFns "let mut y = 1;\nlet r = h(@field(y, 0), @field(y, 1));") .S008 5 25
#guard message (mutFns "let r = g(@field(f(p), 0));") == "a `mut` actual is a place"
#guard fails (mutFns "let r = g(@TypeOf(p));") .S008 4 11

/-!
The argument of `@typeInfo` is no static position, also in a static position (ADR 0031, G3), so a
register there is no `S005`. The index rule still holds for an index in it, also in a query
operand in it.
-/
#guard ok (modBody "reg r: Bool = false;\nlet t = @typeInfo(r);")
#guard ok (modBody "reg r: Bool = false;\ncomptime if (@typeInfo(r).width == 1) {}")
#guard fails (modBody ("reg rs: [Bool; 2] = [false, false];\nwire w: UInt[1];\n" ++
  "let t = @typeInfo(rs[w]);")) .S005 4 22
#guard fails (modBody ("reg rs: [Bool; 2] = [false, false];\nwire w: UInt[1];\n" ++
  "let t = @typeInfo(@TypeOf(rs[w]));")) .S005 4 30
#guard ok (modBody "reg r: Bool = false;\nlet t = @Struct(r);")

/-!
The operand of `@ports` is no static position, also in a static position, but its indices and
keys are (G1). Thus `@ports(us[r])` is `S005` at `r`, also in a type position.
-/
#guard ok (modBody "reg r: Bool = false;\nlet t = @ports(r);")
#guard ok (modBody "reg r: Bool = false;\nlet x: UInt[data_bits(@ports(r))] = 0;")
#guard ok (modBody "reg r: Bool = false;\nlet y: @ports(r) = 0;")
#guard fails (modBody "let us = [1];\nreg r: UInt[1] = 0;\nlet t = @ports(us[r]);") .S005 4 19
#guard message (modBody "let us = [1];\nreg r: UInt[1] = 0;\nlet t = @ports(us[r]);") ==
  "`r` is a register; a static position needs a static value"
#guard fails (modBody "let us = [1];\nwire w: Bool;\nlet y: @ports(@field(us, w)) = 0;")
  .S005 4 26

/-!
A builtin in a type position (F39) is no static position, so `@field(rs, 0)` there names the
registers `rs` without `S005`. The key of `@field` there is still static. An index after the
builtin is `S007` "Index of a builtin type" at the `@`, at 1, 2, and 3 levels.
-/
#guard ok (modBody "reg rs: [Bool; 2] = [false, false];\nlet y: @field(rs, 0) = 0;")
#guard ok (modBody "reg rs: [Bool; 2] = [false, false];\nlet y: [@field(rs, 0); 2] = 0;")
#guard fails (modBody "wire w: UInt[1];\nlet xs = [1, 2];\nlet y: @field(xs, w) = 0;") .S005 4 19
#guard fails (modBody "let x = 1;\nlet y: @TypeOf(x)[8] = x;") .S007 3 8
#guard message (modBody "let x = 1;\nlet y: @TypeOf(x)[8] = x;") ==
  "`@TypeOf(...)` in a type position takes 0 argument(s), but it has 1; the type is " ++
    "complete, so remove the index"
#guard message (modBody "let x = 1;\nlet y: @TypeOf(x)[8][2] = x;") ==
  "`@TypeOf(...)` in a type position takes 0 argument(s), but it has 1; the type is " ++
    "complete, so remove the index"
/-! In a chain of indices, only the first index after the builtin reports, at each depth. -/
#guard fails (modBody "let x = 1;\nlet y: @TypeOf(x)[1][2][3] = x;") .S007 3 8
#guard message (modBody "let x = 1;\nlet y: @TypeOf(x)[1][2, 3][4] = x;") ==
  "`@TypeOf(...)` in a type position takes 0 argument(s), but it has 1; the type is " ++
    "complete, so remove the index"
#guard message (modBody "let fs = [];\nlet y: @Struct(fs)[1, 2][3][4][5] = 0;") ==
  "`@Struct(...)` in a type position takes 0 argument(s), but it has 2; the type is " ++
    "complete, so remove the index"
#guard fails (modBody "let fs = [];\nlet y: [@Struct(fs)[8, 2]; 2] = 0;") .S007 3 9
#guard message (modBody "let fs = [];\nlet y: [@Struct(fs)[8, 2]; 2] = 0;") ==
  "`@Struct(...)` in a type position takes 0 argument(s), but it has 2; the type is " ++
    "complete, so remove the index"

/-!
`@typeInfo` gives a record and `@field` any part, so their index in a type has the fix of the
builtin (section 6.2).
-/
#guard fails (modBody "let y: @typeInfo(Bool)[1] = 0;") .S007 2 8
#guard message (modBody "let y: @typeInfo(Bool)[1] = 0;") ==
  "`@typeInfo(...)` in a type position takes 0 argument(s), but it has 1; `@typeInfo` gives a " ++
    "record, so remove the index, and select a `Type` from the record, for example " ++
    "`@field(@typeInfo(T), \"element\")`"
#guard message (modBody "let xs = [Bool];\nlet y: @field(xs, 0)[1, 2] = 0;") ==
  "`@field(...)` in a type position takes 0 argument(s), but it has 2; remove the index, or " ++
    "select inside `@field`, for example `@field(@field(x, k), i)`"

/-! `@ports` gives a list and not a type, so its index in a type has its own text (section 6.2). -/
#guard fails (modBody "let u = 1;\nlet y: @ports(u)[0] = 0;") .S007 3 8
#guard message (modBody "let u = 1;\nlet y: @ports(u)[0][1] = 0;") ==
  "`@ports` gives a `List[PortInfo]`; select a port type with `@field(@ports(u)[0], \"ty\")`"
#guard ok (modBody "let u = 1;\nlet y = @ports(u)[0];")

end Silicon.Source.Test.Check
