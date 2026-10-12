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
#guard message ("const A: S[1] = 0;" ++ structs) == "`S` takes 0 argument(s), but it has 1"
#guard fails ("const A: P[8][1] = 0;" ++ structs) .S007 1 10
#guard fails (fnBody "let t = P[1, 2];\nreturn p;" ++ structs) .S007 2 9
#guard fails (fnBody "let t = E[0];\nreturn p;" ++ structs) .S007 2 9

/-!
`S007`: a struct with parameters is not used without its arguments: as a type, as a value, and
as the callee of a constructor. The position is the name.
-/
#guard fails ("const A: P = 0;" ++ structs) .S007 1 10
#guard message ("const A: P = 0;" ++ structs) == "`P` takes 1 argument(s), but it has 0"
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
  "a struct constructor takes 0 or 2 argument(s), but it has 1"
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

/-! `S007` at the start of a receiver call: no parameter without `comptime`, or the arity. -/
#guard fails (lists "let t = Int.list();") .S007 6 9
#guard message (lists "let t = Int.list();") ==
  "`list` has no parameter without `comptime` for the receiver"
#guard fails (lists "let t = Int.data_bits();") .S007 6 9
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

end Silicon.Source.Test.Check
