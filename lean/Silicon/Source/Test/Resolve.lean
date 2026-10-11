-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Parse
import Silicon.Source.Resolve

/-!
These tests check the resolver at its public boundary. They check the code and the position of
each `S002` and `S003` rule, the scopes and the shadowing, the prelude, and the pass order. They
also check the declaration of resolved names.
-/

namespace Silicon.Source.Test.Resolve

open Silicon.Source Resolve
open Silicon.Source.Lex (defaultSyntaxDepth)

def run (s : String) : Except Error (Array Resolve.Item) :=
  match Parse.parseSource defaultSyntaxDepth s with
  | .ok items => resolve items
  | .error e => .error e

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

/-! The declaration of the name in the last statement `return x;` of the first function. -/
def retRef (s : String) : Option Ref :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.fn _ _ _ _ _ b) =>
      match b.getLast? with
      | some (.ret _ (some (.name _ _ r))) => some r
      | _ => none
    | _ => none
  | .error _ => none

/-! A file without an error resolves. -/
#guard ok ""
#guard ok (fnBody "let x = p; return x;")
#guard ok (modBody "input a: UInt[W];\noutput b: UInt[W];\nb := resize(UInt[W], a);")
#guard ok ("module M(comptime W: Nat) domains(clk) {\nreg r: UInt[W] = 0;\n" ++
  "wire w: UInt[W];\nw := r;\nr := w;\n}")
#guard ok (fnBody "static_assert(p, \"a\"); error(\"b\"); return p;")
#guard ok "const N: Int = 3;\nconst K: Nat = N;\nconst T: SInt[K] = reinterpret(SInt[K], 0);"

/-! `S002`: two items with one name. The position is the name of the second item. -/
#guard fails "const A: Nat = 1;\nfn A() -> Nat { return 1; }" .S002 2 4
#guard fails "module A() {}\nmodule A() {}" .S002 2 8
#guard fails "const A: Nat = 1;\nconst B: Nat = 1;\ncomptime fn A() -> Nat { return 1; }" .S002 3 13

/-! `S002`: the parameters, the domain names, and the body share one scope. -/
#guard fails "fn f(a: Bool, a: Bool) -> Bool { return a; }" .S002 1 15
#guard fails (fnBody "let p = true;\nreturn p;") .S002 2 5
#guard fails (modBody "wire W: Bool;") .S002 2 6
#guard fails "module M(comptime clk: Nat) domains(clk) {}" .S002 1 37
#guard fails "module M() domains(clk) {\nreg clk: Bool = false;\n}" .S002 2 5
#guard fails (modBody "input a: Bool;\noutput a: Bool;") .S002 3 8
#guard fails (modBody "let u = 1;\ninstance u = M(1);") .S002 3 10
#guard fails (fnBody "let mut x = p;\nlet x = p;\nreturn x;") .S002 3 5

/-! `S002`: the loop variable and the top-level statements of the loop body share one scope. -/
#guard fails (fnBody "comptime for i in 0..2 {\nlet i = 1;\n}\nreturn p;") .S002 3 5
#guard ok (fnBody "comptime for i in 0..2 {\n{ let i = 1; }\n}\nreturn p;")

/-! A nested scope can shadow an outer local, a parameter, or an item. -/
#guard ok (fnBody "let x = 1;\n{ let x = 2; }\nreturn p;")
#guard ok (fnBody "{ let p = 1; }\nreturn p;")
#guard ok (fnBody "comptime if (p) { let x = 1; } else { let x = 2; }\nreturn p;")
#guard ok (fnBody "let x = 1;\ncomptime if (p) { let x = 2; }\nreturn p;")
#guard ok (fnBody "let x = 1;\ncomptime for x in 0..x { let y = x; }\nreturn p;")
#guard retRef "fn f() -> Nat { let x = 2; return x; }\nconst x: Nat = 1;" == some (.local 0)
#guard retRef "fn f() -> Nat { return x; }\nconst x: Nat = 1;" == some (.item 1)
#guard retRef "fn f(a: Nat, b: Nat) -> Nat { let c = a; { let c = b; } return c; }" ==
  some (.local 2)
#guard retRef "fn f(a: Nat) -> Nat { { let a = 1; } return a; }" == some (.local 0)

/-! A declaration can shadow a prelude name. The language reserves no name. -/
#guard ok "const Bool: Nat = 1;"
#guard ok "fn resize(x: Nat) -> Nat { return x; }"
#guard retRef "fn f() -> Nat { return resize; }\nfn resize(x: Nat) -> Nat { return x; }" ==
  some (.item 1)
#guard retRef "fn f() -> Nat { return resize; }" == some (.fn .resize)
#guard retRef "fn f() -> Nat { return UInt; }" == some (.type .uint)
#guard retRef "fn f(error: Nat) -> Nat { return error; }" == some (.local 0)
#guard ok (fnBody "let Int = 1;\nreturn p;")

/-! A shadowed prelude type is not a type in the scope of its shadow. -/
#guard fails "const UInt: Nat = 8;\nconst A: UInt[8] = 0;" .S003 2 10
#guard fails "fn f(Bool: Nat, x: Bool) -> Nat { return x; }" .S003 1 20
#guard ok (fnBody "{ let Bool = 1; }\nlet x: Bool = p;\nreturn x;")

/-! `S003`: a name without a declaration. The position is the name. -/
#guard fails (fnBody "return q;") .S003 2 8
#guard fails (fnBody "return p + f(p, q);") .S003 2 17
#guard fails "const A: Nat = B;" .S003 1 16
#guard fails "const A: Foo = 1;" .S003 1 10
#guard message "const A: Foo = 1;" == "`Foo` is not declared"

/-! `S003`: a local is visible only after its declaration, and only in its scope. -/
#guard fails (fnBody "let y = x;\nlet x = p;\nreturn y;") .S003 2 9
#guard fails (fnBody "let x = x;\nreturn x;") .S003 2 9
#guard fails (modBody "reg r: Bool = r;") .S003 2 15
#guard fails (fnBody "{ let a = 1; }\nreturn a;") .S003 3 8
#guard fails (fnBody "comptime if (p) { let a = 1; }\nreturn a;") .S003 3 8
#guard fails (fnBody "comptime for i in 0..2 {}\nreturn i;") .S003 3 8
#guard fails (fnBody "comptime for i in 0..i {}\nreturn p;") .S003 2 22
#guard fails (modBody "w := 1;\nwire w: Bool;") .S003 2 1
#guard fails (modBody "let y = u.a;\ninstance u = M(1);") .S003 2 9

/-! `S003`: a parameter is visible in the later types and the body, not in its own type. -/
#guard ok "fn f(comptime W: Nat, x: UInt[W]) -> UInt[W] { return x; }"
#guard fails "fn f(x: UInt[x]) -> Bool { return true; }" .S003 1 14
#guard fails "fn f(x: UInt[W], comptime W: Nat) -> Bool { return true; }" .S003 1 14
#guard fails "module M(comptime A: UInt[B], comptime B: Nat) {}" .S003 1 27

/-! An item is visible in the full file, also before its declaration. -/
#guard ok "fn f() -> Nat { return g(); }\nfn g() -> Nat { return N; }\nconst N: Nat = 1;"
#guard ok "module A() { instance b = B(); }\nmodule B() {}"
#guard ok "module A() { instance a = A(); }"

/-! The name after `.` is not resolved. -/
#guard ok "module A() { instance b = B(); let y = b.zzz; }\nmodule B() {}"

/-!
A module without a `domains` clause has the default domain `clock`. It comes before the
parameters, so a parameter `clock` is `S002` at the parameter. `domains()` declares no domain.
-/
#guard ok "module M() {\nlet c = clock;\n}"
#guard ok "module M() domains(clock) {\nlet c = clock;\n}"
#guard fails "module M() domains() {\nlet c = clock;\n}" .S003 2 9
#guard ok "module M() domains() {\nwire clock: Bool;\n}"
#guard fails "module M() {\nwire clock: Bool;\n}" .S002 2 6
#guard fails "module M() domains(clock) {\nwire clock: Bool;\n}" .S002 2 6
#guard fails "module M(comptime clock: Nat) {}" .S002 1 19
#guard ok "module M(comptime clock: Nat) domains() {}"
#guard fails "module M(comptime clock: Nat) domains(clock) {}" .S002 1 39
#guard ok "module M() {\n{ let clock = 1; }\n}"

/-! `S003`: a position that needs a fixed kind gets a name of that kind. -/
#guard fails "const N: Nat = 1;\nconst M: N = 1;" .S003 2 10
#guard fails "fn g() -> Nat { return 1; }\nconst M: g[1] = 1;" .S003 2 10
#guard fails "fn f(x: resize) -> Bool { return true; }" .S003 1 9
#guard message "const N: Nat = 1;\nconst M: N = 1;" == "`N` is not a type"
#guard fails "fn g() -> Nat { return 1; }\nmodule M() {\ninstance u = g();\n}" .S003 3 14
#guard fails "module M() {\ninstance u = resize();\n}" .S003 2 14
#guard fails "module M() {\ninstance u = N();\n}" .S003 2 14
#guard fails "module M() {\nlet N = 1;\ninstance u = N();\n}" .S003 3 14
#guard fails "module A() {}\nmodule B() {\nlet x = A;\n}" .S003 3 9
#guard fails "module A() {}\nconst N: Nat = A();" .S003 2 16

/-! `S003`: a prelude name of a later slice. The message names the slice. -/
#guard fails "fn f(x: TypeInfo) -> Bool { return true; }" .S003 1 9
#guard message "fn f(x: TypeInfo) -> Bool { return true; }" ==
  "`TypeInfo` is not in slice 1; it comes in slice 4"
#guard fails (fnBody "let xs = read(p);\nreturn p;") .S003 2 10
#guard fails (modBody "reg r: Reg[Bool] = 0;") .S003 2 8
#guard message (modBody "reg r: Reg[Bool] = 0;") ==
  "`Reg` is not in slice 1; it comes in slice 3"
#guard ok "const Wire: Nat = 1;\nconst N: Nat = Wire;"

/-! Each pass reports its first error by position. -/
#guard fails (fnBody "return a + b;") .S003 2 8
#guard fails "fn f() -> Bool { let x = true; let x = true; return x; }\nconst f: Nat = 1;"
  .S002 1 36
#guard fails "const f: Nat = 1;\nfn f() -> Bool { let x = true; let x = true; return x; }"
  .S002 2 4

/-! Pass 2 comes before pass 3: an `S002` wins over an earlier `S003`. -/
#guard fails "fn f() -> Bool { return q; }\nconst f: Nat = 1;" .S002 2 7
#guard fails (fnBody "let y = q;\nlet y = p;\nreturn y;") .S002 3 5
#guard fails "const A: Foo = 1;\nmodule M() {\nwire a: Bool;\nwire a: Bool;\n}" .S002 4 6

/-!
The walk is linear and its stack follows the syntax depth. These inputs are at the default
syntax depth or hold many statements in one scope.
-/
def lets (n : Nat) : String :=
  String.join ((List.range n).map fun i => s!"let x{i} = p;\n")
def blocks (n : Nat) : String := "".pushn '{' n ++ "let a = p;" ++ "".pushn '}' n
def chain (n : Nat) : String := " + ".intercalate (List.replicate n "p")

#guard ok (fnBody (lets 20000 ++ "return p;"))
#guard fails (fnBody (lets 20000 ++ "let x0 = p;\nreturn p;")) .S002 20002 5
#guard ok (fnBody (blocks 4094 ++ "\nreturn p;"))
#guard ok (fnBody ("return " ++ chain 4096 ++ ";"))
#guard ok (fnBody (String.join (List.replicate 20000 "{ let a = p; }\n") ++ "return p;"))

end Silicon.Source.Test.Resolve
