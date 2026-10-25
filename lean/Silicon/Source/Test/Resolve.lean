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

/-! The user items of a resolved file, without the prelude structs. -/
def users (s : String) : Option (Array Resolve.Item) :=
  (run s).toOption.map fun a => a.extract 0 (a.size - preludeCount)

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

/-!
A shadowed prelude type is not a prelude type in the scope of its shadow. A local in a type
position can hold a type, so only `Elab` checks it.
-/
#guard fails "const UInt: Nat = 8;\nconst A: UInt[8] = 0;" .S003 2 10
#guard ok "fn f(Bool: Nat, x: Bool) -> Nat { return x; }"
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

/-!
The prelude structs of slice 4 are type names and names in an expression (section 5.6). They are
the items after `ReadResponse`, and a user item of one of their names shadows it.
-/
#guard ok "fn f(x: TypeInfo) -> Bool { return true; }"
#guard ok "module M() {\ninput k: PortKey;\nreg r: PortInfo = PortInfo();\n}"
#guard retRef "fn f() -> Bool { return FieldInfo; }" == some (.item 2)
#guard retRef "fn f() -> Bool { return TypeInfo; }" == some (.item 3)
#guard retRef "fn f() -> Bool { return VariantInfo; }" == some (.item 4)
#guard retRef "fn f() -> Bool { return PortKey; }" == some (.item 5)
#guard retRef "fn f() -> Bool { return PortInfo; }" == some (.item 6)
#guard retRef "fn f() -> Bool { return PortKey; }\nstruct PortKey {}" == some (.item 1)
#guard ok "const TypeInfo: Nat = 1;\nconst N: Nat = TypeInfo;"

/-!
The handle types and `read` of slice 3 are prelude names (section 5.6). `Domain` stays `S003`
at the name, with its text of section 6.2. A user item or a local shadows each prelude name.
-/
#guard ok (fnBody "let xs = read(p);\nreturn p.read();")
#guard ok (modBody ("reg r: Reg[Bool] = 0;\nwire w: Wire[Bool];\ninput i: Input[Bool];\n" ++
  "let m: Type = Mem[Bool, 2];"))
#guard ok "const Wire: Nat = 1;\nconst N: Nat = Wire;"
#guard fails "fn f(x: Domain) -> Bool { return true; }" .S003 1 9
#guard message "fn f(x: Domain) -> Bool { return true; }" ==
  "`Domain` is not supported yet; it comes with more domains (#11); a module has one domain " ++
    "or none, so it needs no `Domain` value"
#guard fails (modBody "let d = Domain;") .S003 2 9
#guard ok "const Domain: Nat = 1;\nconst N: Nat = Domain;"
#guard retRef (fnBody "return read;") == some (.fn .read)
#guard retRef (fnBody "return read;" ++ "\nfn read(x: Bool) -> Bool { return x; }") ==
  some (.item 1)
#guard retRef (fnBody "let read = p;\nreturn read;") == some (.local 1)
#guard ok ("fn read(x: Bool, y: Bool) -> Bool { return x; }\n" ++ fnBody "return read(p, p);")
#guard ok "module read() {}\nmodule M() {\ninstance read = read();\nlet x = read.q;\n}"

/-!
The first argument of `Instance` resolves by the ordinary scoping to a module item, in a type and
in an expression. Another first argument is `S003` at its start, with the text of section 6.2.
That error replaces each `S003` in the argument. A module name in another argument is `S003`.
-/
def counter : String := "module C(comptime W: Nat) {}\n"
#guard ok (counter ++ "module M() {\nlet t = Instance[C, 8];\nlet x: Instance[C, 8] = t;\n}")
#guard ok (counter ++ "fn f(x: Instance[C, 8]) -> Bool { return true; }")
#guard fails (counter ++ "const N: Nat = 1;\nconst T: Type = Instance[N, 8];") .S003 3 26
#guard message (counter ++ "const N: Nat = 1;\nconst T: Type = Instance[N, 8];") ==
  "the first argument of `Instance` is not a module; write the module first, for example " ++
    "`Instance[Counter, 8]`"
#guard fails (counter ++ "fn f(x: Instance[Q, 8]) -> Bool { return true; }") .S003 2 18
#guard message (counter ++ "fn f(x: Instance[Q, 8]) -> Bool { return true; }") ==
  "the first argument of `Instance` is not a module; write the module first, for example " ++
    "`Instance[Counter, 8]`"
#guard fails (counter ++ "module M() {\nlet C = 1;\nlet t = Instance[C, 8];\n}") .S003 4 18
#guard fails (counter ++ "const T: Type = Instance[1 + 2];") .S003 2 26
#guard message (counter ++ "const T: Type = Instance[q::A];") ==
  "the first argument of `Instance` is not a module; write the module first, for example " ++
    "`Instance[Counter, 8]`"
#guard fails (counter ++ "const T: Type = (z, Instance[N]);") .S003 2 18
#guard message (counter ++ "const T: Type = (z, Instance[N]);") == "`z` is not declared"
#guard fails (counter ++ "const T: Type = Instance[C, C];") .S003 2 29
#guard message (counter ++ "const T: Type = Instance[C, C];") ==
  "`C` is not a value; a module is used only in an `instance`"
#guard fails (counter ++ "const T: Type = Reg[C];") .S003 2 21

/-! The container forms of slice 2 resolve their parts. `Unit` and `len` are prelude names. -/
#guard ok (fnBody "let t = (p, [p, p], ());\nlet x: (Bool, [Bool; 2], ()) = t;\nreturn t.0;")
#guard ok (fnBody "let x: (Bool,) = (p,);\nlet n = len([x.0]);\nreturn x.0x0;")
#guard ok "const A: Unit = ();\nconst N: Nat = len([A, A]);"
#guard retRef "fn f() -> Nat { return len; }" == some (.fn .len)
#guard retRef "fn f() -> Nat { return Unit; }" == some (.type .unit)
#guard retRef "fn f(len: Nat) -> Nat { return len; }" == some (.local 0)
#guard fails "const Unit: Nat = 1;\nconst A: Unit = 1;" .S003 2 10

/-! `S003` in a part of a container form. The position is the name. -/
#guard fails (fnBody "return (p, q);") .S003 2 12
#guard fails (fnBody "return [p, q];") .S003 2 12
#guard fails (fnBody "return q.0;") .S003 2 8
#guard fails (fnBody "return [p][q];") .S003 2 12
#guard fails (fnBody "let x: [Bool; N] = [];\nreturn p;") .S003 2 15
#guard fails (fnBody "let x: [Foo; 2] = [];\nreturn p;") .S003 2 9
#guard fails (fnBody "let x: (Bool, Foo) = (p, p);\nreturn p;") .S003 2 15
#guard fails "const N: Nat = 1;\nconst A: (N,) = (1,);" .S003 2 11
#guard message "const N: Nat = 1;\nconst A: (N,) = (1,);" == "`N` is not a type"

/-! The declaration of the type name of the first `const` item. -/
def tyRef (s : String) : Option Ref :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.const _ _ (.name _ _ r) _) => some r
    | some (Resolve.Item.const _ _ (.index _ (.name _ _ r) _) _) => some r
    | _ => none
  | .error _ => none

/-!
A `struct` item and a `type` item are in the item scope. A type name refers to a prelude type,
one of these items, or a local. `Type` and `data_bits` are prelude names.
-/
#guard ok "struct P(comptime W: Nat) { a: UInt[W], b: Bool }\nconst A: P[8] = P[8](1, true);"
#guard ok "type A = UInt[8];\nconst B: A = A(3);"
#guard tyRef "const A: T = 1;\ntype T = Bool;" == some (.item 1)
#guard tyRef "const A: P[8] = 1;\nstruct P(comptime W: Nat) {}" == some (.item 1)
#guard tyRef "const A: Type = Bool;" == some (.type .type)
#guard retRef "fn f() -> Nat { return Type; }" == some (.type .type)
#guard retRef "fn f() -> Nat { return data_bits; }" == some (.fn .dataBits)
#guard retRef "fn f() -> Nat { return S; }\nstruct S {}" == some (.item 1)
#guard retRef "fn f() -> Nat { return A; }\ntype A = Bool;" == some (.item 1)
#guard ok "fn f(comptime T: Type, x: T) -> T { return x; }"
#guard ok "fn f(comptime T: Type) -> Nat { let x: T = T(); return data_bits(T); }"
#guard ok "type A = A;"
#guard fails "const A: Nat = 1;\ntype A = Bool;" .S002 2 6
#guard fails "struct A {}\nmodule A() {}" .S002 2 8

/-!
The parameters of a struct are visible in the later parameter types and in the field types.
They are not visible in their own type or outside the struct. A field name is not a local, so it
can be the name of a parameter.
-/
#guard ok "struct P(comptime T: Type, comptime x: T) { a: T, b: [T; 2] }"
#guard ok "struct P(comptime a: Nat) { a: UInt[a] }"
#guard fails "struct P(comptime W: UInt[W]) { a: Bool }" .S003 1 27
#guard fails "struct P(comptime A: UInt[B], comptime B: Nat) {}" .S003 1 27
#guard fails "struct P(comptime W: Nat) { a: Bool }\nconst N: Nat = W;" .S003 2 16
#guard fails "struct P { a: UInt[W] }" .S003 1 20
#guard fails "struct P(comptime a: Nat, comptime a: Nat) {}" .S002 1 36

/-! `S002`: two fields of a struct with one name. The position is the name of the later field. -/
#guard fails "struct S { a: Bool, a: Bool }" .S002 1 21
#guard fails "struct S {\na: Bool,\nb: Bool,\na: UInt[8],\n}" .S002 4 1
#guard message "struct S { a: Bool, a: Bool }" == "the field `a` is already declared"
#guard fails "const A: Foo = 1;\nstruct S { a: Bool, a: Bool }" .S002 2 21

/-!
A `type` statement declares a local. It is visible after its statement and only in its scope,
so its type reads an outer name.
-/
#guard ok (fnBody "type T = Bool;\nlet x: T = p;\nreturn x;")
#guard ok "type T = Bool;\nfn f() -> Nat { type T = T; let x: T = true; return 1; }"
#guard fails (fnBody "type T = T;\nreturn p;") .S003 2 10
#guard fails (fnBody "type T = Bool;\ntype T = Bool;\nreturn p;") .S002 3 6
#guard fails (fnBody "let T = 1;\ntype T = Bool;\nreturn p;") .S002 3 6
#guard fails (fnBody "{ type T = Bool; }\nlet x: T = p;\nreturn p;") .S003 3 8

/-! An array type `[T; N]` in an expression resolves its element type and its length. -/
#guard ok (fnBody "let t = [Bool; 2];\nlet u = [[UInt[8]; 2]; 3]();\nreturn p;")
#guard fails (fnBody "let t = [Foo; 2];\nreturn p;") .S003 2 10
#guard fails (fnBody "let t = [Bool; N];\nreturn p;") .S003 2 16
#guard fails "const N: Nat = 1;\nconst A: Type = [N; 2];" .S003 2 18

/-! `S003`: a module, a `const`, or a function is not a type, and a struct is not a module. -/
#guard fails "module M() {}\nconst A: M = 1;" .S003 2 10
#guard fails "fn g() -> Nat { return 1; }\nstruct S { a: g }" .S003 2 15
#guard fails "const N: Nat = 1;\ntype A = N;" .S003 2 10
#guard fails "struct S {}\nmodule M() {\ninstance u = S();\n}" .S003 3 14
#guard fails "type A = Bool;\nmodule M() {\ninstance u = A();\n}" .S003 3 14

/-!
The strings and the lists of slice 2 are prelude names: `String`, `List`, `list`, `push`, `pop`,
and `str`. A `mut` parameter is a local, and it keeps its mode.
-/
#guard tyRef "const S: String = \"a\";" == some (.type .string)
#guard tyRef "const L: List[Int] = list(Int);" == some (.type .list)
#guard retRef "fn f() -> Nat { return list; }" == some (.fn .list)
#guard retRef "fn f() -> Nat { return push; }" == some (.fn .push)
#guard retRef "fn f() -> Nat { return pop; }" == some (.fn .pop)
#guard retRef "fn f() -> Nat { return str; }" == some (.fn .str)
#guard retRef "fn f(mut xs: List[Int]) -> Nat { return xs; }" == some (.local 0)
#guard ok "fn f(mut xs: List[Int], x: Int) -> () { push(xs, x); let s = str(pop(xs)); }"
#guard (match run "fn f(mut xs: List[Int], comptime n: Nat, x: Bool) -> () {}" with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.fn _ _ _ ps _ _) => ps.map (·.mode)
    | _ => []
  | .error _ => []) == [ParamMode.mut, .comptime, .none]
#guard ok "const List: Nat = 1;\nconst N: Nat = List;"

/-! The function and the call site of the receiver call `return x.m(...);` of the first item. -/
def retMethod (s : String) : Option (Ref × Nat) :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.fn _ _ _ _ _ b) =>
      match b.getLast? with
      | some (.ret _ (some (.method _ _ _ f _ _ k))) => some (f, k)
      | _ => none
    | _ => none
  | .error _ => none

/-! The parameter that the receiver of `return x.m(...);` of the first item binds to. -/
def retParam (s : String) : Option (Option Nat) :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.fn _ _ _ _ _ b) =>
      match b.getLast? with
      | some (.ret _ (some (.method _ _ _ _ q _ _))) => some q
      | _ => none
    | _ => none
  | .error _ => none

/-!
The name `m` of a receiver call `x.m(args)` is a function of the item scope, else of the
prelude. A local never hides it, and an item hides a prelude function.
-/
#guard retMethod "fn f(p: Bool) -> Bool { return p.g(); }\nfn g(x: Bool) -> Bool { return x; }" ==
  some (.item 1, 0)
#guard retMethod "fn f(g: Bool) -> Bool { return g.g(); }\nfn g(x: Bool) -> Bool { return x; }" ==
  some (.item 1, 0)
#guard retMethod "fn f(xs: List[Int]) -> () { return xs.push(1); }" == some (.fn .push, 0)
#guard retMethod "fn f(p: Bool) -> Nat { return p.len(); }" == some (.fn .len, 0)
#guard retMethod "fn f(p: Bool) -> Nat { return p.len(); }\nfn len(x: Bool) -> Nat { return 1; }"
  == some (.item 1, 0)
#guard retMethod "fn f(T: Type) -> Nat { return T.data_bits(); }" == some (.fn .dataBits, 0)
#guard ok (fnBody "let x = p.resize(UInt[8]);\nreturn p.static_assert(\"a\");")

/-! The receiver binds to the first parameter without a written `comptime` mark, if one exists. -/
#guard retParam "fn f(T: Type) -> Nat { return T.data_bits(); }" == some (some 0)
#guard retParam "fn f(p: Bool) -> Bool { return p.resize(Bool); }" == some (some 1)
#guard retParam "fn f(T: Type) -> Nat { return T.list(); }" == some none
#guard retParam ("fn f(p: Nat) -> Nat { return p.g(1); }\n" ++
  "comptime fn g(comptime a: Nat, b: Nat) -> Nat { return b; }") == some (some 1)

/-! `S003`: the name of a receiver call is not a function there. The position is the name. -/
#guard fails (fnBody "return p.foo();") .S003 2 10
#guard message (fnBody "return p.foo();") == "`foo` is not declared"
#guard fails (fnBody "let h = 1;\nreturn p.h();") .S003 3 10
#guard fails ("const g: Nat = 1;\n" ++ fnBody "return p.g();") .S003 3 10
#guard message ("const g: Nat = 1;\n" ++ fnBody "return p.g();") ==
  "`g` is not a function; a receiver call `a.f()` needs a function `f`, so " ++
    "write `g(a)` to call a type or a function value"
#guard fails ("const len: Nat = 1;\n" ++ fnBody "return p.len();") .S003 3 10
#guard fails ("module M() {}\n" ++ fnBody "return p.M();") .S003 3 10
#guard fails ("struct S {}\n" ++ fnBody "return p.S();") .S003 3 10
#guard fails (fnBody "return p.Bool();") .S003 2 10
#guard message (fnBody "return p.Bool();") ==
  "`Bool` is not a function; a receiver call `a.f()` needs a function `f`, so " ++
    "write `Bool(a)` to call a type or a function value"
#guard fails (fnBody "return p.Reg();") .S003 2 10
#guard message (fnBody "return p.Reg();") ==
  "`Reg` is not a function; a receiver call `a.f()` needs a function `f`, so " ++
    "write `Reg(a)` to call a type or a function value"
#guard fails (fnBody "return p.PortKey();") .S003 2 10
#guard message (fnBody "return p.PortKey();") ==
  "`PortKey` is not a function; a receiver call `a.f()` needs a function `f`, so " ++
    "write `PortKey(a)` to call a type or a function value"

/-! `S003` in the receiver or an argument of a receiver call. The first error by position wins. -/
#guard fails (fnBody "return q.len();") .S003 2 8
#guard fails (fnBody "return q.foo();") .S003 2 8
#guard fails (fnBody "return p.foo(q);") .S003 2 10
#guard fails (fnBody "return p.len(q);") .S003 2 14
#guard fails (fnBody "return p.len().foo();") .S003 2 16

/-! The statements of the body of the first item. -/
def body (s : String) : List Resolve.Stmt :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.fn _ _ _ _ _ b) | some (Resolve.Item.module _ _ _ _ b) => b
    | _ => []
  | .error _ => []

/-!
The call sites of a body count the call nodes and the receiver-call nodes from 0 in pre-order. A
node comes before its callee, its receiver, and its arguments. A call outside the body does not
shift them, and each body starts at 0.
-/
#guard body (fnBody "let a = len(p);\nreturn p.len(len(p));") matches
  [.local _ _ _ _ (.call _ _ _ 0), .ret _ (some (.method _ _ _ _ _ [.call _ _ _ 2] 1))]
#guard body (fnBody "return len(p).len();") matches
  [.ret _ (some (.method _ (.call _ _ _ 1) _ _ _ [] 0))]
#guard body ("fn f(x: UInt[len([1])]) -> Bool {\nreturn x.f(len(x));\n}") matches
  [.ret _ (some (.method _ _ _ _ _ [.call _ _ _ 1] 0))]
#guard body (fnBody "return UInt[8](p)(p);") matches
  [.ret _ (some (.call _ (.call _ _ _ 1) _ 0))]
#guard body ("module M() {\nlet a = len([1]);\n}\nfn g() -> Nat { return len([1]); }") matches
  [.local _ _ _ _ (.call _ _ _ 0)]

/-! The type of the first `const` item. -/
def constTy (s : String) : Option Resolve.TypeExpr :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.const _ _ t _) => some t
    | _ => none
  | .error _ => none

/-!
A function type resolves its parameter types and its result type, in a type and in an
expression. It keeps the `mut` mark of each parameter type. A local and a later item are visible
in it.
-/
#guard ok "fn f(g: fn (Bool, mut UInt[8]) -> Bool) -> Bool { return g(true); }"
#guard ok "fn f(comptime T: Type) -> Type { return fn (T, mut [T; 2]) -> (T, T); }"
#guard ok "const A: fn (T) -> fn () -> T = 1;\ntype T = Bool;"
#guard constTy "const A: fn (mut Bool, T) -> () = 1;\ntype T = Bool;" matches
  some (.fn _ [.mk true (.name _ _ (.type .bool)), .mk false (.name _ _ (.item 1))] (.unit _))
#guard body (fnBody "let h = fn (mut Bool) -> fn () -> Bool;\nreturn p;") matches
  [.local _ _ _ _ (.fnType _ [.mk true (.name _ _ (.type .bool))]
    (.fn _ [] (.name _ _ (.type .bool)))), _]
#guard body (fnBody "let h = (fn () -> Bool)[1];\nreturn p;") matches
  [.local _ _ _ _ (.index _ (.fnType _ [] _) [.num _ 1]), _]

/-! `S003` in a function type. The position is the name. -/
#guard fails "const A: fn (Foo) -> Bool = 1;" .S003 1 14
#guard fails "const A: fn () -> Foo = 1;" .S003 1 19
#guard fails "const A: fn (mut fn () -> Foo) -> Bool = 1;" .S003 1 27
#guard fails (fnBody "let h = fn (Foo) -> Bool;\nreturn p;") .S003 2 13
#guard fails (fnBody "let h = fn () -> Foo;\nreturn p;") .S003 2 18
#guard fails (fnBody "let h = fn (Bool, mut Foo) -> Bool;\nreturn p;") .S003 2 23
#guard fails "fn g() -> Nat { return 1; }\nconst A: fn (g) -> Bool = 1;" .S003 2 14
#guard message "fn g() -> Nat { return 1; }\nconst A: fn (g) -> Bool = 1;" == "`g` is not a type"
#guard fails "module M() {}\nconst A: fn () -> M = 1;" .S003 2 19

/-!
A function name as a value resolves to its item, also a generic function. A builtin resolves to
its prelude function. `Elab` reports a generic function and a builtin as values (`S010`). A
module is not a value.
-/
#guard retRef "fn f() -> Nat { let h = g; return h; }\nfn g() -> Nat { return 1; }" ==
  some (.local 0)
#guard body "fn f() -> Nat { let h = g; return h(); }\nfn g() -> Nat { return 1; }" matches
  [.local _ _ _ _ (.name _ _ (.item 1)), .ret _ (some (.call _ (.name _ _ (.local 0)) [] 0))]
#guard retRef "fn f() -> Nat { return g; }\nfn g(comptime N: Nat) -> Nat { return N; }" ==
  some (.item 1)
#guard retRef "fn f() -> Nat { return g; }\ncomptime fn g() -> Nat { return 1; }" ==
  some (.item 1)
#guard retRef "fn f() -> Nat { return len; }" == some (.fn .len)
#guard fails "fn f() -> Nat { return (M); }\nmodule M() {}" .S003 1 25

/-! Each pass reports its first error by position. -/
#guard fails (fnBody "return a + b;") .S003 2 8
#guard fails "fn f() -> Bool { let x = true; let x = true; return x; }\nconst f: Nat = 1;"
  .S002 1 36
#guard fails "const f: Nat = 1;\nfn f() -> Bool { let x = true; let x = true; return x; }"
  .S002 2 4

/-! The first statement of the body of the first module. -/
def firstStmt (s : String) : Option Resolve.Stmt :=
  match run s with
  | .ok items =>
    match items[0]? with
    | some (Resolve.Item.module _ _ _ _ b) => b.head?
    | _ => none
  | .error _ => none

/-!
A `mem` declares its name as a local after `clock` and the parameters. Its word type and its
depth see only the earlier declarations.
-/
#guard ok (modBody "mem m: [UInt[W]; W + 1];
let x = m;")
#guard match firstStmt (modBody "mem m: [UInt[W]; 4];") with
  | some (.mem _ b (.index _ (.name _ _ (.type .uint)) [.name _ _ (.local 1)]) (.num _ 4)) =>
    b.name.name == "m" && b.id == 2
  | _ => false
#guard fails (modBody "mem m: [T; 4];") .S003 2 9
#guard fails (modBody "mem m: [Bool; n];") .S003 2 15
#guard fails (modBody "mem m: [Bool; m];") .S003 2 15
#guard fails (modBody "wire m: Bool;
mem m: [Bool; 4];") .S002 3 5
#guard fails (modBody "mem m: [Bool; 4];
let m = 1;") .S002 3 5
#guard fails (modBody "mem W: [Bool; 4];") .S002 2 5

/-!
The prelude structs are struct items after the user items, with the `prelude` flag, in the order
of section 5.6. They are built already resolved, so a user `struct Bool`, `type Type`,
`struct String`, or `struct FieldInfo` does not change them. A field type refers to a prelude
struct by its index. The user items keep their indices.
-/
#guard (run "").toOption == some (preludeStructs 0).toArray
#guard preludeCount == 6
#guard (preludeStructs 0).map (·.name.name) ==
  ["ReadResponse", "FieldInfo", "TypeInfo", "VariantInfo", "PortKey", "PortInfo"]
#guard (run "struct Bool { x: UInt[2] }\ntype Type = UInt[3];").toOption.map (·.extract 2) ==
  some (preludeStructs 2).toArray
#guard (run "struct String {}\nstruct FieldInfo {}\nstruct List {}").toOption.map (·.extract 3) ==
  some (preludeStructs 3).toArray
#guard responseIndex (2 + preludeCount) == 2
/-! `preludeTypeNames` is the list of the prelude types, then of the prelude structs. -/
#guard preludeTypeNames ==
  prelude.filterMap (fun | (x, .type _) => some x | _ => none) ++
    (preludeStructs 0).map (·.name.name)
def listOf (x : String) (k : Nat) : Resolve.TypeExpr :=
  .index ⟨0, 0⟩ (.name ⟨0, 0⟩ "List" (.type .list)) [.name ⟨0, 0⟩ x (.item k)]
#guard match ((preludeStructs 2)[2]? : Option Resolve.Item) with
  | some (.struct _ x [] [_, f, _, _, _, v] true) =>
    x.name == "TypeInfo" && f.ty == listOf "FieldInfo" 3 && v.ty == listOf "VariantInfo" 5
  | _ => false
#guard match ((preludeStructs 2)[5]? : Option Resolve.Item) with
  | some (.struct _ x [] [k, _, _, d] true) =>
    x.name == "PortInfo" && k.ty == .name ⟨0, 0⟩ "PortKey" (.item 6) &&
      d.ty == .name ⟨0, 0⟩ "String" (.type .string)
  | _ => false
#guard match (run "struct Bool { x: UInt[2] }\ntype Type = UInt[3];").toOption with
  | some #[.struct _ _ [] _ false, .alias .., .struct _ x [q] [d, v] true, _, _, _, _, _] =>
    x.name == "ReadResponse" && q.mode == .comptime && q.name.id == 0 &&
      q.ty == .name ⟨0, 0⟩ "Type" (.type .type) &&
      d.ty == .name ⟨0, 0⟩ "T" (.local 0) && v.ty == .name ⟨0, 0⟩ "Bool" (.type .bool)
  | _ => false

/-! The prelude name `ReadResponse` refers to the item after the user items. A user item shadows
it. -/
#guard retRef "fn f() -> Type { return ReadResponse; }" == some (.item 1)
#guard retRef "fn f() -> Type { return ReadResponse; }\nstruct A {}" == some (.item 2)
#guard retRef "fn f() -> Type { return ReadResponse; }\nstruct ReadResponse {}" == some (.item 1)
#guard ok (fnBody "let r: ReadResponse[Bool] = ReadResponse[Bool](p, p);\nreturn r.valid;")
#guard fails (fnBody "return p.ReadResponse();") .S003 2 10

/-!
`read_port` and `write_port` are prelude functions without a `comptime` or `mut` parameter, so
the receiver binds to the first parameter. A user function with the name shadows them, also in
the receiver form.
-/
#guard retRef "fn f() -> Bool { return read_port; }" == some (.fn .readPort)
#guard retRef "fn f() -> Bool { return write_port; }" == some (.fn .writePort)
#guard retRef "fn f() -> Bool { return read_port; }\ncomptime fn read_port() -> Bool {}" ==
  some (.item 1)
#guard match users "fn f(x: Nat) -> Nat { return x.write_port(1, 2, 3); }" with
  | some #[.fn _ _ _ _ _ [.ret _ (some (.method _ _ _ (.fn .writePort) (some 0) _ _))]] =>
    true
  | _ => false
#guard match users ("fn f(x: Nat) -> Nat { return x.write_port(); }\n" ++
    "fn write_port(a: Nat) -> Nat { return a; }") with
  | some #[.fn _ _ _ _ _ [.ret _ (some (.method _ _ _ (.item 1) (some 0) _ _))], _] => true
  | _ => false

/-! `diagnostic` is a prelude function of slice 2, and a user function with the name shadows it. -/
#guard retRef "fn f() -> Bool { return diagnostic; }" == some (.fn .diagnostic)
#guard retRef "fn f() -> Bool { return diagnostic; }\nfn diagnostic() -> Bool {}" ==
  some (.item 1)

/-!
Enums (slice 3, section 5.6). An enum item is a type name and a name in an expression. A variant
path resolves its first part by the ordinary scoping to an enum item, and its second part to a
variant. `E::V` and `E::V(args)` are one `variant` node with the item and the variant index.
-/
def ops : String := "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n"

#guard ok (ops ++ "fn f(x: UInt[8]) -> Op { let a: Op = Op::Add; return Op::Load(x); }")
#guard ok "fn f() -> UInt[1] { return E::A; }\nenum E: UInt[1] { A = 0 }"
#guard ok "enum E: UInt[1] {}"
#guard retRef ("fn f() -> Bool { return Op; }\n" ++ ops) == some (.item 1)
#guard match users (ops ++ "fn f(x: UInt[8]) -> Op { return Op::Load(x); }") with
  | some #[_, .fn _ _ _ _ _ [.ret _ (some (.variant _ _ _ 0 1 [.name _ _ (.local 0)] true))]] =>
    true
  | _ => false
#guard match users (ops ++ "fn f() -> Op { return Op::Add; }") with
  | some #[_, .fn _ _ _ _ _ [.ret _ (some (.variant _ _ _ 0 0 [] false))]] => true
  | _ => false

/-! A call of a path keeps its call site, so a later call gets the next site. -/
#guard match users (ops ++ "fn f(x: UInt[8]) -> Op { return g(Op::Load(g(x))); }\n" ++
    "fn g(x: UInt[8]) -> UInt[8] { return x; }") with
  | some #[_, .fn _ _ _ _ _ [.ret _ (some (.call _ _ [.variant _ _ _ _ _ [.call _ _ _ 2] _] 0))],
      _] => true
  | _ => false

/-! `S002`: a second variant with one name in one enum, at its name. -/
#guard fails "enum E: UInt[1] { A = 0, B = 1, A = 1 }" .S002 1 33
#guard message "enum E: UInt[1] { A = 0, A = 1 }" ==
  "the variant `A` is already declared in this enum; rename one of the two variants"
#guard ok "enum E: UInt[1] { A = 0 }\nenum F: UInt[1] { A = 0 }"
#guard fails (ops ++ "fn Op() -> Bool {}") .S002 2 4

/-! `S003`: a second part that names no variant, at the second part. -/
#guard fails (ops ++ "fn f() -> Op { return Op::Mul; }") .S003 2 27
#guard message (ops ++ "fn f() -> Op { return Op::Mul; }") ==
  "`Op` has no variant `Mul`; use a variant that `Op` declares"

/-!
`S003`: a first part that is not an enum item, at the start of the path, with the text of
section 6.2. This holds for a struct, a function, a module, a prelude name, and a name with no
declaration. A `type` alias of an enum is not an enum item (U2).
-/
#guard message (ops ++ "fn f() -> Op { return std::x; }") ==
  "`std` is not an enum, so `std::x` names no variant; use the name of an enum"
#guard fails (ops ++ "fn f() -> Op { return std::x; }") .S003 2 23
#guard fails "struct S { a: Bool }\nfn f() -> S { return S::a; }" .S003 2 22
#guard fails "fn f() -> Bool { return f::a; }" .S003 1 25
#guard fails "module M() {}\nfn f() -> Bool { return M::a; }" .S003 2 25
#guard fails "fn f() -> Bool { return Bool::A; }" .S003 1 25
#guard fails (ops ++ "type A = Op;\nfn f() -> Op { return A::Add; }") .S003 3 23
#guard message (ops ++ "type A = Op;\nfn f() -> Op { return A::Add; }") ==
  "`A` is not an enum, so `A::Add` names no variant; use the name of an enum"

/-!
`S003`: a local or a parameter shadows an enum item by the ordinary scoping (U1). After the
scope of the local ends, the path names the enum again.
-/
#guard fails (ops ++ "fn f(Op: Nat) -> Nat { return Op::Add; }") .S003 2 31
#guard message (ops ++ "fn f(Op: Nat) -> Nat { return Op::Add; }") ==
  "`Op` is not an enum, so `Op::Add` names no variant; use the name of an enum"
#guard fails (ops ++ "fn f() -> Op { let Op = 1; return Op::Add; }") .S003 2 35
#guard ok (ops ++ "fn f() -> Op { { let Op = 1; } return Op::Add; }")

/-! The tag type, the payload types, and the tag values resolve in the item scope. -/
#guard fails "enum E: T { A = 0 }" .S003 1 9
#guard fails "enum E: UInt[1] { A(Q) = 0 }" .S003 1 21
#guard fails "enum E: UInt[1] { A = N }" .S003 1 23
#guard ok "const N: Nat = 1;\nstruct S { a: Bool }\nenum E: UInt[N] { A(S, E) = N }"

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

/-!
A `match` (slice 3, section 5.6) resolves its scrutinee, then each arm. The path of a variant
pattern resolves as a variant path in an expression. The binders of a pattern are locals in a new
scope that holds only the value of their arm. `arms s` puts the arms `s` on line 3, from
column 20.
-/
def pair : String := "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n"
def arms (s : String) : String :=
  pair ++ "fn f(x: Op, p: UInt[8]) -> UInt[8] {\nreturn match (x) { " ++ s ++ " };\n}"

/-! The arms of the `match` in the `return` of `f`. -/
def matchArms (s : String) : Option (List Resolve.Arm) :=
  match run s with
  | .ok items =>
    match items[1]? with
    | some (Resolve.Item.fn _ _ _ _ _ [.ret _ (some (.«match» _ _ as))]) => some as
    | _ => none
  | .error _ => none

#guard ok (arms "Op::Add => p, Op::Load(v) => v, Op::Pair(_, w) => p, -1 => 0, true => 0, _ => 0")
#guard ok (arms "Op::Pair(_, _) => p, Op::Add() => p, _ => 0")
#guard ok (arms "Op::Load(v) => v, Op::Pair(_, v) => p, _ => 0")

/-! A variant pattern holds its enum item, its variant, and a binder or `_` for each place. -/
#guard match matchArms (arms "Op::Pair(_, w) => w, _ => 0") with
  | some [.mk (.variant _ _ _ 0 2 [none, some ⟨_, 2⟩]) (.name _ _ (.local 2)), .mk (.wild _) _] =>
    true
  | _ => false

/-! A binder shadows a parameter, and its scope ends with its arm. -/
#guard match matchArms (arms "Op::Load(p) => p, _ => p") with
  | some [.mk _ (.name _ _ (.local 2)), .mk _ (.name _ _ (.local 1))] => true
  | _ => false
#guard fails (arms "Op::Load(v) => v, _ => v") .S003 3 43
#guard fails (pair ++ "fn f(x: Op) -> UInt[8] {\n" ++
  "let a = match (x) { Op::Load(v) => v, _ => 0 };\nreturn v;\n}") .S003 4 8

/-! A nested `match` opens its own scopes. An inner binder shadows an outer binder. -/
#guard ok (arms "Op::Load(v) => match (x) { Op::Load(v) => v, _ => v }, _ => 0")

/-! The path resolves before the binders, so a binder can have the name of the enum. -/
#guard ok (arms "Op::Load(Op) => Op, Op::Add => p, _ => 0")

/-! `S002`: two binders with one name in one pattern, at the second binder. -/
#guard fails (arms "Op::Pair(a, a) => p, _ => 0") .S002 3 32
#guard message (arms "Op::Pair(a, a) => p, _ => 0") == "`a` is already declared in this scope"

/-! `S003` of a pattern path, with the texts of a variant path in an expression. -/
#guard fails (arms "Op::Mul => p, _ => 0") .S003 3 24
#guard message (arms "Op::Mul => p, _ => 0") ==
  "`Op` has no variant `Mul`; use a variant that `Op` declares"
#guard fails (arms "p::Add => 0, _ => 0") .S003 3 20
#guard message (arms "p::Add => 0, _ => 0") ==
  "`p` is not an enum, so `p::Add` names no variant; use the name of an enum"
#guard fails (pair ++ "fn f(x: Op) -> UInt[8] {\nlet Op = 1;\n" ++
  "return match (x) { Op::Add => 0 };\n}")
  .S003 4 20
#guard fails (arms "_ => q") .S003 3 25
#guard fails (pair ++ "fn f(x: Op) -> UInt[8] {\nreturn match (q) { _ => 0 };\n}") .S003 3 15

/-! Pass 2 comes before pass 3 in a `match` too. -/
#guard fails (arms "Op::Mul => q, Op::Pair(a, a) => 0") .S002 3 46

/-!
A binder in a signature is no parameter, so it does not make a function generic. A parameter in
the same position does.
-/
def genericFn (s : String) : Option Bool :=
  match run s with
  | .ok items =>
    match items[1]? with
    | some (Resolve.Item.fn _ _ _ ps r _) => some (generic ps r)
    | _ => none
  | .error _ => none

#guard genericFn (pair ++ "fn g(y: UInt[match (Op::Load(8)) { Op::Load(v) => v, _ => 1 }]) " ++
  "-> Bool { return true; }") == some false
#guard genericFn (pair ++ "fn g(n: Nat, y: UInt[match (n) { _ => n }]) -> Bool { return true; }") ==
  some true

/-!
Port families (section 5.6). The first indexed declaration of a name gives one family binder in
the scope of the body. A loop declares the entries, and a later loop selects them (F35). The
implicit `clock` is the local 0 and `W` the local 1, so the family takes the local 2 before the
loop value `i`.
-/
def familyLoops : String :=
  modBody ("comptime for i in 0..2 {\ninput req[i]: Bool;\n}\noutput o: Bool;\n" ++
    "comptime for j in 0..2 {\no := req[j];\n}")

#guard match users familyLoops with
  | some #[.module _ _ _ _
      [.ctFor _ ⟨_, 3⟩ _ _ [.input _ ⟨_, 2⟩ (.indexed (.name _ _ (.local 3))) _],
      .output _ ⟨_, 4⟩ .scalar _,
      .ctFor _ ⟨_, 5⟩ _ _ [.connect _ _ (.index _ (.name _ _ (.family 2 true)) _)]]] => true
  | _ => false

/-! Each indexed declaration of a name, at each depth, takes the one family binder. -/
#guard match users (modBody "output g[0]: Bool;\n{\noutput g[1]: Bool;\n}\noutput g[2]: Bool;") with
  | some #[.module _ _ _ _ [.output _ ⟨_, 2⟩ _ _, .block _ [.output _ ⟨_, 2⟩ _ _],
      .output _ ⟨_, 2⟩ _ _]] => true
  | _ => false

/-! A use before the first declaration resolves. Its key is `S013` at run time. -/
#guard match users (modBody "output o: Bool;\no := req[0];\ninput req[0]: Bool;") with
  | some #[.module _ _ _ _ [_, .connect _ _ (.index _ (.name _ _ (.family 2 true)) _), _]] => true
  | _ => false

/-! Two entries of one family in one block are no second declaration. -/
#guard ok (modBody "input req[0]: Bool;\ninput req[1]: Bool;")

/-! A `let` in a nested block without an indexed declaration of the name shadows the family. -/
#guard match users (modBody "input req[0]: Bool;\n{\nlet req = 1;\nlet y = req;\n}") with
  | some #[.module _ _ _ _ [_, .block _ [_, .local _ _ _ _ (.name _ _ (.local 3))]]] => true
  | _ => false

/-!
In a `comptime fn`, an indexed port declares a local at its statement, and `Check` reports it
(`S006`).
-/
#guard match users "comptime fn f(p: Bool) -> Bool {\ninput req[0]: Bool;\nreturn p;\n}" with
  | some #[.fn _ _ _ _ _ [.input _ ⟨_, 1⟩ (.indexed _) _, _]] => true
  | _ => false

/-! `S002` "Family and scalar port", at the later name, at any depth, in each order. -/
#guard fails (modBody "input req: Bool;\n{\ninput req[0]: Bool;\n}") .S002 4 7
#guard message (modBody "input req: Bool;\n{\ninput req[0]: Bool;\n}") ==
  "`req` names a port family and a scalar port, here and at 2:7; use one form for the name"
#guard fails (modBody "{\ninput req[0]: Bool;\n}\noutput req: Bool;") .S002 5 8
#guard message (modBody "{\ninput req[0]: Bool;\n}\noutput req: Bool;") ==
  "`req` names a port family and a scalar port, here and at 3:7; use one form for the name"
#guard fails (modBody "comptime if (true) {\ninput req: Bool;\n}\noutput req[0]: Bool;") .S002 5 8

/-! `S002` "Family with two directions", at the first entry of the second direction. -/
#guard fails (modBody "input req[0]: Bool;\ncomptime if (true) {\noutput req[1]: Bool;\n}")
  .S002 4 8
#guard message (modBody "input req[0]: Bool;\ncomptime if (true) {\noutput req[1]: Bool;\n}") ==
  "the port family `req` has an input entry and an output entry, here and at 2:7; give the " ++
    "entries of one direction another name"

/-! A family and another name of the body scope: the ordinary `S002` at the later name. -/
#guard fails "module M(comptime req: Nat) {\ninput req[0]: Bool;\n}" .S002 2 7
#guard message "module M(comptime req: Nat) {\ninput req[0]: Bool;\n}" ==
  "`req` is already declared in this scope"
#guard fails (modBody "let req = 1;\n{\ninput req[0]: Bool;\n}") .S002 4 7
#guard fails (modBody "{\ninput req[0]: Bool;\n}\nlet req = 1;") .S002 5 5
#guard fails (modBody "let req = 1;\ninput req[0]: Bool;") .S002 3 7

/-!
An indexed declaration declares its name in its own block too, so another declaration of the
name in that block is `S002` in each order. The loop value and the loop body share one scope.
-/
#guard fails (modBody "{\nlet req = 1;\ninput req[0]: Bool;\n}") .S002 4 7
#guard message (modBody "{\nlet req = 1;\ninput req[0]: Bool;\n}") ==
  "`req` is already declared in this scope"
#guard fails (modBody "{\ninput req[0]: Bool;\nlet req = 1;\n}") .S002 4 5
#guard message (modBody "{\ninput req[0]: Bool;\nlet req = 1;\n}") ==
  "`req` is already declared in this scope"
#guard fails (modBody "comptime for req in 0..2 {\ninput req[req]: Bool;\n}") .S002 3 7

/-!
The walk also runs on the body of a `fn` without `comptime` (section 5.6). A family of a helper
has the scope of the helper body: a loop declares the entries, and a later statement selects one.
The parameter `p` is the local 0, so the family takes the local 1 before the loop value.
-/
#guard match users (fnBody "comptime for i in 0..2 {\ninput req[i]: Bool;\n}\nreturn req[0];") with
  | some #[.fn _ false _ _ _ [.ctFor _ ⟨_, 2⟩ _ _ [.input _ ⟨_, 1⟩ (.indexed _) _],
      .ret _ (some (.index _ (.name _ _ (.family 1 true)) _))]] => true
  | _ => false

/-! A use before the first declaration resolves in a helper too. -/
#guard match users (fnBody "let x = req[0];\ninput req[0]: Bool;\nreturn p;") with
  | some #[.fn _ _ _ _ _ [.local _ _ _ _ (.index _ (.name _ _ (.family 1 true)) _), _, _]] => true
  | _ => false

/-! A helper body has the collisions of a module body, at the later name. -/
#guard fails (fnBody "input req: Bool;\n{\ninput req[0]: Bool;\n}\nreturn p;") .S002 4 7
#guard message (fnBody "input req: Bool;\n{\ninput req[0]: Bool;\n}\nreturn p;") ==
  "`req` names a port family and a scalar port, here and at 2:7; use one form for the name"
#guard fails (fnBody "input req[0]: Bool;\noutput req[1]: Bool;\nreturn p;") .S002 3 8
#guard fails (fnBody "let req = 1;\ninput req[0]: Bool;\nreturn p;") .S002 3 7
#guard fails "fn f(req: Bool) -> Bool {\ninput req[0]: Bool;\nreturn req;\n}" .S002 2 7

/-!
The module body cannot select a family that only a helper declares. There, the name has no
declaration, so it is `S003`.
-/
#guard fails ("fn lane() -> Nat {\ninput req[0]: Bool;\nreturn 0;\n}\n" ++
  "module M() {\nlet x = lane();\nlet y = req[0];\n}") .S003 7 9

/-!
A port with an `as` key is no port name of the walk. Its binder is a name of the body only, so a
family with the name of the binder is the ordinary `S002`.
-/
#guard fails (modBody "input req: Bool as \"x\";\ninput req[0]: Bool;") .S002 3 7
#guard message (modBody "input req: Bool as \"x\";\ninput req[0]: Bool;") ==
  "`req` is already declared in this scope"
#guard fails (fnBody "input req[0]: Bool;\noutput req: Bool as \"x\";\nreturn p;") .S002 3 8

/-! The operands of a builtin resolve as expressions: an unknown name in one is `S003`. -/
#guard ok (fnBody "let x = 1;\nlet t = @TypeOf(x);\nlet y = @field(x, \"a\");\nreturn p;")
#guard fails (fnBody "let t = @TypeOf(q);\nreturn p;") .S003 2 17
#guard fails (fnBody "let y = @field(p, k);\nreturn p;") .S003 2 19
#guard match run "fn f(x: Nat) -> Nat { return @field(x, 0); }" with
  | .ok items => match items[0]? with
    | some (Resolve.Item.fn _ _ _ _ _
        [.ret _ (some (.atField _ (.name _ "x" (.local _)) (.num _ 0)))]) => true
    | _ => false
  | .error _ => false

end Silicon.Source.Test.Resolve
