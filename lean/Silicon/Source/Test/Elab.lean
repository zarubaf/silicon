-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli

/-!
These tests check the instantiations of `Source.Elab`: the table of instantiations, the depth
first order, and the charges of `instance` statements. They run the budget files of section 11.3
that slice 1 can run. They check each check for each instantiation at its position, and the core
names of section 7.3.
-/

namespace Silicon.Source.Test.Elab

open Silicon.Source

/-! A test digest function that maps each serialization to one digest. -/
def collide (_ : String) : String := "0000000000000000"

/-! The result of `cost`: its output, or the code and the position of the first error. -/
def cost (src t : String) (fuel : Nat := 100000000) (depth : Nat := 1000)
    (digest : String → String := Names.sha16) : String :=
  match Cli.costText { budget := { fuel, depth } } src t digest with
  | .ok text => text
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .reject line => line
  | .usage _ => "usage"
  | .defect _ => "defect"

/-!
The elaboration of `src` with the top selection `t`, without the lowering: the design and its
units, or the code and the position of the first error.
-/
def elaborated (src t : String) : Except String (Elab.Design × Nat) :=
  match Cli.load 4096 src with
  | .error e => .error s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked t with
    | .error _ => .error "usage"
    | .ok (p, i, _, xs) =>
      match Elab.elaborate {} checked Names.sha16 p i xs with
      | .ok r => .ok r
      | .error e => .error s!"{e.code} {e.pos.line}:{e.pos.col}"

/-! The elaborated design of `src` with the top selection `t`. -/
def design (src t : String) : Option Elab.Design := (elaborated src t).toOption.map (·.1)

/-! The total fuel of `cost`. -/
def total (src t : String) : Nat :=
  match design src t with
  | some _ =>
    match Cli.costText {} src t with
    | .ok text => ((text.splitOn "\n").head!.drop 6).toString.toNat!
    | _ => 0
  | none => 0

/-! The cost is `units`. This fuel passes, and one unit less gives `S015`. -/
def exact (src t : String) (units : Nat) : Bool :=
  total src t == units && (cost src t units).startsWith "total" &&
    (cost src t (units - 1)).startsWith "S015"

/-! The emitted names in the order in which the instantiations finish. -/
def order (src t : String) : List String :=
  ((design src t).map fun d => d.insts.toList.map (Names.encode ·.iface.name)).getD []

/-! The core names of the named bindings, the registers, the wires, and the children of `m`. -/
def names (src t m : String) : List String :=
  match design src t with
  | some d =>
    match d.insts.find? (Names.encode ·.iface.name == m) with
    | some i =>
      let enc (p : Names.Path) := Names.encode p.name
      i.body.lets.toList.map (enc ·.path) ++ i.body.regs.toList.map (enc ·.path) ++
        i.body.wires.toList.map (enc ·.path) ++ i.body.children.toList.map (enc ·.path)
    | none => []
  | none => []

/-! The counter of the v0.1 README, with a parent. -/
def counter : String :=
  "module Counter(comptime W: Nat) {\n" ++
  "    input enable: Bool;\n" ++
  "    output value: UInt[W];\n" ++
  "    output full: Bool;\n" ++
  "    reg count: UInt[W] = 0;\n" ++
  "    count := if (enable) { count +% 1 } else { count };\n" ++
  "    value := count;\n" ++
  "    full := count == UInt[W]((1 << W) - 1);\n" ++
  "}\n" ++
  "module Main() {\n" ++
  "    input enable: Bool;\n" ++
  "    output value: UInt[4];\n" ++
  "    instance counter = Counter(4);\n" ++
  "    counter.enable := enable;\n" ++
  "    value := counter.value;\n" ++
  "}\n"

#guard cost counter "Main" == "total 427\nCounter$4 194\nMain 196\n"
#guard exact counter "Main" 427
#guard cost counter "Counter(8)" == "total 254\nCounter$8 194\n"
#guard order counter "Main" == ["Counter$4", "Main"]

/-!
The table of instantiations. A child finishes before its parent. A repeated `InstantiationId`
elaborates once. Its `instance` statement charges 1, and its argument charges 2 for the node and
the literal, and 1 for the recursive size. Its serialization charges 1 for the decimal form and
32 for its bytes. Its lowering charges 44. The `inst` node and its name charge 2, and the
emitted name 2. Each of the two domain connections charges 20. These are 81 units.
-/
def leaf : String := "module C(comptime n: Nat) {\n}\n"
def one : String := leaf ++ "module T() {\n  instance a = C(5);\n}\n"
def two : String := leaf ++ "module T() {\n  instance a = C(5);\n  instance b = C(5);\n}\n"
def other : String := leaf ++ "module T() {\n  instance a = C(5);\n  instance b = C(6);\n}\n"

#guard total two "T" == total one "T" + 81
#guard order two "T" == ["C$5", "T"]
#guard order other "T" == ["C$5", "C$6", "T"]
#guard cost other "T" == s!"total {total other "T"}\nC$5 25\nC$6 25\nT 191\n"

/-! An instantiation that depends on itself is `S019` at its `instance` statement. -/
def selfDep : String := "module M(comptime d: Nat) {\n  instance a = M(d);\n}\n"
def loop : String :=
  "module A(comptime d: Nat) {\n  instance b = B(d);\n}\n" ++
  "module B(comptime d: Nat) {\n  instance a = A(d);\n}\n"
#guard cost selfDep "M(3)" == "S019 2:3"
#guard cost loop "A(1)" == "S019 5:3"

/-!
Two identities that share an emitted name are `S019` at the `instance` statement of the second.
A test digest function makes all digests equal, as section 7.1 plan item 4 states.
-/
def digests : String :=
  "module M(comptime x: UInt[8]) {\n}\n" ++
  "module T() {\n  instance a = M(UInt[8](1));\n  instance b = M(UInt[8](2));\n}\n"
#guard (cost digests "T").startsWith "total"
#guard cost digests "T" (digest := collide) == "S019 5:3"
#guard order digests "T" ==
  ["M$0h" ++ Names.sha16 "(instantiation root M ((uint 8 1)))",
   "M$0h" ++ Names.sha16 "(instantiation root M ((uint 8 2)))", "T"]

/-!
An emitted name is taken when its instantiation starts. A descendant that shares the emitted name
of an active ancestor is thus `S019` at its own `instance` statement.
-/
def nested : String :=
  "module M(comptime x: UInt[8]) {\n" ++
  "  comptime if (x == UInt[8](1)) { instance a = M(UInt[8](0)); }\n}\n" ++
  "module T() {\n  instance b = M(UInt[8](1));\n}\n"
#guard (cost nested "T").startsWith "total"
#guard cost nested "T" (digest := collide) == "S019 2:35"

/-!
A serialization charges its length in bytes, and an emitted name too. A module with a long name
thus pays for each new instantiation, and 1000 of them fail with `S015` under a small fuel. A
short name passes with the same fuel.
-/
def longName (n : String) : String :=
  s!"module {n}(comptime i: Int) \{\n}\nmodule T() \{\n  comptime for i in 0..1000 \{\n" ++
  s!"    instance u = {n}(i);\n  }\n}\n"
#guard cost (longName (String.ofList (List.replicate 100000 'a'))) "T" (fuel := 1000000) ==
  "S015 5:5"
#guard (cost (longName "L") "T" (fuel := 1000000)).startsWith "total"

/-!
The decimal form of an integer in a serialization charges the square of its size. The argument
`1 << 1000000` has the size 15626, so its serialization fails with `S015` before it runs.
-/
def bigArg : String :=
  "module M(comptime x: Int) {\n}\nmodule T() {\n  instance u = M(1 << 1000000);\n}\n"
#guard cost bigArg "T" (fuel := 10000000) == "S015 4:3"

/-!
A child with a free input is `S018` at its `instance` statement. The counts select the first
such child, so a module with 8000 inputs and 8000 children without bindings returns fast.
-/
def wide (n : Nat) : String :=
  "module W() {\n" ++ String.join ((List.range n).map fun j => s!"  input i{j}: Bool;\n") ++
  s!"}\nmodule T() \{\n  comptime for k in 0..{n} \{\n    instance u = W();\n  }\n}\n"
#guard cost (wide 8000) "T" (fuel := 1000000) == "S018 8005:5"

/-! The branching hierarchy of section 11.3 with `d = 10`: 2047 instantiations. -/
def branch : String :=
  "module M(comptime d: Nat, comptime id: Nat) {\n" ++
  "  output o: Bool;\n" ++
  "  comptime if (d == 0) { o := true; } else {\n" ++
  "    instance a = M(d - 1, 2 * id);\n" ++
  "    instance b = M(d - 1, 2 * id + 1);\n" ++
  "    o := a.o && b.o;\n" ++
  "  }\n" ++
  "}\n"
#guard (order branch "M(10, 0)").length == 2047
#guard exact branch "M(10, 0)" (total branch "M(10, 0)")
#guard total branch "M(10, 0)" > 0

/-! The shared hierarchy of section 11.3 with `d = 30`: 31 instantiations, linear in `d`. -/
def shared : String :=
  "module M(comptime d: Nat) {\n" ++
  "  output o: Bool;\n" ++
  "  comptime if (d == 0) { o := true; } else {\n" ++
  "    instance a = M(d - 1);\n" ++
  "    instance b = M(d - 1);\n" ++
  "    o := a.o && b.o;\n" ++
  "  }\n" ++
  "}\n"
#guard (order shared "M(30)").length == 31
#guard exact shared "M(30)" (total shared "M(30)")
#guard total shared "M(30)" - total shared "M(29)" == total shared "M(20)" - total shared "M(19)"

/-!
A deep child first and a shallow child later, and the reverse order. The top and the chain
`Chain(5)` to `Chain(0)` nest 7 levels. In the reverse order, `Chain(3)` nests 5 levels first.
Then `Chain(5)` and `Chain(4)` nest 3 levels, and `Chain(3)` is done.
-/
def chain : String :=
  "module Chain(comptime d: Nat) {\n" ++
  "  comptime if (d > 0) { instance c = Chain(d - 1); }\n" ++
  "}\n"
def deepFirst : String := chain ++
  "module Top() {\n  instance a = Chain(5);\n  instance b = Chain(3);\n}\n"
def shallowFirst : String := chain ++
  "module Top() {\n  instance a = Chain(3);\n  instance b = Chain(5);\n}\n"
#guard (cost deepFirst "Top" (depth := 7)).startsWith "total"
#guard cost deepFirst "Top" (depth := 6) == "S015 2:25"
#guard (cost shallowFirst "Top" (depth := 5)).startsWith "total"
#guard cost shallowFirst "Top" (depth := 4) == "S015 2:25"
#guard total deepFirst "Top" == total shallowFirst "Top"

/-! The core names of section 7.3: loop frames, call frames, versions, and the result role. -/
def helpers : String :=
  "fn add(comptime W: Nat, a: UInt[W], b: UInt[W]) -> UInt[W] {\n" ++
  "  let t = a +% b;\n" ++
  "  return t;\n" ++
  "}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n" ++
  "  output y: UInt[8];\n" ++
  "  let s = add(8, x, 1);\n" ++
  "  comptime for i in 0..2 {\n" ++
  "    let z = add(8, s, i);\n" ++
  "    reg r: Bool = false;\n" ++
  "    r := true;\n" ++
  "  }\n" ++
  "  { let s = x; }\n" ++
  "  let mut q = x;\n" ++
  "  q = q +% 1;\n" ++
  "  instance u = Leaf();\n" ++
  "  y := s;\n" ++
  "}\n" ++
  "module Leaf() {\n}\n"
#guard names helpers "M" "M" ==
  ["add$0c$a", "add$0c$t", "add$0c$0ret", "s", "i$0$add$1c$a", "i$0$add$1c$t",
   "i$0$add$1c$0ret", "i$0$z", "i$1$add$1c$a", "i$1$add$1c$t", "i$1$add$1c$0ret", "i$1$z",
   "s$1v", "q", "q$1v", "i$0$r", "i$1$r", "u"]

/-!
A call result never gets a version (section 7.3). A loop and a recursion add frames. Each
result name thus ends with `0ret`, and no two names are equal.
-/
def results : String :=
  "fn g(comptime n: Nat, a: UInt[8]) -> UInt[8] {\n" ++
  "  comptime if (n == 0) {\n" ++
  "    return a +% 1;\n" ++
  "  }\n" ++
  "  let b = g(n - 1, a);\n" ++
  "  return b +% 1;\n" ++
  "}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n" ++
  "  output y: UInt[8];\n" ++
  "  let mut s = g(0, x);\n" ++
  "  comptime for i in 0..2 {\n" ++
  "    s = g(2, s);\n" ++
  "  }\n" ++
  "  y := s;\n" ++
  "}\n"
def retNames : List Names.Name :=
  ((names results "M" "M").filterMap Names.decode).filter (·.rest.contains (.role .ret))
#guard retNames.length == 7
#guard retNames.all (·.rest.getLast? == some (.role .ret))
#guard retNames.all fun p => !p.rest.any fun | .version _ => true | _ => false
#guard (names results "M" "M").eraseDups.length == (names results "M" "M").length
#guard (names results "M" "M").contains "i$1$g$1c$g$0c$g$0c$0ret"

/-! A static value gets no core name. A user name equal to a core keyword gets `0k`. -/
def keywords : String :=
  "module next() {\n" ++
  "  input add: Bool;\n" ++
  "  output bits: Bool;\n" ++
  "  let design = add;\n" ++
  "  let k = 5;\n" ++
  "  wire inst: Bool;\n" ++
  "  inst := design;\n" ++
  "  bits := inst;\n" ++
  "}\n"
#guard names keywords "next" "next$0k" == ["design$0k", "inst$0k"]

/-!
Each hardware operator of slice 1, a hardware `if` with static arms, a hardware shift count, the
conversions, and a child input through a handle alias. A hardware `if` with two equal static
`Int` arms gives the static value (F19), here the static shift count `n`.
-/
def ops : String :=
  "module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := !a;\n}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n  input s: SInt[8];\n  input c: UInt[3];\n  input e: Bool;\n" ++
  "  output y: UInt[8];\n  output z: SInt[16];\n  output b: Bool;\n" ++
  "  let w = (x +% 1) -% (x *% 3) & ~x | (x ^ 255);\n" ++
  "  let v = -s >> c;\n" ++
  "  let n = if (e) { 2 } else { 2 };\n" ++
  "  let k = if (e) { 1 } else { x << n };\n" ++
  "  instance u = C();\n" ++
  "  let h = u.a;\n" ++
  "  h := e && x < 5 || s >= -1 && x != w;\n" ++
  "  y := if (u.q) { k } else { reinterpret(UInt[8], s) };\n" ++
  "  z := resize(SInt[16], v);\n" ++
  "  b := if (e) { true } else { false };\n" ++
  "}\n"
#guard order ops "M" == ["C", "M"]
#guard names ops "M" "M" == ["w", "v", "k", "u"]
#guard exact ops "M" (total ops "M")

/-! Two ports with one name are `S019`, also from a loop and after a binding of the name. -/
#guard cost "module M() {\n  comptime for i in 0..2 {\n    input x: Bool;\n  }\n}\n" "M" ==
  "S019 3:5"
#guard cost "module M() {\n  input y: Bool;\n  let x = y;\n  { input x: Bool; }\n}\n" "M" ==
  "S019 4:5"

/-! `S010`: a port type is hardware data, operands have one type, and a binding has its type. -/
#guard cost "module M() {\n  input x: Nat;\n}\n" "M" == "S010 2:3"
#guard cost ("module M() {\n  input x: UInt[8];\n  input z: UInt[4];\n  output y: UInt[8];\n" ++
  "  y := x +% z;\n}\n") "M" == "S010 5:8"
#guard cost "module M() {\n  output y: UInt[8];\n  y := true;\n}\n" "M" == "S010 3:3"
#guard cost "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n  y := x + 1;\n}\n" "M" ==
  "S010 4:8"
#guard cost "module M() {\n  input x: UInt[8];\n  output y: Bool;\n  y := x && true;\n}\n" "M" ==
  "S010 4:8"

/-!
`S011`: a static position gets a static value. The pre-check already rejects a port name in a
static position with `S005`, so these cases use a `let` binding of a port.
-/
#guard cost "module M() {\n  input x: Bool;\n  comptime if (x) { }\n}\n" "M" == "S005 3:16"
#guard cost "module M() {\n  input x: Bool;\n  let a = x;\n  comptime if (a) { }\n}\n" "M" ==
  "S011 4:3"
#guard cost "module M() {\n  input x: Bool;\n  let a = x;\n  reg r: Bool = a;\n  r := a;\n}\n"
  "M" == "S011 4:3"
#guard cost ("comptime fn f(b: Bool) -> Bool { return b; }\n" ++
  "module M() {\n  input x: Bool;\n  output y: Bool;\n  let a = x;\n  y := f(a);\n}\n") "M" ==
  "S011 6:8"

/-! `S012`: a value fits its type. `S013`: a negative shift count. `S014`: an assertion. -/
#guard cost "module M() {\n  reg r: UInt[4] = 16;\n  r := r;\n}\n" "M" == "S012 2:3"
#guard cost "module M() {\n  output y: UInt[8];\n  y := 300;\n}\n" "M" == "S012 3:3"
#guard cost "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n  y := x << -1;\n}\n" "M" ==
  "S013 4:8"
#guard cost "module M() {\n  static_assert(1 == 2, \"no\");\n}\n" "M" == "S014 2:3"

/-!
A container argument gives the digest form of the emitted name. The serialization holds the
argument as it evaluates. A `[]` argument takes the type of its parameter, also nested.
-/
def container (ty arg : String) : String :=
  s!"module C(comptime xs: {ty}) \{\n}\nmodule T() \{\n  instance a = C({arg});\n}\n"
#guard order (container "[UInt[8]; 2]" "[1, 2]") "T" ==
  ["C$0h" ++ Names.sha16 "(instantiation root C ((array int ((int 1) (int 2)))))", "T"]
#guard order (container "[Bool; 0]" "[]") "T" ==
  ["C$0h" ++ Names.sha16 "(instantiation root C ((array bool ())))", "T"]
#guard order (container "([Bool; 0], Int)" "([], 1)") "T" ==
  ["C$0h" ++ Names.sha16 "(instantiation root C ((tuple ((array bool ()) (int 1)))))", "T"]
#guard cost (container "[Bool; 0]" "[[]]") "T" == "S010 4:3"
#guard (cost ("module C(comptime n: Nat, comptime xs: [[Bool; 0]; n]) {\n}\n" ++
  "module T() {\n  instance a = C(2, [[], []]);\n}\n") "T").startsWith "total"

/-!
The serialization of a container charges 1 for each container node, then its bytes. The parent
pays it. `[[1, 2]]` costs `T` 31 units more than `[1, 2]`. The outer literal charges 1 for its
node and 4 for its size. The copy adds 1, the walk 1, and the serialization 24 bytes.
-/
#guard (cost (container "[UInt[8]; 2]" "[1, 2]") "T").endsWith "\nT 173\n"
#guard (cost (container "[[UInt[8]; 2]; 1]" "[[1, 2]]") "T").endsWith "\nT 204\n"

/-! The nested doubling of section 11.3 in a module: `S015` at the `let` of `a17`. -/
def doubling (k : Nat) : String :=
  "module T() {\n" ++ String.join ((List.range (k + 1)).map fun i =>
    if i == 0 then "  let a0 = [0, 0];\n" else s!"  let a{i} = [a{i - 1}, a{i - 1}];\n") ++ "}\n"
#guard cost (doubling 20) "T" (fuel := 1000000) == "S015 19:13"
#guard (cost (doubling 16) "T" (fuel := 1000000)).startsWith "total"

/-! `S017`: the resource rule. -/
#guard cost "module M() {\n  input x: Bool;\n  x := true;\n}\n" "M" == "S017 3:3"
#guard cost "module M() domains() {\n  reg r: Bool = false;\n}\n" "M" == "S017 2:3"
#guard cost "module M() domains() {\n  wire w: UInt[8];\n  w.0 := 1;\n}\n" "M" == "S017 3:3"
#guard cost "module M() domains() {\n  wire w: UInt[8];\n  w[1 / 0] := 1;\n}\n" "M" ==
  "S017 3:3"
#guard cost ("module C() {\n  input a: Bool;\n}\nmodule M() {\n  instance c = C();\n" ++
  "  c.a[0] := true;\n}\n") "M" == "S017 6:3"
#guard cost ("module C() {\n}\nmodule M() domains() {\n  instance c = C();\n}\n") "M" == "S017 4:3"
#guard cost ("module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\n" ++
  "module M() domains() {\n  output y: Bool;\n  instance c = C();\n  c.a := false;\n" ++
  "  c.q := true;\n  y := c.q;\n}\n") "M" == "S017 10:3"
#guard cost ("module C() domains() {\n  input a: Bool;\n}\n" ++
  "module M() domains() {\n  output y: Bool;\n  instance c = C();\n  c.a := false;\n" ++
  "  y := c.a;\n}\n") "M" == "S017 8:3"

/-!
`S018`: each resource has exactly one binding. The errors wait for the end of the body and
compete by position. A missing binding is at the declaration, and a missing child input is at
the `instance` statement.
-/
#guard cost "module M() {\n  output y: Bool;\n  y := true;\n  y := false;\n}\n" "M" == "S018 4:3"
#guard cost "module M() {\n  wire w: Bool;\n}\n" "M" == "S018 2:3"
#guard cost "module M() {\n  output y: Bool;\n  wire w: Bool;\n  w := y;\n  w := y;\n}\n" "M" ==
  "S018 2:3"
#guard cost ("module C() domains() {\n  input a: Bool;\n}\n" ++
  "module M() domains() {\n  instance c = C();\n}\n") "M" == "S018 5:3"
#guard cost ("module C() domains() {\n  input a: Bool;\n}\n" ++
  "module M() domains() {\n  instance c = C();\n  c.a := true;\n  c.a := false;\n}\n") "M" ==
  "S018 7:3"
#guard cost
  ("module M() {\n  output y: Bool;\n  comptime for i in 0..2 {\n    y := true;\n  }\n}\n") "M" ==
  "S018 4:5"

/-! An error in the body comes before an `S018` of the same body. A child finishes first. -/
#guard cost "module M() {\n  wire w: Bool;\n  output y: UInt[8];\n  y := true;\n}\n" "M" ==
  "S010 4:3"
#guard cost ("module C() {\n  output q: Bool;\n}\n" ++
  "module M() {\n  output y: UInt[8];\n  instance c = C();\n  y := true;\n}\n") "M" ==
  "S018 2:3"

/-!
The `mem` statement (section 6.2). Each check is at the statement. First, the statement charges
1. A combinational module is `S017`, before the type. The word type is `S010` when it is not
hardware data or has no leaf, and `S012` above 65536 bits. Then the depth is `S011`, `S010`, or
`S012` outside 1 to 16777216. A memory without a port call is `S018` at its statement.
-/
def memBody (ss : String) : String := "module M() {\n" ++ ss ++ "}\n"

#guard cost "module M() domains() {\n  mem m: [Int; 0];\n}\n" "M" == "S017 2:3"
#guard cost "module M() domains() {\n  mem m: [Int; 0];\n}\n" "M" (fuel := 28) == "S017 2:3"
#guard cost "module M() domains() {\n  mem m: [Int; 0];\n}\n" "M" (fuel := 27) == "S015 2:3"
#guard cost (memBody "  mem m: [Int; 4];\n") "M" == "S010 2:3"
#guard cost (memBody "  mem m: [(); 4];\n") "M" == "S010 2:3"
#guard cost (memBody "  mem m: [[Unit; 4]; 4];\n") "M" == "S010 2:3"
#guard cost (memBody "  mem m: [[fn () -> Bool; 0]; 4];\n") "M" == "S010 2:3"
#guard cost (memBody "  mem m: [UInt[65536]; 4];\n  mem k: [[UInt[65536]; 2]; 4];\n") "M" ==
  "S012 3:3"
#guard cost (memBody "  mem m: [Bool; 0];\n") "M" == "S012 2:3"
#guard cost (memBody "  mem m: [Bool; 16777217];\n") "M" == "S012 2:3"
#guard cost (memBody "  mem m: [Bool; -1];\n") "M" == "S012 2:3"
#guard cost (memBody "  mem m: [Bool; true];\n") "M" == "S010 2:3"
#guard cost (memBody "  mem m: [Bool; \"a\"];\n") "M" == "S010 2:3"
#guard cost (memBody "  mem m: [Bool; []];\n") "M" == "S010 2:3"
#guard cost (memBody "  input x: UInt[4];\n  let h = x;\n  mem m: [Bool; h];\n") "M" == "S011 4:3"

/-! The word type checks before the depth, and the width before the depth. -/
#guard cost (memBody "  input x: UInt[4];\n  let h = x;\n  mem m: [Int; h];\n") "M" == "S010 4:3"
#guard cost (memBody "  input x: UInt[4];\n  let h = x;\n  mem m: [[UInt[65536]; 2]; h];\n")
  "M" == "S012 4:3"

/-!
The charge: the statement, the type, and the depth, with no `[T; N]` type. A wide word with the
largest depth costs as much as one with the depth 1, and its last charge is at the depth.
-/
#guard cost (memBody "  mem m: [Bool; 4];\n") "M" (fuel := 31) == "S018 2:3"
#guard cost (memBody "  mem m: [Bool; 4];\n") "M" (fuel := 30) == "S015 2:17"
#guard cost (memBody "  mem m: [UInt[65536]; 16777216];\n") "M" (fuel := 36) == "S018 2:3"
#guard cost (memBody "  mem m: [UInt[65536]; 16777216];\n") "M" (fuel := 35) == "S015 2:24"
#guard cost (memBody "  mem m: [UInt[65536]; 1];\n") "M" (fuel := 36) == "S018 2:3"
#guard cost (memBody "  mem m: [UInt[65536]; 1];\n") "M" (fuel := 35) == "S015 2:24"

/-!
A memory is never data: a read, an index, a field, and an operand are `S010` at the use. A `let`
alias keeps the handle, so only its read fails.
-/
#guard cost (memBody "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m;\n") "M" == "S010 4:3"
#guard cost (memBody "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m[0];\n") "M" == "S010 4:8"
#guard cost (memBody "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m.a;\n") "M" == "S010 4:8"
#guard cost (memBody "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m + 1;\n") "M" ==
  "S010 4:8"
#guard cost (memBody "  mem m: [Bool; 4];\n  let a = m;\n  let b: Bool = a;\n") "M" ==
  "S010 4:3"
#guard cost (memBody "  mem m: [Bool; 16777216];\n  let a = m;\n") "M" == "S018 2:3"

/-! `S018` at the statement competes by position with the other bindings, also in a loop. -/
#guard cost (memBody "  mem m: [Bool; 4];\n  wire w: Bool;\n") "M" == "S018 2:3"
#guard cost (memBody "  wire w: Bool;\n  mem m: [Bool; 4];\n") "M" == "S018 2:3"
#guard cost (memBody "  output y: Bool;\n  y := true;\n  mem m: [Bool; 4];\n  y := false;\n")
  "M" == "S018 4:3"
#guard cost (memBody "  comptime for i in 0..2 {\n    mem m: [Bool; 2];\n  }\n") "M" == "S018 3:5"

/-! The elaboration alone: `ok` and its units, or the code and the position of the first error. -/
def elabOnly (src t : String) : String :=
  match elaborated src t with
  | .ok (_, u) => s!"ok {u}"
  | .error e => e

/-! The units of the elaboration alone, or 0 for an error. -/
def elabUnits (src t : String) : Nat := ((elabOnly src t).drop 3).toString.toNat?.getD 0

/-! The description of the top instantiation. -/
def topBody (src t : String) : Option Elab.Body := do
  let d ← design src t
  return (← d.insts[d.top]?).body

/-!
A port, a register, and a wire have a hardware data type (section 5.1). This type can be a
struct type, an array type, or a tuple type. A read of an aggregate gives a reference, and a
field or a static index of it gives a part. A record field can hold a hardware value.
-/
def ps : String := "struct P(comptime W: Nat) { a: UInt[W], b: Bool }\n"
def agg (body : String) : String :=
  ps ++ "module M() {\n  input x: P[8];\n" ++ body ++ "}\n"
#guard (elabOnly (agg "") "M").startsWith "ok"
#guard (elabOnly (agg "  output y: P[8];\n  y := x;\n") "M").startsWith "ok"
#guard (elabOnly (agg "  output y: UInt[8];\n  y := x.a;\n") "M").startsWith "ok"
#guard (elabOnly (agg "  reg r: P[8] = P[8](3, true);\n  r := x;\n") "M").startsWith "ok"
#guard (elabOnly (agg "  reg r: P[8] = P[8]();\n  r := r;\n  output y: Bool;\n  y := r.b;\n") "M")
  |>.startsWith "ok"
#guard (elabOnly (agg ("  wire w: [Bool; 2];\n  w := [x.b, true];\n  output y: Bool;\n" ++
  "  y := w[1];\n")) "M").startsWith "ok"
#guard (elabOnly (agg ("  wire w: (UInt[8], Bool);\n  w := (x.a, x.b);\n  output y: UInt[8];\n" ++
  "  y := w.0;\n")) "M").startsWith "ok"

/-!
The register value is static, and it takes the register type by a typed use. Each leaf of it
gives the reset constant of its leaf in the lowering. A value that does not fit is `S012` at the
statement, and another type is `S010`.
-/
def regInit (ty v : String) : String := s!"module M() \{\n  reg r: {ty} = {v};\n  r := r;\n}\n"
#guard ((topBody (regInit "[UInt[4]; 2]" "[1, 2]") "M").map
  (·.regs.toList.map (·.init.serialize))) == some ["(array (uint 4) ((uint 4 1) (uint 4 2)))"]
#guard elabOnly (regInit "[UInt[4]; 2]" "[1, 16]") "M" == "S012 2:3"
#guard elabOnly (ps ++ regInit "P[8]" "1") "M" == "S010 3:3"
#guard (elabOnly (regInit "[Bool; 0]" "[]") "M").startsWith "ok"
#guard (elabOnly (regInit "([UInt[8]; 0], Bool)" "([], false)") "M").startsWith "ok"
#guard elabOnly (regInit "[Bool; 1]" "[]") "M" == "S010 2:3"

/-!
A `:=` binding of an aggregate is one binding. It holds the aggregate, so the lowering makes the
leaf statements. A static leaf of the value takes its type by the typed use: it converts, and
a value that does not fit is `S012`. Another type is `S010` at the statement.
-/
#guard ((topBody (agg "  output y: P[8];\n  y := x;\n") "M").map fun b =>
  b.binds.toList.map fun d => match d.sink, d.value with
    | .own .output t _, .ref _ u => t.same u
    | _, _ => false) == some [true]
#guard (elabOnly (agg "  output y: (UInt[8], UInt[8]);\n  y := (x.a, 1);\n") "M").startsWith "ok"
#guard elabOnly (agg "  output y: (UInt[8], UInt[8]);\n  y := (x.a, 256);\n") "M" == "S012 5:3"
#guard elabOnly (ps ++ "module M() {\n  input x: P[4];\n  output y: P[8];\n  y := x;\n}\n") "M" ==
  "S010 5:3"
#guard elabOnly (agg "  output y: UInt[8];\n  y := x;\n") "M" == "S010 5:3"

/-!
The value of `:=` is a typed use. A read of an aggregate handle thus copies the handle and the
reference: 1 plus the zero size of the type (section 5.4). An aggregate port is a reference
already, so its copy charges the zero size alone.
-/
def viaWire (y : String) : String :=
  "module M() {\n  input x: (UInt[256], Bool);\n  wire w: (UInt[256], Bool);\n" ++
  s!"  output y: (UInt[256], Bool);\n  w := x;\n  y := {y};\n}\n"
#guard elabUnits (viaWire "w") "M" == elabUnits (viaWire "x") "M" + 1
#guard elabUnits (viaWire "x") "M" > 0

/-!
A `:=` target is a whole resource. A part of a register, an output, or a child input is `S017`
at the start of the target. An input is never a target. A hardware index of a reference is
`S011`, and a static index out of range is `S013` at the index.
-/
#guard elabOnly (agg "  reg r: P[8] = P[8]();\n  r.a := 1;\n") "M" == "S017 5:3"
#guard elabOnly (agg "  output y: P[8];\n  y.b := true;\n") "M" == "S017 5:3"
#guard elabOnly (agg "  output y: P[8];\n  y := x;\n  x := y;\n") "M" == "S017 6:3"
#guard elabOnly (agg "  input z: [Bool; 4];\n  output y: Bool;\n  let k = x.a;\n  y := z[k];\n")
  "M" == "S011 7:10"
#guard elabOnly ("module M() {\n  input x: [Bool; 4];\n  output y: Bool;\n  y := x[4];\n}\n") "M" ==
  "S013 4:10"

/-!
A reference stays lazy. A read and a static index of a port with 2^40 leaves take constant work.
The copy of the whole port charges its zero size before any work: `S015` at the statement.
-/
def huge (body : String) : String :=
  "module M() {\n  input x: [Bool; 1099511627776];\n" ++ body ++ "}\n"
#guard elabUnits (huge "  output y: Bool;\n  y := x[5];\n") "M" < 100
#guard elabOnly (huge "  output y: [Bool; 1099511627776];\n  y := x;\n") "M" == "S015 4:3"

/-!
A type that holds a function type at any depth is not hardware data. A port, a register, and a
wire of such a type are `S010` at the statement. Examples are a struct with a function field and
a tuple with `[fn () -> Bool; 0]`.
-/
def withFn : String := "struct R { f: fn () -> Bool, a: Bool }\n"
#guard elabOnly (withFn ++ "module M() {\n  input x: R;\n}\n") "M" == "S010 3:3"
#guard elabOnly (withFn ++ "module M() {\n  output y: (Bool, [fn () -> Bool; 0]);\n}\n") "M" ==
  "S010 3:3"
#guard elabOnly (withFn ++ "module M() {\n  wire w: [R; 0];\n}\n") "M" == "S010 3:3"
#guard elabOnly (withFn ++ "module M() {\n  reg r: (Bool, R) = (true, R());\n}\n") "M" ==
  "S010 3:3"

/-!
A port, a register, and a wire can have an empty type. Each still needs exactly one `:=`
(`S018` at its declaration), and so does an empty input of a child (`S018` at the `instance`
statement). A register in a combinational module is `S017` first, also with an empty type. A
read of an empty input gives its zero.
-/
def empty (body : String) : String := s!"module M() \{\n{body}}\n"
#guard (elabOnly (empty ("  input e: ();\n  output o: ();\n  o := e;\n  wire w: [UInt[8]; 0];\n" ++
  "  w := [];\n  reg r: () = ();\n  r := ();\n")) "M").startsWith "ok"
#guard elabOnly (empty "  wire w: ();\n") "M" == "S018 2:3"
#guard elabOnly (empty "  output o: [Bool; 0];\n") "M" == "S018 2:3"
#guard elabOnly (empty "  reg r: () = ();\n") "M" == "S018 2:3"
#guard elabOnly "module M() domains() {\n  reg r: () = ();\n}\n" "M" == "S017 2:3"
#guard elabOnly (empty "  wire w: ();\n  w := ();\n  w := ();\n") "M" == "S018 4:3"
/-!
An empty input charges nothing at its declaration, also with 2^40 leaves. Each read of it
charges the zero size of its type, then gives its zero. `[(); 8]` has the zero size 9. The `let`
and the name charge 1 each. A read of the huge input is thus `S015` at the name.
-/
def emptyIn (ty body : String) : String := s!"module M() \{\n  input x: {ty};\n{body}}\n"
#guard elabOnly (emptyIn "[(); 1 << 40]" "") "M" == "ok 43"
#guard elabOnly (emptyIn "[(); 1 << 40]" "  let y = x;\n") "M" == "S015 3:11"
#guard elabUnits (emptyIn "[(); 8]" "  let y = x;\n") "M" ==
  elabUnits (emptyIn "[(); 8]" "") "M" + 11
#guard elabUnits (emptyIn "()" "  let y = x;\n") "M" == elabUnits (emptyIn "()" "") "M" + 3

def emptyChild (bind : String) : String :=
  s!"module C() \{\n  input p: ();\n}\nmodule M() \{\n  instance c = C();\n{bind}}\n"
#guard elabOnly (emptyChild "") "M" == "S018 5:3"
#guard (elabOnly (emptyChild "  c.p := ();\n") "M").startsWith "ok"

/-!
A child port can have an aggregate type. A `:=` of a child input is one binding, and its sink
holds the port type for the leaves. A child output gives a reference. A part of a child input is
`S017`, and an input without a binding is `S018` at the `instance` statement.
-/
def aggChild (bind : String) : String :=
  ps ++ "module C() {\n  input p: P[8];\n  output q: P[8];\n  q := p;\n}\n" ++
  "module M() {\n  input x: P[8];\n  output y: UInt[8];\n  instance c = C();\n" ++ bind ++
  "  y := c.q.a;\n}\n"
#guard (elabOnly (aggChild "  c.p := x;\n") "M").startsWith "ok"
#guard ((topBody (aggChild "  c.p := x;\n") "M").map fun b =>
  b.binds.toList.filterMap fun d => match d.sink with
    | .child _ _ q t => some (Names.encode q, t.text)
    | _ => none) == some [("p", "P[8]")]
#guard elabOnly (aggChild "  c.p.a := x.a;\n") "M" == "S017 11:3"
#guard elabOnly (aggChild "") "M" == "S018 10:3"
#guard elabOnly (aggChild "  c.p := (x.a, x.b);\n") "M" == "S010 11:3"

/-!
A data field selection and a data index selection are data contexts (section 9.2). A read of a
part of a child input is thus `S017` at the start of the selection, before the field check.
-/
def readChild (ty read : String) : String :=
  ps ++ s!"module C() \{\n  input p: {ty};\n}\nmodule M() \{\n  input x: {ty};\n" ++
  s!"  output y: Bool;\n  instance c = C();\n  c.p := x;\n  y := {read};\n}\n"
#guard elabOnly (readChild "P[8]" "c.p.b") "M" == "S017 10:8"
#guard elabOnly (readChild "P[8]" "!c.p.b") "M" == "S017 10:9"
#guard elabOnly (readChild "P[8]" "c.p.c") "M" == "S017 10:8"
#guard elabOnly (readChild "[Bool; 2]" "c.p[0]") "M" == "S017 10:8"
#guard elabOnly (readChild "(Bool, Bool)" "c.p.1") "M" == "S017 10:8"

#guard cost (ps ++ "module M() {\n  input x: UInt[8];\n  let r = P[8](x, true);\n}\n") "M" ==
  "total 101\nM 73\n"

/-!
A constructor argument is in a data context, so a register reads (section 9.2). A module
argument is a static position. Thus an aggregate with a hardware leaf there is `S011` at the
statement, also in a literal that waits for its type.
-/
#guard cost (ps ++ "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n" ++
  "  reg q: UInt[8] = 0;\n  let r = P[8](q, true);\n  q := x;\n  y := r.a;\n}\n") "M" ==
  "total 160\nM 132\n"
def cArg (t a : String) : String :=
  s!"module C(comptime p: {t}) \{\n}\nmodule M() \{\n  input x: UInt[8];\n{a}}\n"
#guard cost (cArg "(UInt[8], Int)" "  let a = (x, 1);\n  instance c = C(a);\n") "M" == "S011 6:3"
#guard cost (cArg "([Bool; 0], UInt[8])" "  let h = x;\n  instance c = C(([], h));\n") "M" ==
  "S011 6:3"
#guard (cost (cArg "(UInt[8], Int)" "  instance c = C((3, 1));\n") "M").startsWith "total"

/-!
A module parameter can be a type or a record. Such an argument gives the digest form of the
emitted name, and the serialization holds the record with its struct type. A static field of a
record drives a port.
-/
def typed : String :=
  ps ++ "module C(comptime T: Type, comptime r: P[8]) {\n  output y: T;\n  y := r.a;\n}\n" ++
  "module M() {\n  output y: UInt[8];\n  instance c = C(UInt[8], P[8](5, true));\n" ++
  "  y := c.y;\n}\n"
#guard order typed "M" ==
  ["C$0h" ++ Names.sha16 ("(instantiation root C ((type (uint 8)) " ++
    "(record (struct root P ((int 8))) ((uint 8 5) (bool true)))))"), "M"]
#guard (cost typed "M").startsWith "total"
#guard cost (ps ++ "module C(comptime r: P[8]) {\n}\n" ++
  "module M() {\n  instance c = C(P[4](5, true));\n}\n") "M" == "S010 5:3"


/-!
A list holds no hardware value: `S011` at the element. A hardware arm cannot `push` or `pop` a
binding from before the arm: `S016` at the call. A function that the arm calls can change its
own list.
-/
def armLists (body : String) : String :=
  "fn g() -> UInt[8] { let mut ys = list(UInt[8]); push(ys, 1); return pop(ys); }\n" ++
  "module T() {\n  input c: Bool;\n  output o: UInt[8];\n" ++ body ++ "}\n"
#guard cost (armLists "  let mut xs = list(Bool);\n  push(xs, c);\n  o := 0;\n") "T" ==
  "S011 6:12"
#guard cost (armLists "  let mut xs = list(Bool);\n  push(xs, true);\n  xs[0] = c;\n  o := 0;\n")
  "T" == "S011 7:11"
#guard cost (armLists
  "  let mut xs = list(UInt[8]);\n  push(xs, 1);\n  o := if (c) { pop(xs) } else { 2 };\n")
  "T" == "S016 7:17"
#guard cost (armLists
  "  let mut xs = list(UInt[8]);\n  push(xs, 1);\n  o := if (c) { 3 } else { pop(xs) };\n")
  "T" == "S016 7:28"
#guard cost (armLists "  let mut xs = list(UInt[8]);\n  o := if (c) { push(xs, 1) } else { 2 };\n")
  "T" == "S016 6:17"
#guard (cost (armLists "  o := if (c) { g() } else { 2 };\n") "T").startsWith "total"

/-!
A hardware write-back gives the caller root its next version after the result of the call. The
write-backs run in the order of the parameters. A write-back of a binding from before a hardware
arm is `S016` at the call. A function that the arm calls can pass its own binding.
-/
def muts (body : String) : String :=
  "fn inc(mut a: UInt[8]) -> () { a = a +% 1; return (); }\n" ++
  "fn swap(mut a: UInt[8], mut b: UInt[8]) -> UInt[8] { let t = a; a = b; b = t; return t; }\n" ++
  "fn own() -> UInt[8] { let mut z: UInt[8] = 1; inc(z); return z; }\n" ++
  "module M() {\n  input c: Bool;\n  input x: UInt[8];\n  input w: UInt[8];\n" ++
  "  output y: UInt[8];\n" ++ body ++ "}\n"
#guard names (muts "  let mut q = x;\n  inc(q);\n  y := q;\n") "M" "M" ==
  ["q", "inc$0c$a", "inc$0c$a$1v", "q$1v"]
#guard names (muts "  let mut q = x;\n  q.inc();\n  q.inc();\n  y := q;\n") "M" "M" ==
  ["q", "inc$0c$a", "inc$0c$a$1v", "q$1v", "inc$1c$a", "inc$1c$a$1v", "q$2v"]
#guard names (muts "  let mut q = x;\n  let mut r = w;\n  let s = swap(q, r);\n  y := q +% r;\n")
  "M" "M" ==
  ["q", "r", "swap$0c$a", "swap$0c$b", "swap$0c$t", "swap$0c$a$1v", "swap$0c$b$1v",
   "swap$0c$0ret", "q$1v", "r$1v", "s"]
#guard cost (muts "  let mut q = x;\n  let mut r = w;\n  y := if (c) { swap(q, r) } else { 0 };\n")
  "M" == "S016 11:17"
#guard (cost (muts "  y := if (c) { own() } else { 0 };\n") "M").startsWith "total"
#guard cost (muts "  let mut q: UInt[4] = 1;\n  inc(q);\n  y := 0;\n") "M" == "S010 10:3"
#guard (cost (muts "  let mut q = [UInt[8](1)];\n  inc(q[0]);\n  y := 0;\n") "M").startsWith
  "total"

/-!
The call sites count the call nodes in pre-order (decision F18). The constructor call `T()(1)`
has two call nodes at one position, so the later call of `add` has the site 2. A receiver call
has its own site at its receiver.
-/
def sites : String :=
  "comptime fn T() -> Type { return UInt[8]; }\n" ++
  "fn add(a: UInt[8], b: UInt[8]) -> UInt[8] { return a +% b; }\n" ++
  "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n" ++
  "  let a = T()(1);\n  let s = add(x, a);\n  y := s.add(a);\n}\n"
#guard names sites "M" "M" ==
  ["add$2c$a", "add$2c$0ret", "s", "add$3c$a", "add$3c$0ret"]

/-!
A call through a function value runs as a call of its item. The call frame has the name of
the item and the site of the call. The `mut` write-backs give the same names and the same
charges as a named call. A `comptime fn` runs in the static mode, so a hardware argument is
`S011` at the call.
-/
def viaValue (body : String) : String :=
  "fn inc(mut a: UInt[8]) -> () { a = a +% 1; return (); }\n" ++
  "fn swap(mut a: UInt[8], mut b: UInt[8]) -> UInt[8] { let t = a; a = b; b = t; return t; }\n" ++
  "comptime fn cc(a: UInt[8]) -> UInt[8] { return a; }\n" ++
  "module M() {\n  input c: Bool;\n  input x: UInt[8];\n  input w: UInt[8];\n" ++
  "  output y: UInt[8];\n  let f = swap;\n  let mut q = x;\n  let mut r = w;\n" ++ body ++ "}\n"
#guard names (viaValue "  let s = f(q, r);\n  y := q +% r;\n") "M" "M" ==
  names (viaValue "  let s = swap(q, r);\n  y := q +% r;\n") "M" "M"
#guard names (viaValue "  let s = f(q, r);\n  y := q +% r;\n") "M" "M" ==
  ["q", "r", "swap$0c$a", "swap$0c$b", "swap$0c$t", "swap$0c$a$1v", "swap$0c$b$1v",
   "swap$0c$0ret", "q$1v", "r$1v", "s"]
#guard total (viaValue "  let s = f(q, r);\n  y := q +% r;\n") "M" ==
  total (viaValue "  let s = swap(q, r);\n  y := q +% r;\n") "M"
#guard names (viaValue "  let g = inc;\n  g(q);\n  g(q);\n  y := q;\n") "M" "M" ==
  ["q", "r", "inc$0c$a", "inc$0c$a$1v", "q$1v", "inc$1c$a", "inc$1c$a$1v", "q$2v"]
#guard cost (viaValue "  let g = inc;\n  y := if (c) { g(q) } else { 0 };\n") "M" ==
  "S016 13:17"
#guard cost (viaValue "  let g = cc;\n  y := g(x);\n") "M" == "S011 13:8"
#guard (cost (viaValue "  let g = cc;\n  y := g(3);\n") "M").startsWith "total"

/-!
A hardware `if` with two function arms: one function item gives the static value, and two
different items are `S011` at the `if`. The pair charges as a static equality, 1 + 1. Thus the
`if` charges its node, 1 for `c`, 4 for the second `g`, and 2 for the pair. A function and
another value are `S010` at the `if`.
-/
def fnArms (body : String) : String :=
  "fn g() -> Bool { return true; }\nfn g2() -> Bool { return false; }\n" ++
  "module T() {\n  input c: Bool;\n  output o: Bool;\n" ++ body ++ "  o := c;\n}\n"
#guard (cost (fnArms "  let f = if (c) { g } else { g };\n") "T").startsWith "total"
#guard total (fnArms "  let f = if (c) { g } else { g };\n") "T" ==
  total (fnArms "  let f = g;\n") "T" + 8
#guard cost (fnArms "  let f = if (c) { g } else { g2 };\n") "T" == "S011 6:11"
#guard cost (fnArms "  let f = if (c) { g } else { true };\n") "T" == "S010 6:11"
#guard cost (fnArms "  let f: fn () -> Bool = if (c) { g } else { g };\n") "T" |>.startsWith
  "total"

/-!
F19: a hardware `if` with two static arms of a type that is not hardware data is a static pair.
It charges as a static equality, the sum of the sizes. Thus `if (c) { 3 } else { 3 }` charges
its node, 1 for `c`, 2 for each arm, and 2 for the pair: 6 more than `3`, which charges 2. Equal
arms give the static value, and different arms are `S011` at the `if`. An `Int` arm and a `Bool`
arm have no join, so they are `S010` at the `if`. Two arms of type `()` give `()`.
-/
def arms (body : String) : String :=
  "module T() {\n  input c: Bool;\n  output o: UInt[8];\n" ++ body ++ "  o := 0;\n}\n"
#guard total (arms "  let k = if (c) { 3 } else { 3 };\n") "T" ==
  total (arms "  let k = 3;\n") "T" + 6
#guard (cost (arms "  let k = if (c) { \"a\" } else { \"a\" };\n") "T").startsWith "total"
#guard (cost (arms "  let k = if (c) { () } else { () };\n") "T").startsWith "total"
#guard cost (arms "  let k = if (c) { 3 } else { 4 };\n") "T" == "S011 4:11"
#guard cost (arms "  let k = if (c) { UInt[8] } else { UInt[4] };\n") "T" == "S011 4:11"
#guard cost (arms "  let k = if (c) { 3 } else { true };\n") "T" == "S010 4:11"

/-!
A function value is a module argument (section 7.1). It serializes as `(function root inc)`, so
it gives the digest form of the emitted name. A constant and a name of one function give one
instantiation. A function type, an array of functions, and `[]` at an array of functions are
arguments too. The child calls the function through its parameter.
-/
def fnItems : String :=
  "fn inc(a: UInt[8]) -> UInt[8] { return a +% 1; }\n" ++
  "fn dec(a: UInt[8]) -> UInt[8] { return a -% 1; }\n" ++
  "fn bump(mut a: UInt[8]) -> UInt[8] { return a; }\n" ++
  "fn gen(comptime W: Nat, a: UInt[W]) -> UInt[W] { return a; }\n"
def fnTy : String := "fn (UInt[8]) -> UInt[8]"
def fnArg (ty arg : String) : String :=
  fnItems ++ s!"module C(comptime f: {ty}) \{\n}\nmodule M() \{\n  instance c = C({arg});\n}\n"
def fnDigest (arg : String) : String :=
  "C$0h" ++ Names.sha16 s!"(instantiation root C ({arg}))"
#guard order (fnArg fnTy "inc") "M" == [fnDigest "(function root inc)", "M"]
#guard order (fnArg fnTy "dec") "M" == [fnDigest "(function root dec)", "M"]
#guard order (fnArg "Type" "fn (mut UInt[8]) -> Bool") "M" ==
  [fnDigest "(type (fn ((mut (uint 8))) bool))", "M"]
#guard order (fnArg s!"[{fnTy}; 1]" "[inc]") "M" ==
  [fnDigest "(array (fn ((uint 8)) (uint 8)) ((function root inc)))", "M"]
#guard order (fnArg s!"[{fnTy}; 0]" "[]") "M" ==
  [fnDigest "(array (fn ((uint 8)) (uint 8)) ())", "M"]
#guard order (s!"const F: {fnTy} = inc;\n" ++ fnItems ++
  s!"module C(comptime f: {fnTy}) \{\n}\nmodule M() \{\n  instance c = C(F);\n" ++
  "  instance d = C(inc);\n}\n") "M" == [fnDigest "(function root inc)", "M"]
#guard (cost (fnItems ++ s!"module C(comptime f: {fnTy}) \{\n" ++
  "  input x: UInt[8];\n  output y: UInt[8];\n  y := f(x);\n}\n" ++
  "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n  let g = inc;\n" ++
  "  instance c = C(g);\n  c.x := x;\n  y := c.y;\n}\n") "M").startsWith "total"

/-!
The parent pays for a function argument as for each argument. The units of `M` with `C(inc)`
are those with `C(3)` at an `Int` parameter, plus 61. The name `inc` charges 16 units more than
the literal `3` (`Test.Eval`). Each argument has the size 1. The walk that measures the
serialization charges 1 for the integer and nothing for the function. The serialization has
44 bytes instead of 32. The emitted name has 20 bytes instead of 3, and both the statement and
the lowering of the child charge it.
-/
def units (src t m : String) : Nat :=
  match (cost src t).splitOn "\n" |>.find? (·.startsWith s!"{m} ") with
  | some line => (line.drop (m.length + 1)).toString.toNat!
  | none => 0
#guard units (fnArg fnTy "inc") "M" "M" ==
  units (fnArg "Int" "3") "M" "M" + 16 + (44 - 32) + 2 * (20 - 3) - 1
#guard exact (fnArg fnTy "inc") "M" (total (fnArg fnTy "inc") "M")

/-!
A typed use at a module parameter needs the exact function type: another `mut` mark, another
function type, and another value are `S010` at the statement. A generic function and a builtin
are `S010` at the name, before the statement.
-/
#guard cost (fnArg fnTy "bump") "M" == "S010 8:3"
#guard cost (fnArg "fn (UInt[8]) -> Bool" "inc") "M" == "S010 8:3"
#guard cost (fnArg fnTy "3") "M" == "S010 8:3"
#guard cost (fnArg "UInt[8]" "inc") "M" == "S010 8:3"
#guard cost (fnArg fnTy "gen") "M" == "S010 8:18"
#guard cost (fnArg fnTy "len") "M" == "S010 8:18"

/-!
A top selection has only literal arguments (section 8), so a function there is a usage error.
A literal at a function parameter is `S010` at the top selection.
-/
#guard cost (fnItems ++ s!"module C(comptime f: {fnTy}) \{\n}\n") "C(inc)" == "usage"
#guard cost (fnItems ++ s!"module C(comptime f: {fnTy}) \{\n}\n") "C(3)" == "S010 1:1"

/-!
A function value is a struct argument and a field of a record. The struct type serializes its
arguments, so the key of the specialization and the `InstantiationId` hold the function. Another
function gives another struct type: `S010` at the statement. A function with another type at
the struct parameter is `S010` at the specialization.
-/
def fnStruct (field arg : String) : String :=
  fnItems ++ s!"struct S(comptime f: {fnTy}) \{ a: UInt[8] }\nstruct R \{ f: {fnTy} }\n" ++
  s!"module C(comptime s: {field}) \{\n}\nmodule M() \{\n  instance c = C({arg});\n}\n"
#guard order (fnStruct "S[inc]" "S[inc](1)") "M" ==
  [fnDigest "(record (struct root S ((function root inc))) ((uint 8 1)))", "M"]
#guard order (fnStruct "R" "R(inc)") "M" ==
  [fnDigest "(record (struct root R ()) ((function root inc)))", "M"]
#guard cost (fnStruct "S[inc]" "S[dec](1)") "M" == "S010 10:3"
#guard cost (fnStruct "S[inc]" "S[bump](1)") "M" == "S010 10:18"
#guard cost (fnStruct "R" "R(bump)") "M" == "S010 10:18"
#guard (cost (fnItems ++ s!"struct R \{ f: {fnTy} }\nmodule M() \{\n  input x: UInt[8];\n" ++
  "  output y: UInt[8];\n  let r = R(inc);\n  y := (r.f)(x);\n}\n") "M").startsWith "total"

/-!
A function type is not hardware data. A port, a register, and a wire of a function type, also
in an array, are `S010` at the statement. A function value at a hardware use is `S010` at the
statement: a `:=` value and a register value, also from a hardware `if` with one function.
No function value thus reaches the lowering.
-/
def fnHw (body : String) : String :=
  fnItems ++ "module M() domains(clk) {\n  input c: Bool;\n" ++ body ++ "}\n"
#guard cost (fnHw s!"  input x: {fnTy};\n") "M" == "S010 7:3"
#guard cost (fnHw s!"  output x: {fnTy};\n") "M" == "S010 7:3"
#guard cost (fnHw s!"  wire x: {fnTy};\n") "M" == "S010 7:3"
#guard cost (fnHw s!"  reg x: {fnTy} = inc;\n") "M" == "S010 7:3"
#guard cost (fnHw s!"  input x: [{fnTy}; 0];\n") "M" == "S010 7:3"
#guard cost (fnHw "  reg r: UInt[8] = inc;\n  r := r;\n") "M" == "S010 7:3"
#guard cost (fnHw "  output y: UInt[8];\n  y := inc;\n") "M" == "S010 8:3"
#guard cost (fnHw "  output y: UInt[8];\n  y := if (c) { inc } else { inc };\n") "M" ==
  "S010 8:3"

/-!
A name refers to a core name, so its hardware value has the size of a finite value of its type
(section 5.4). Each copy of a `UInt[256]` name thus charges 4, and each copy of a `UInt[64]`
name 1. The binding of `p`, the binding of `x`, and the `:=` of `y` copy a name.
-/
def copies (w : Nat) : String :=
  s!"module M() \{\n  input p: UInt[{w}];\n  output q: UInt[{w}];\n" ++
  "  let x = p;\n  let y = x;\n  q := y;\n}\n"
#guard total (copies 256) "M" == total (copies 64) "M" + 9
#guard exact (copies 256) "M" 99

/-!
The memory port calls (section 6.2). The elaboration alone runs them, with the fuel `fuel` and
the depth `depth`. A call gives each error at the call, and a receiver call starts at its
receiver.
-/
def elabAt (src t : String) (fuel : Nat) (depth : Nat := 1000) : String :=
  match Cli.load 4096 src with
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked t with
    | .error _ => "usage"
    | .ok (p, i, _, xs) =>
      match Elab.elaborate { fuel, depth } checked Names.sha16 p i xs with
      | .ok (_, u) => s!"ok {u}"
      | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"

def portBody (ss : String) : String :=
  "module M() {\n  input a: UInt[2];\n  input e: Bool;\n  input d: UInt[8];\n" ++ ss ++ "}\n"
def port (ss : String) : String := elabOnly (portBody ss) "M"
def portAt (ss : String) (fuel : Nat) (depth : Nat := 1000) : String :=
  elabAt (portBody ss) "M" fuel depth
def m4 : String := "  mem m: [UInt[8]; 4];\n"
def wr : String := "  write_port(m, a, d, e);\n"
def rw : String := m4 ++ wr ++ "  let r = m.read_port(a, e);\n"

/-! A hardware leaf of a binding: a leaf of a word with its offset and type, or a name. -/
def leafOp (h : Eval.Hw) : String :=
  match h with
  | .node _ t _ (.word m o) _ => s!"word {Names.encode m.name}@{o}:{t.text}"
  | .node _ _ _ (.ref p) _ => s!"ref {Names.encode p.name}"
  | _ => "other"

/-! The bindings of the top instantiation with their leaves. -/
def portLets (ss : String) : Option (List (String × String)) :=
  (topBody (portBody ss) "M").map
    (·.lets.toList.map fun l => (Names.encode l.path.name, leafOp l.value))

/-! The requests of each memory of the top instantiation, as the texts of their parts. -/
def requests (ss : String) : Option (List (Option (List String) × Option (List String))) :=
  (topBody (portBody ss) "M").map (·.mems.toList.map fun m =>
    (m.read.map fun (x, y) => [x.text, y.text],
     m.write.map fun (x, y, z) => [x.text, y.text, z.text]))

/-!
The memory records the first request of each kind after its typed uses. The response refers to
the word at the offset 0 and to `m$0rvalid`, and its binding binds each hardware leaf.
-/
#guard port rw == "ok 95"
#guard requests rw == some [(some ["hardware UInt[2]", "hardware Bool"],
  some ["hardware UInt[2]", "hardware UInt[8]", "hardware Bool"])]
#guard requests (m4 ++ "  write_port(m, 1, 7, true);\n  let r = m.read_port(a, e);\n") ==
  some [(some ["hardware UInt[2]", "hardware Bool"], some ["UInt[2]", "UInt[8]", "Bool"])]
#guard portLets rw == some [("r$data", "word m@0:UInt[8]"), ("r$valid", "ref m$0rvalid")]
#guard portLets ("  mem m: [(UInt[3], Bool, UInt[5]); 4];\n" ++
  "  write_port(m, a, (1, true, 2), e);\n  let r = m.read_port(a, e);\n") ==
  some [("r$data$0e", "word m@0:UInt[3]"), ("r$data$1e", "word m@3:Bool"),
    ("r$data$2e", "word m@4:UInt[5]"), ("r$valid", "ref m$0rvalid")]

/-!
The first argument is a memory, else `S010` at the call. The address has the type `UInt[A]`
with `A = max(1, ⌈log₂ N⌉)`. The enable has the type `Bool`, and the data the word type. Another
hardware type is `S010`, and a static value that does not fit is `S012`. The typed uses run in
the order of the arguments. A static address that fits but is not below `N` is valid, not `S013`.
-/
#guard port (m4 ++ wr ++ "  let q = read_port(e, a, e);\n") == "S010 7:11"
#guard port (m4 ++ wr ++ "  let q = read_port(5, a, e);\n") == "S010 7:11"
#guard port ("  reg g: UInt[8] = 0;\n  g := g;\n" ++ m4 ++ "  write_port(g, a, d, e);\n") ==
  "S010 8:3"
#guard port ("  mem m: [UInt[8]; 3];\n  let r = read_port(m, d, e);\n") == "S010 6:11"
#guard port (m4 ++ "  let r = read_port(m, a, d);\n") == "S010 6:11"
#guard port (m4 ++ "  write_port(m, a, a, e);\n") == "S010 6:3"
#guard port (m4 ++ "  let q = read_port(m, 4, d);\n") == "S012 6:11"
#guard port (m4 ++ "  write_port(m, 4, 256, d);\n") == "S012 6:3"
#guard port (m4 ++ "  write_port(m, a, 256, d);\n") == "S012 6:3"
#guard port ("  mem m: [UInt[8]; 1];\n  write_port(m, 2, 1, true);\n") == "S012 6:3"
#guard port ("  mem m: [UInt[8]; 3];\n  write_port(m, 3, 1, true);\n" ++
  "  let r = read_port(m, 3, false);\n") == "ok 106"
#guard port ("  mem m: [UInt[8]; 1];\n  write_port(m, 1, 1, true);\n" ++
  "  let r = read_port(m, 0, false);\n") == "ok 106"

/-!
A call in a hardware arm is `S016` at the call, after the memory check and before the typed
uses.
-/
#guard port (m4 ++ "  let q = if (e) { read_port(m, 4, d) } else { 1 };\n") == "S016 6:20"
#guard port (m4 ++ "  let q = if (e) { read_port(a, 4, d) } else { 1 };\n") == "S010 6:20"

/-!
`S018`: a second call of one kind is `S018` at the call, also by a receiver and through a `let`
alias. It waits for the end of the body, so a later error comes first. A memory without a read
or without a write is `S018` at its statement, and all of them compete by position.
-/
def rr : String := rw ++ "  let q = m.read_port(a, e);\n"
#guard port rr == "S018 8:11"
#guard port (rw ++ "  m.write_port(a, d, e);\n") == "S018 8:3"
#guard port (m4 ++ "  let k = m;\n  write_port(k, a, d, e);\n" ++
  "  let r = m.read_port(a, e);\n  let q = k.read_port(a, e);\n") == "S018 9:11"
#guard port (rr ++ "  let z: Bool = d;\n") == "S010 9:3"
#guard port (m4 ++ "  let r = m.read_port(a, e);\n") == "S018 5:3"
#guard port (m4 ++ wr) == "S018 5:3"
#guard port (m4 ++ "  mem n: [UInt[8]; 4];\n  write_port(n, a, d, e);\n" ++
  "  let r = read_port(n, a, e);\n  let q = read_port(n, a, e);\n") == "S018 5:3"
#guard port (m4 ++ wr ++ wr ++ "  let r = read_port(m, a, e);\n  let q = read_port(m, a, e);\n") ==
  "S018 7:3"

/-!
An error in the work of the prelude struct reports at the call (D7): the depth of
`ReadResponse[T]`.
-/
#guard portAt rw 100000 (depth := 2) == "S015 7:11"
#guard portAt rw 100000 (depth := 3) == "ok 95"

/-!
The charges. The zero size of the response is the last charge of the call. A second read
charges as a read with a done specialization of `ReadResponse[T]`, also of another memory. A
wide word charges the copy of its data and the zero size of its response, with no walk.
-/
#guard portAt rw 95 == "ok 95"
#guard portAt rw 94 == "S015 7:11"
#guard portAt rr 110 == "S018 8:11"
#guard portAt rr 109 == "S015 8:11"
#guard portAt (rw ++ wr) 106 == "S018 8:3"
#guard portAt (rw ++ wr) 105 == "S015 8:3"
def spec8 : String := "  let t = ReadResponse[UInt[8]];\n"
#guard portAt (m4 ++ wr) 63 == "S018 5:3"
#guard portAt (m4 ++ wr) 62 == "S015 6:3"
#guard port (spec8 ++ rw) == "ok 107"
#guard portAt (spec8 ++ m4 ++ wr) 92 == "S018 6:3"
#guard portAt (spec8 ++ m4 ++ wr) 91 == "S015 7:3"
#guard 110 - 95 == 107 - 92
def mn : String := rw ++ "  mem n: [UInt[8]; 4];\n  write_port(n, a, d, e);\n"
#guard port (mn ++ "  let q = n.read_port(a, e);\n") == "ok 130"
#guard portAt mn 115 == "S018 8:3"
#guard portAt mn 114 == "S015 9:3"
def wideW (k : Nat) : String :=
  s!"  input x: [Bool; {k}];\n  mem m: [[Bool; {k}]; 4];\n  let r = m.read_port(a, e);\n" ++
  "  write_port(m, a, x, e);\n"
#guard port (wideW 4) == "ok 120"
#guard port (wideW 4096) == s!"ok {120 + 2 * (4096 - 4)}"

end Silicon.Source.Test.Elab
