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

/-! The elaborated design of `src` with the top selection `t`. -/
def design (src t : String) : Option Elab.Design :=
  match Cli.load 4096 src with
  | .error _ => none
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked t with
    | .error _ => none
    | .ok (p, i, _, xs) =>
      match Elab.elaborate {} checked Names.sha16 p i xs with
      | .ok (d, _) => some d
      | .error _ => none

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
conversions, and a child input through a handle alias.
-/
def ops : String :=
  "module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := !a;\n}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n  input s: SInt[8];\n  input c: UInt[3];\n  input e: Bool;\n" ++
  "  output y: UInt[8];\n  output z: SInt[16];\n  output b: Bool;\n" ++
  "  let w = (x +% 1) -% (x *% 3) & ~x | (x ^ 255);\n" ++
  "  let v = -s >> c;\n" ++
  "  let k = if (e) { 1 } else { x << 2 };\n" ++
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

/-! `S017`: the resource rule. -/
#guard cost "module M() {\n  input x: Bool;\n  x := true;\n}\n" "M" == "S017 3:3"
#guard cost "module M() domains() {\n  reg r: Bool = false;\n}\n" "M" == "S017 2:3"
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

end Silicon.Source.Test.Elab
