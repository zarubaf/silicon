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

#guard cost counter "Main" == "total 427\nCounter$4 193\nMain 197\n"
#guard exact counter "Main" 427
#guard cost counter "Counter(8)" == "total 254\nCounter$8 193\n"
#guard order counter "Main" == ["Counter$4", "Main"]

/-!
The table of instantiations. A child finishes before its parent. A repeated `InstantiationId`
elaborates once. Its `instance` statement charges 1, and its argument charges 2 for the node and
the literal. Its parameter type `Nat` charges 1, and the recursive size 1. Its serialization
charges 1 for the decimal form and 32 for its bytes. Its lowering charges 44. The `inst` node and
its name charge 2, and the emitted name 2. Each of the two domain connections charges 20. These
are 82 units. The child pays nothing for its parameter.
-/
def leaf : String := "module C(comptime n: Nat) {\n}\n"
def one : String := leaf ++ "module T() {\n  instance a = C(5);\n}\n"
def two : String := leaf ++ "module T() {\n  instance a = C(5);\n  instance b = C(5);\n}\n"
def other : String := leaf ++ "module T() {\n  instance a = C(5);\n  instance b = C(6);\n}\n"

#guard total two "T" == total one "T" + 82
#guard order two "T" == ["C$5", "T"]
#guard order other "T" == ["C$5", "C$6", "T"]
#guard cost other "T" == s!"total {total other "T"}\nC$5 24\nC$6 24\nT 193\n"

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
  "module M(comptime x: [UInt[8]; 1]) {\n}\n" ++
  "module T() {\n  instance a = M([1]);\n  instance b = M([2]);\n}\n"
#guard (cost digests "T").startsWith "total"
#guard cost digests "T" (digest := collide) == "S019 5:3"
#guard order digests "T" ==
  ["M$0h" ++ Names.sha16 "(instantiation root M ((array (uint 8) ((uint 8 1)))))",
   "M$0h" ++ Names.sha16 "(instantiation root M ((array (uint 8) ((uint 8 2)))))", "T"]

/-!
An emitted name is taken when its instantiation starts. A descendant that shares the emitted name
of an active ancestor is thus `S019` at its own `instance` statement.
-/
def nested : String :=
  "module M(comptime x: [UInt[8]; 1]) {\n" ++
  "  comptime if (x[0] == UInt[8](1)) { instance a = M([0]); }\n}\n" ++
  "module T() {\n  instance b = M([1]);\n}\n"
#guard (cost nested "T").startsWith "total"
#guard cost nested "T" (digest := collide) == "S019 2:38"

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

/-!
The typed use of the module arguments nests one level at each `instance` statement, also at a
repeat of a done instantiation (section 5.3). `Leaf()` in `Wrap` is a repeat at the depth 3.
-/
def repeatDeep : String :=
  "module Leaf() {\n}\nmodule Wrap() {\n  instance c = Leaf();\n}\n" ++
  "module Top() {\n  instance a = Leaf();\n  instance b = Wrap();\n}\n"
#guard (cost repeatDeep "Top" (depth := 3)).startsWith "total"
#guard cost repeatDeep "Top" (depth := 2) == "S015 4:3"

/-!
The `InstantiationId` holds the arguments after their typed use (section 7.1). `C(1)` and
`C(UInt[8](1))` thus give one instantiation, and so do `[1, 2]` and `[UInt[8](1), UInt[8](2)]` at
the type `[UInt[8]; 2]`.
-/
def convTwo (ty a b : String) : String :=
  s!"module C(comptime x: {ty}) \{\n}\nmodule T() \{\n  instance a = C({a});\n" ++
  s!"  instance b = C({b});\n}\n"
#guard (order (convTwo "UInt[8]" "1" "UInt[8](1)") "T").length == 2
#guard order (convTwo "UInt[8]" "1" "UInt[8](1)") "T" ==
  order (convTwo "UInt[8]" "UInt[8](1)" "UInt[8](1)") "T"
#guard (order (convTwo "[UInt[8]; 2]" "[1, 2]" "[UInt[8](1), UInt[8](2)]") "T").length == 2
#guard order (convTwo "[UInt[8]; 2]" "[1, 2]" "[UInt[8](1), UInt[8](2)]") "T" ==
  order (convTwo "[UInt[8]; 2]" "[UInt[8](1), UInt[8](2)]" "[1, 2]") "T"
#guard (order (convTwo "[Nat; 2]" "[1, 2]" "[1, 2]") "T").length == 2

/-!
A failed typed use is at the statement, before `S017` (section 6.2). `Clocked(300)` in a
combinational module is thus `S012`, and `Clocked(3)` is `S017`.
-/
def comb (arg : String) : String :=
  "module Clocked(comptime n: UInt[8]) {\n}\n" ++
  s!"module Comb() domains() \{\n  instance u = Clocked({arg});\n}\n"
#guard cost (comb "300") "Comb" == "S012 4:3"
#guard cost (comb "3") "Comb" == "S017 4:3"
#guard cost (comb "true") "Comb" == "S010 4:3"

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
argument after its typed use: each element converts to the element type of the parameter. A `[]`
argument takes the type of its parameter, also nested.
-/
def container (ty arg : String) : String :=
  s!"module C(comptime xs: {ty}) \{\n}\nmodule T() \{\n  instance a = C({arg});\n}\n"
#guard order (container "[UInt[8]; 2]" "[1, 2]") "T" ==
  ["C$0h" ++
    Names.sha16 "(instantiation root C ((array (uint 8) ((uint 8 1) (uint 8 2)))))", "T"]
#guard order (container "[Bool; 0]" "[]") "T" ==
  ["C$0h" ++ Names.sha16 "(instantiation root C ((array bool ())))", "T"]
#guard order (container "([Bool; 0], Int)" "([], 1)") "T" ==
  ["C$0h" ++ Names.sha16 "(instantiation root C ((tuple ((array bool ()) (int 1)))))", "T"]
#guard cost (container "[Bool; 0]" "[[]]") "T" == "S010 4:3"
#guard (cost ("module C(comptime n: Nat, comptime xs: [[Bool; 0]; n]) {\n}\n" ++
  "module T() {\n  instance a = C(2, [[], []]);\n}\n") "T").startsWith "total"

/-!
The serialization of a container charges 1 for each container node, then its bytes. The parent
pays it, with the parameter type and the conversion of each element. `[[1, 2]]` costs `T` 50
units more than `[1, 2]`: the outer literal, the outer array type, the size of the outer node,
the walk, and the longer serialization.
-/
#guard (cost (container "[UInt[8]; 2]" "[1, 2]") "T").endsWith "\nT 206\n"
#guard (cost (container "[[UInt[8]; 2]; 1]" "[[1, 2]]") "T").endsWith "\nT 256\n"

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
  "S013 3:5"
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

/-!
The size limit of section 5.4 at the largest fuel. A reference of a type with a zero size above
2^32 stays valid, and a binding of it walks only its hardware leaves. A value that the type
makes, an expansion in a place update, and a `diagnostic` record fail before their charges.
-/
def limited (src : String) : String :=
  match Cli.load 4096 src with
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked "M" with
    | .error _ => "usage"
    | .ok (p, i, _, xs) =>
      match Elab.elaborate { fuel := 2 ^ 64 - 1 } checked Names.sha16 p i xs with
      | .ok (_, u) => s!"ok {u}"
      | .error e => s!"{e.code} {e.pos.line}:{e.pos.col} {e.msg}"

def hugeIn (body : String) : String :=
  emptyIn "([(); 2305843009213693952], Bool)" s!"  let mut y = x;\n{body}"
def zeroAt (pos : String) : String := s!"S015 {pos} {Eval.zeroLimitText}"
#guard (limited (hugeIn "")).startsWith "ok"
#guard limited (hugeIn "  y.1 = true;\n") == zeroAt "4:3"
#guard limited (hugeIn "  let w = y.0;\n") == zeroAt "4:11"
#guard limited (emptyIn "[(); 2305843009213693952]" "  let y = x;\n") == zeroAt "3:11"
#guard limited (hugeIn "  diagnostic(\"d\", y);\n") ==
  s!"S015 4:3 {Eval.recordLimitText}"

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
are those with `C(3)` at an `Int` parameter, plus 78. The name `inc` charges 16 units more than
the literal `3` (`Test.Eval`). The parameter type `fn (UInt[8]) -> UInt[8]` charges 17 units more
than `Int`. Each argument has the size 1. The walk that measures the serialization charges 1 for
the integer and nothing for the function. The serialization has 44 bytes instead of 32. The
emitted name has 20 bytes instead of 3, and both the statement and the lowering of the child
charge it.
-/
def units (src t m : String) : Nat :=
  match (cost src t).splitOn "\n" |>.find? (·.startsWith s!"{m} ") with
  | some line => (line.drop (m.length + 1)).toString.toNat!
  | none => 0
#guard units (fnArg fnTy "inc") "M" "M" ==
  units (fnArg "Int" "3") "M" "M" + 16 + 17 + (44 - 32) + 2 * (20 - 3) - 1
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

/-!
Structural contexts (section 9.4). Each sets a guard of the kind `structural` at the current
depth. A `push`, a `pop`, or a `mut` write-back of a binding from before the context is `S016`
at the call. A helper that the context calls can change its own locals. `T(x)`, `static_assert`,
`comptime if`, `comptime for`, and the body of a `comptime fn` that the module body calls are
not structural. The innermost guard wins, so a type in a hardware arm gives the structural text.
-/
def sPre : String :=
  "struct P(comptime W: Nat) { a: UInt[W] }\n" ++
  "fn f(mut n: Int) -> Int { n = n + 1; return n; }\n" ++
  "fn h() -> Nat { let mut ys = list(Nat); push(ys, 4); return pop(ys); }\n"
def sMod (body : String) : String :=
  sPre ++ "module M() {\n  input c: Bool;\n  input a: UInt[2];\n  input d: UInt[8];\n" ++
  "  output o: UInt[8];\n  let mut xs = list(Nat);\n  push(xs, 2);\n  push(xs, 3);\n" ++
  "  let mut n = 3;\n" ++ body ++ "  o := 0;\n}\n"
def sRun (body : String) (fs : String := "") : String := elabOnly (fs ++ sMod body) "M"

/-! The message of the first error of `src` with the top `M`, or `ok`. -/
def said (src : String) : String :=
  match Cli.load 4096 src with
  | .error e => e.msg
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked "M" with
    | .error _ => "usage"
    | .ok (p, i, _, xs) =>
      match Elab.elaborate {} checked Names.sha16 p i xs with
      | .ok _ => "ok"
      | .error e => e.msg

-- Context 1: the annotations of a `let`, a `wire`, and a `reg`, and the parameter and result
-- types of a call.
#guard sRun "  let x: [Bool; pop(xs)] = [false, false, false];\n" == "S016 13:17"
#guard sRun "  let x: UInt[f(n)] = 0;\n" == "S016 13:15"
#guard sRun "  wire w: UInt[pop(xs)];\n  w := 0;\n" == "S016 13:16"
#guard sRun "  reg r: UInt[pop(xs)] = 0;\n  r := r;\n" == "S016 13:15"
#guard sRun "  let z = g(xs, 1);\n"
  "fn g(mut ys: List[Nat], b: UInt[pop(ys)]) -> Nat { return 1; }\n" == "S016 1:33"
#guard sRun "  let z = g(xs);\n"
  "fn g(mut ys: List[Nat]) -> UInt[pop(ys)] { return 1; }\n" == "S016 1:33"
-- Context 2: the expression forms that make a type.
#guard sRun "  let x = UInt[pop(xs)](0);\n" == "S016 13:16"
#guard sRun "  let x = UInt[xs.pop()](0);\n" == "S016 13:16"
#guard sRun "  let t = [Bool; push(xs, 4)];\n" == "S016 13:18"
#guard sRun "  let t = fn (UInt[pop(xs)]) -> Bool;\n" == "S016 13:20"
-- Context 3: a `type` statement.
#guard sRun "  type T = UInt[pop(xs)];\n" == "S016 13:17"
-- Context 4: the arguments of a struct use.
#guard sRun "  let t = P[pop(xs)];\n" == "S016 13:13"
#guard sRun "  let x: P[f(n)] = P[4](1);\n" == "S016 13:12"
-- Context 5: the word type and the depth of a `mem` statement.
#guard sRun "  mem q: [UInt[pop(xs)]; 4];\n" == "S016 13:16"
#guard sRun "  mem q: [UInt[8]; pop(xs)];\n" == "S016 13:20"
#guard sRun "  mem q: [UInt[8]; f(n)];\n" == "S016 13:20"
-- A helper changes its own locals; the other forms are not structural.
#guard sRun "  let x: UInt[h()] = 0;\n" == "ok 106"
#guard sRun "  let x = UInt[8](pop(xs));\n" == "ok 90"
#guard sRun "  comptime if (pop(xs) == 3) {}\n" == "ok 86"
#guard sRun "  comptime for i in 0..pop(xs) {}\n" == "ok 90"
#guard sRun "  let z = cf();\n  let w: UInt[cf()] = 0;\n"
  "comptime fn cf() -> Nat { let mut ys = list(Nat); push(ys, 4); return pop(ys); }\n" ==
  "ok 128"
-- A constant used first inside a hardware arm runs its helper with no `S016`.
#guard sRun "  let z = if (c) { UInt[8](K) } else { 0 };\n" "const K: Nat = h();\n" == "ok 120"
#guard sRun "  let z = if (c) { UInt[K](1) } else { 0 };\n" "const K: Nat = h();\n" == "ok 120"
-- The innermost guard wins: a type in a hardware arm gives the structural text.
#guard sRun "  let z = if (c) { pop(xs) } else { 0 };\n" == "S016 13:20"
#guard said (sMod "  let z = if (c) { UInt[pop(xs)](0) } else { 0 };\n") ==
  "a type or a constant cannot change `xs`; change `xs` before it, keep the result in a " ++
  "`let`, and use that name here"

/-!
The other effects (section 9.4). A declaration or a `:=` in a helper is a graph effect, so in a
structural context it is `S016` at the statement. In a `comptime fn` it is `S006` (pass 4). A
memory port call in a structural context is `S016` at the call. The check rejects a memory name
at a static position (`S005`), so an alias reaches the call.
-/
#guard sRun "  let x: UInt[g()] = 0;\n" "fn g() -> Nat { reg r: UInt[8] = 0; return 1; }\n" ==
  "S016 1:17"
#guard sRun "  let x: UInt[g()] = 0;\n" "fn g() -> Nat { mem q: [UInt[8]; 4]; return 1; }\n" ==
  "S016 1:17"
#guard sRun "  let x: UInt[g()] = 0;\n"
  "comptime fn g() -> Nat { reg r: UInt[8] = 0; return 1; }\n" == "S006 1:26"
#guard sRun "  let x: UInt[g()] = 0;\n"
  "comptime fn g() -> Nat { mem q: [UInt[8]; 4]; return 1; }\n" == "S006 1:26"
#guard sRun "  let x: UInt[g(1)] = 0;\n" "fn g(x: UInt[8]) -> Nat { x := 1; return 1; }\n" ==
  "S016 1:27"
#guard sRun "  let x: UInt[g(1)] = 0;\n"
  "comptime fn g(x: UInt[8]) -> Nat { x := 1; return 1; }\n" == "S006 1:36"
def sMem (wr : Bool) (rest : String) : String :=
  sMod ("  mem q: [UInt[8]; 4];\n" ++
    (if wr then "  write_port(q, a, d, c);\n" else "  let r = read_port(q, a, c);\n") ++
    "  let k = q;\n" ++ rest)
#guard elabOnly (sMem true "  let x: UInt[read_port(k, 0, true)] = 0;\n") "M" == "S016 16:15"
#guard elabOnly (sMem false "  mem q2: [UInt[8]; write_port(k, 0, 1, true)];\n") "M" ==
  "S016 16:21"
#guard elabOnly (sMem false "  let t = [Bool; k.write_port(0, 1, true)];\n") "M" == "S016 16:18"
#guard elabOnly (sMem true "  let x: UInt[read_port(q, 0, true)] = 0;\n") "M" == "S005 16:25"

/-! Each normative text of `S016` (section 9.4), in full. -/
def armEffect (g : String) : String :=
  s!"a hardware arm has no graph effect such as `{g}`; call `{g}` before the `if` or `match`, " ++
    "and use its result in the arm"
#guard said (sMod "  let x: [Bool; pop(xs)] = [false, false, false];\n") ==
  "a type or a constant cannot change `xs`; change `xs` before it, keep the result in a " ++
  "`let`, and use that name here"
#guard said (sMod "  let x: UInt[f(n)] = 0;\n") ==
  "a type or a constant cannot change `n`; change `n` before it, keep the result in a " ++
  "`let`, and use that name here"
#guard said (sMem true "  let x: UInt[read_port(k, 0, true)] = 0;\n") ==
  "a type or a constant has no graph effect such as `read_port`; call it before and use the result"
#guard said (sMod "  let z = if (c) { pop(xs) } else { 0 };\n") ==
  "a hardware arm changes a binding from before the arm"
#guard said (sMem true "  let z = if (c) { read_port(q, a, c) } else { 0 };\n") ==
  armEffect "read_port"

/-!
`diagnostic` (sections 6.2 and 8.2). A call charges its node and its name, then its arguments
from left to right, then their copies. Then come the effect rule (`S016`), the message in the
`data` context, and a value that waits for its type (`S010`). Then the measure charge of the
value and the length of the record in bytes. The record goes into the list after its charges.
-/
def dMod (body : String) (fs : String := "") : String :=
  fs ++ "module M() {\n  input c: Bool;\n  input d: UInt[8];\n  output o: UInt[8];\n" ++ body ++
    "  o := 0;\n}\n"

/-! The records of `observe` with the top `M`, then `ok` or the code and the position. -/
def observed (src : String) (fuel : Nat := 100000000) : List String :=
  let (rs, r) := Cli.observeRun { budget := { fuel, depth := 1000 } } src "M" Names.sha16
  rs.toList ++ [match r with
    | .ok _ => "ok"
    | .error (.error e) => s!"{e.code} {e.pos.line}:{e.pos.col}"
    | .error _ => "other"]

/-!
An instantiation of `C(1)` that reaches `C(UInt[8](1))` reaches itself: `S019` at the inner
statement. The body of `C` runs once, so its record comes out once.
-/
def convSelf : String :=
  "module C(comptime x: UInt[8]) {\n  diagnostic(\"c\", x);\n" ++
  "  instance a = C(UInt[8](1));\n}\nmodule M() {\n  instance b = C(1);\n}\n"
#guard (observed convSelf).length == 2
#guard (observed convSelf).getLast? == some "S019 3:3"

/-! At the fuel `fuel`, the elaboration of `src` stops at the charge of `units` at `pos`. -/
def pays (src : String) (fuel : Nat) (pos : String) (units : Nat) : Bool :=
  match Cli.load 4096 src with
  | .error _ => false
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked "M" with
    | .error _ => false
    | .ok (p, i, _, xs) =>
      match Elab.elaborate { fuel, depth := 1000 } checked Names.sha16 p i xs with
      | .ok _ => false
      | .error e =>
        s!"{e.code} {e.pos.line}:{e.pos.col} {e.msg}" ==
          s!"S015 {pos} the fuel cannot pay {units} unit(s); 0 remain; raise --fuel"

/-! The code, the position, and the message of the first error of the elaboration of `src`. -/
def failure (src : String) (fuel : Nat) : String :=
  match Cli.load 4096 src with
  | .error _ => "load"
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked "M" with
    | .error _ => "top"
    | .ok (p, i, _, xs) =>
      match Elab.elaborate { fuel, depth := 1000 } checked Names.sha16 p i xs with
      | .ok _ => "ok"
      | .error e => s!"{e.code} {e.pos.line}:{e.pos.col} {e.msg}"

-- The joins of two tuple types cost 2 units. A fuel below that names no count (issue #250).
def joinSrc : String := "module M() domains() {\n    let t = [(1, (2, 3)), (4, (5, 6))];\n}\n"
#guard failure joinSrc 61 ==
  "S015 2:13 the fuel cannot pay the joins of the types; 0 remain; raise --fuel"
#guard failure joinSrc 62 ==
  "S015 2:13 the fuel cannot pay the joins of the types; 1 remain; raise --fuel"

-- A scan that the fuel cannot pay names no count (issue #250).
def scanSrc : String :=
  "module M() domains() {\n" ++
  "    let s = \"abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz\";\n" ++
  "    let c = s[3];\n}\n"
#guard failure scanSrc 87 ==
  "S015 3:13 the fuel cannot pay the scan of the string; 0 remain; raise --fuel"
#guard failure scanSrc 90 ==
  "S015 3:13 the fuel cannot pay the scan of the string; 3 remain; raise --fuel"

def d16 : String := dMod "  diagnostic(\"depth\", 16);\n"
#guard observed d16 == ["(record 5 3 M () (string \"depth\") (int 16))", "ok"]
-- 1. The statement, then the node and the name of the call.
#guard pays d16 43 "5:3" 1 && pays d16 44 "5:3" 1 && pays d16 45 "5:3" 1
-- 2. The arguments from left to right: the node and the size of each.
#guard pays d16 46 "5:14" 1 && pays d16 47 "5:14" 6 && pays d16 53 "5:23" 1 &&
  pays d16 54 "5:23" 1
-- 3. The copies of the arguments.
#guard pays d16 55 "5:3" 7
-- 7. The measure charge of the value, then the 43 bytes of the record.
#guard pays d16 62 "5:3" 1 && pays d16 63 "5:3" 43
-- 8. The record goes into the list after its charges.
#guard observed d16 105 == ["S015 5:3"]
#guard observed d16 106 == ["(record 5 3 M () (string \"depth\") (int 16))", "S015 6:3"]

-- 4. The effect rule comes after the copies.
def dArm : String := dMod "  let z = if (c) { diagnostic(\"a\", 1) } else { 0 };\n"
#guard pays dArm 53 "5:20" 3
#guard elabAt dArm "M" 56 == "S016 5:20"
-- 5. The message comes after the copies.
def dMsg : String := dMod "  diagnostic(5, 1);\n"
#guard pays dMsg 50 "5:3" 2
#guard elabAt dMsg "M" 52 == "S010 5:3"
-- 6. A value that waits for its type comes after the copies and has no measure charge.
def dWait : String := dMod "  diagnostic(\"s\", []);\n"
#guard pays dWait 51 "5:3" 3
#guard elabAt dWait "M" 54 == "S010 5:3"
#guard elabOnly (dMod "  diagnostic(\"s\", [1, []]);\n") "M" == "S010 5:3"

-- The measure charge: the square of the size of an integer, and 1 for each container node.
def dBig : String := dMod "  diagnostic(\"n\", 340282366920938463463374607431768211456);\n"
#guard pays dBig 58 "5:3" 9 && pays dBig 67 "5:3" 76
#guard observed dBig 143 ==
  ["(record 5 3 M () (string \"n\") (int 340282366920938463463374607431768211456))", "S015 6:3"]
def dArr : String := dMod "  diagnostic(\"n\", [1, 2]);\n"
#guard pays dArr 62 "5:3" 3 && pays dArr 65 "5:3" 60
#guard observed dArr ==
  ["(record 5 3 M () (string \"n\") (array int ((int 1) (int 2))))", "ok"]

/-!
The message takes the `data` context. A register, a wire, an output, an own input, and a
hardware value are `S011`. A child input is `S017`. A memory, an instance, and a domain are
`S010`, and so is a static value that is not a `String`. The order is: the effect rule, the
message, then the value.
-/
def dRes (msg : String) : String :=
  "module C() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\n" ++
  "module M() {\n  input c: Bool;\n  input d: UInt[8];\n  output o: UInt[8];\n" ++
  "  reg r: UInt[8] = 0;\n  r := d;\n  wire w: UInt[8];\n  w := d;\n  mem m: [UInt[8]; 4];\n" ++
  "  write_port(m, 0, d, c);\n  let k = read_port(m, 0, c);\n  instance u = C();\n" ++
  "  u.a := c;\n" ++ s!"  diagnostic({msg}, 1);\n" ++ "  o := 0;\n}\n"
#guard elabOnly (dRes "r") "M" == "S011 19:3"
#guard elabOnly (dRes "w") "M" == "S011 19:3"
#guard elabOnly (dRes "o") "M" == "S011 19:3"
#guard elabOnly (dRes "d") "M" == "S011 19:3"
#guard elabOnly (dRes "d +% 1") "M" == "S011 19:3"
#guard elabOnly (dRes "u.q") "M" == "S011 19:3"
#guard elabOnly (dRes "u.a") "M" == "S017 19:3"
#guard elabOnly (dRes "m") "M" == "S010 19:3"
#guard elabOnly (dRes "u") "M" == "S010 19:3"
#guard elabOnly (dRes "clock") "M" == "S010 19:3"
#guard elabOnly (dRes "5") "M" == "S010 19:3"
#guard elabOnly (dRes "(1, 2)") "M" == "S010 19:3"
#guard elabOnly (dRes "[]") "M" == "S010 19:3"
#guard elabOnly (dRes "\"s\"") "M" == "ok 219"
#guard elabOnly (dMod "  wire e: ();\n  diagnostic(e, 1);\n") "M" == "S011 6:3"
-- A receiver call starts at its receiver, which is the message. A hardware scalar is `(hw <type>)`.
#guard observed (dMod "  \"r\".diagnostic(d);\n") ==
  ["(record 5 3 M () (string \"r\") (hw (uint 8)))", "ok"]
#guard said (dRes "r") == "the message of `diagnostic` is a static String, not a register"
#guard said (dRes "d") == "the message of `diagnostic` is a static String, not hardware UInt[8]"
#guard said (dRes "u.a") ==
  "the input `a` of `u` is a target only; read the value that you bind to it"
#guard said (dRes "m") == "`m` is a memory, not data; read a word with `read_port`"
#guard said (dRes "u") == "`u` is an instance, not data; read its outputs as `u.q`"
#guard said (dRes "5") == "the message of `diagnostic` is a String, not Int"
#guard said (dRes "[]") == "the message of `diagnostic` is a String, not `[]` without a type"
#guard said (dMod "  diagnostic(5, []);\n") == "the message of `diagnostic` is a String, not Int"
#guard said (dMod "  let z = if (c) { diagnostic(5, []) } else { 0 };\n") ==
  armEffect "diagnostic"
#guard said dWait == "the value of `diagnostic` needs a type; `[]` without a type"

/-!
The effect rule (section 9.4): `diagnostic` is `S016` in a hardware arm, also through a helper
and a function value. It is `S016` in each structural context too, with the text of the kind. A
`comptime fn` that the module body calls, `T(x)`, `comptime if`, and `comptime for` make records.
-/
def dg : String := "fn g() -> Nat { diagnostic(\"a\", 1); return 2; }\n"
#guard sRun "  let z = if (c) { diagnostic(\"b\", 1) } else { 0 };\n" dg == "S016 14:20"
#guard sRun "  let z = if (c) { UInt[8](g()) } else { 0 };\n" dg == "S016 1:17"
#guard sRun "  let fv = g;\n  let z = if (c) { UInt[8](fv()) } else { 0 };\n" dg == "S016 1:17"
-- Context 1: a type expression, also a parameter type.
#guard sRun "  let x: UInt[g()] = 0;\n" dg == "S016 1:17"
#guard sRun "  wire w: UInt[g()];\n  w := 0;\n" dg == "S016 1:17"
#guard sRun "  reg r: UInt[g()] = 0;\n  r := r;\n" dg == "S016 1:17"
#guard sRun "  let z = k();\n" (dg ++ "fn k() -> UInt[g()] { return 1; }\n") == "S016 1:17"
#guard sRun "  let z = k(1);\n" (dg ++ "fn k(b: UInt[g()]) -> Nat { return 1; }\n") == "S016 1:17"
-- Context 2: the expression forms that make a type.
#guard sRun "  let x = UInt[g()](0);\n" dg == "S016 1:17"
#guard sRun "  let t = [Bool; g()];\n" dg == "S016 1:17"
#guard sRun "  let t = fn (UInt[g()]) -> Bool;\n" dg == "S016 1:17"
-- Context 3: a `const` item and a `type` item at their first use, and a `type` statement.
#guard sRun "  let x = K;\n" (dg ++ "const K: Nat = g();\n") == "S016 1:17"
#guard sRun "  let x: T = 0;\n" (dg ++ "type T = UInt[g()];\n") == "S016 1:17"
#guard sRun "  type T = UInt[g()];\n" dg == "S016 1:17"
-- Context 4: a struct use.
#guard sRun "  let t = P[g()];\n" dg == "S016 1:17"
#guard sRun "  let t = Q[1];\n" (dg ++ "struct Q(comptime W: Nat) { a: UInt[g()] }\n") ==
  "S016 1:17"
-- Context 5: the word type and the depth of a `mem` statement.
#guard sRun "  mem q: [UInt[g()]; 4];\n" dg == "S016 1:17"
#guard sRun "  mem q: [UInt[8]; g()];\n" dg == "S016 1:17"
#guard said (dg ++ sMod "  let x: UInt[g()] = 0;\n") ==
  "a type or a constant has no graph effect such as `diagnostic`; call it before and use the " ++
  "result"
#guard said (dg ++ sMod "  let z = if (c) { UInt[8](g()) } else { 0 };\n") ==
  armEffect "diagnostic"
-- Not structural: each makes one record.
#guard observed (dg ++ sMod "  let x = UInt[8](g());\n") ==
  ["(record 1 17 M ((call g 14 19)) (string \"a\") (int 1))", "ok"]
#guard observed (dg ++ sMod "  comptime if (g() == 2) {}\n  comptime for i in 0..g() {}\n") ==
  ["(record 1 17 M ((call g 14 16)) (string \"a\") (int 1))",
   "(record 1 17 M ((call g 15 24)) (string \"a\") (int 1))", "ok"]
#guard observed (dg ++ sMod "  static_assert(g() == 2, \"m\");\n") ==
  ["(record 1 17 M ((call g 14 17)) (string \"a\") (int 1))", "ok"]
#guard observed ("comptime fn cg() -> Nat { diagnostic(\"c\", 1); return 2; }\n" ++
  sMod "  let z = cg();\n") ==
  ["(record 1 27 M ((call cg 14 11)) (string \"c\") (int 1))", "ok"]

/-!
The rendering of a value in a record (section 8.2) and its measure charge (section 5.4). A
hardware leaf is `(hw <type>)`. An aggregate is its container form with each part rendered, and
each container node charges 1. A reference renders as the value that it stands for. A part
without a hardware leaf is its static zero, with no charge. Each container part with a hardware
leaf charges 1. A handle renders by its kind and has no measure charge.
-/
-- A type value renders in its serialization form, also a handle type (section 7.1).
#guard Eval.Agg.render {} (.static (.type (.reg (.uint 8)))) == "(type (reg (uint 8)))"
#guard Eval.Agg.render {} (.static (.type (.inst 0 "C" #[.int 8]))) ==
  "(type (instance root C ((int 8))))"
#guard Eval.Agg.renderCharge {} (.static (.type (.mem .bool 4))) == 0

def dIn (ports body : String) (items : String := "") : String :=
  items ++ "module M() {\n  input c: Bool;\n  input d: UInt[8];\n" ++ ports ++
    "  output o: UInt[8];\n" ++ body ++ "  o := 0;\n}\n"

-- A hardware tuple: the tuple charges 1, and its static `1` charges 1.
def dTup : String := dMod "  diagnostic(\"t\", (d, 1, c));\n"
#guard observed dTup ==
  ["(record 5 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))", "ok"]
#guard pays dTup 64 "5:3" 2 && pays dTup 66 "5:3" 72
#guard observed dTup 138 ==
  ["(record 5 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))", "S015 6:3"]
#guard observed dTup 137 == ["S015 5:3"]

-- Nested aggregates with hardware and static leaves, and a reference with an empty part.
def dNest : String :=
  dIn "  input a: (UInt[2], [Bool; 0]);\n" "  diagnostic(\"n\", (a, [d, 2], (c, (3, true))));\n"
#guard observed dNest ==
  ["(record 6 3 M () (string \"n\") (tuple ((tuple ((hw (uint 2)) (array bool ()))) " ++
    "(array (uint 8) ((hw (uint 8)) (uint 8 2))) (tuple ((hw bool) (tuple ((int 3) " ++
    "(bool true))))))))", "ok"]
#guard pays dNest 137 "6:3" 7 && pays dNest 144 "6:3" 174

-- A reference: its empty parts are static zeros with no charge, so only the tuple charges.
def dRef : String := dIn "  input a: (UInt[8], [Bool; 0], ());\n" "  diagnostic(\"r\", a);\n"
#guard observed dRef ==
  ["(record 6 3 M () (string \"r\") (tuple ((hw (uint 8)) (array bool ()) (unit))))", "ok"]
#guard pays dRef 99 "6:3" 1 && pays dRef 100 "6:3" 77
#guard observed dRef 177 ==
  ["(record 6 3 M () (string \"r\") (tuple ((hw (uint 8)) (array bool ()) (unit))))", "S015 7:3"]
#guard observed dRef 176 == ["S015 6:3"]

-- A reference of a struct type renders as a record. An array of arrays renders each part.
def dRec : String :=
  dIn "  input a: P[4];\n" "  diagnostic(\"r\", a);\n"
    "struct P(comptime W: Nat) { x: UInt[W], y: (), z: Bool }\n"
#guard observed dRec ==
  ["(record 7 3 M () (string \"r\") (record (struct root P ((int 4))) " ++
    "((hw (uint 4)) (unit) (hw bool))))", "ok"]
#guard pays dRec 89 "7:3" 1 && pays dRec 90 "7:3" 98
#guard observed (dIn "  input a: [[UInt[4]; 2]; 2];\n" "  diagnostic(\"r\", a);\n") ==
  ["(record 6 3 M () (string \"r\") (array (array (uint 4) 2) ((array (uint 4) " ++
    "((hw (uint 4)) (hw (uint 4)))) (array (uint 4) ((hw (uint 4)) (hw (uint 4)))))))", "ok"]

/-!
A hardware enum renders as `(enum <type> <tag> <payload>)`: a static tag is an integer, and a
hardware leaf is `(hw (uint ..))`. A reference of an enum type renders each leaf as a hardware
leaf, and an empty payload has no part. The enum charges 1 as a container, and a static tag its
measure charge.
-/
def dOp : String := "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n"
def dEnumRef : String := dIn "  input a: Op;\n" "  diagnostic(\"r\", a);\n" dOp
#guard observed dEnumRef ==
  ["(record 7 3 M () (string \"r\") (enum (enum root Op ()) (hw (uint 2)) (hw (uint 8))))", "ok"]
#guard pays dEnumRef 102 "7:3" 1 && pays dEnumRef 103 "7:3" 83
def dEnumHw : String := dIn "" "  diagnostic(\"h\", Op::Load(d));\n" dOp
#guard observed dEnumHw ==
  ["(record 6 3 M () (string \"h\") (enum (enum root Op ()) 1 (hw (uint 8))))", "ok"]
#guard pays dEnumHw 107 "6:3" 2 && pays dEnumHw 109 "6:3" 71
def dFlag : String :=
  dIn "  input a: F;\n" "  diagnostic(\"r\", a);\n" "enum F: UInt[1] { A = 0 }\n"
#guard observed dFlag ==
  ["(record 7 3 M () (string \"r\") (enum (enum root F ()) (hw (uint 1))))", "ok"]
#guard observed (dIn "" "  diagnostic(\"s\", Op::Load(3));\n" dOp) ==
  ["(record 6 3 M () (string \"s\") (enum (enum root Op ()) 1 (uint 8 3)))", "ok"]

-- The response of `read_port`: a record of the word reference and of `valid`.
def dResp : String :=
  dIn "" ("  mem m: [(UInt[8], Bool); 4];\n  write_port(m, 0, (d, c), c);\n" ++
    "  diagnostic(\"k\", read_port(m, 0, c));\n")
#guard observed dResp ==
  ["(record 7 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (tuple " ++
    "((uint 8) bool))))) ((tuple ((hw (uint 8)) (hw bool))) (hw bool))))", "ok"]
#guard pays dResp 144 "7:3" 2 && pays dResp 146 "7:3" 148

-- Each handle kind. A handle has no measure charge, so its bytes follow its copy.
#guard observed ("module C() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\n" ++
  dIn "" ("  reg r: UInt[8] = 0;\n  r := d;\n  wire w: (Bool, UInt[2]);\n  w := (c, 1);\n" ++
    "  mem m: [UInt[8]; 4];\n  write_port(m, 0, d, c);\n  let k = read_port(m, 0, c);\n" ++
    "  instance u = C();\n  u.a := c;\n  diagnostic(\"r\", r);\n  diagnostic(\"w\", w);\n" ++
    "  diagnostic(\"o\", o);\n  diagnostic(\"m\", m);\n  diagnostic(\"u\", u);\n" ++
    "  diagnostic(\"i\", u.a);\n  diagnostic(\"q\", u.q);\n  diagnostic(\"clk\", clock);\n")) ==
  ["(record 19 3 M () (string \"r\") (reg (uint 8) r))",
   "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
   "(record 21 3 M () (string \"o\") (output (uint 8) o))",
   "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
   "(record 23 3 M () (string \"u\") (instance C u))",
   "(record 24 3 M () (string \"i\") (input bool u a))",
   "(record 25 3 M () (string \"q\") (hw bool))",
   "(record 26 3 M () (string \"clk\") (domain clock))", "ok"]
def dReg : String := dIn "" "  reg r: UInt[8] = 0;\n  r := d;\n  diagnostic(\"r\", r);\n"
#guard pays dReg 67 "7:3" 47
#guard observed dReg 114 == ["(record 7 3 M () (string \"r\") (reg (uint 8) r))", "S015 8:3"]
#guard observed dReg 113 == ["S015 7:3"]

-- A reference with 1000 leaves: 1 for the array and 1 for each tuple, then 24059 bytes.
def dWide : String := dIn "  input a: [(UInt[1],); 1000];\n" "  diagnostic(\"r\", a);\n"
#guard observed dWide 27143 ==
  ["(record 6 3 M () (string \"r\") (array (tuple ((uint 1))) (" ++
    " ".intercalate (List.replicate 1000 "(tuple ((hw (uint 1))))") ++ ")))", "S015 7:3"]
#guard pays dWide 2083 "6:3" 1001 && pays dWide 3084 "6:3" 24059
#guard observed dWide 27142 == ["S015 6:3"]

/-!
The emitted name and the call frames of a record (section 8.2). A frame names the item of the
callee and the position of its call, outermost first, also through a function value and a
receiver call. A receiver call starts at its receiver. The frames are part of the byte charge.
-/
def dDeep : String :=
  dMod "  let z = k(3);\n  diagnostic(\"m\", z);\n"
    ("fn h(x: Nat) -> Nat { diagnostic(\"h\", x); return x; }\n" ++
     "fn g(x: Nat) -> Nat { let f = h; return f(x); }\n" ++
     "fn k(x: Nat) -> Nat { return x.g(); }\n")
#guard observed dDeep ==
  ["(record 1 23 M ((call k 8 11) (call g 3 30) (call h 2 41)) (string \"h\") (int 3))",
   "(record 9 3 M () (string \"m\") (int 3))", "ok"]
#guard pays dDeep 86 "1:23" 80
#guard observed dDeep 165 == ["S015 1:23"]
#guard observed dDeep 166 ==
  ["(record 1 23 M ((call k 8 11) (call g 3 30) (call h 2 41)) (string \"h\") (int 3))",
   "S015 1:43"]

-- A child gives its records with its emitted name, before the rest of the parent. A done
-- instantiation gives no second record (decision F15).
def dKid : String :=
  "module C(comptime W: Nat) {\n  input a: UInt[W];\n  output q: UInt[W];\n" ++
  "  diagnostic(\"w\", W);\n  q := a;\n}\n" ++
  dMod ("  diagnostic(\"x\", 0);\n  instance u = C(8);\n  u.a := d;\n" ++
    "  diagnostic(\"y\", u);\n  instance v = C(8);\n  v.a := d;\n  instance s = C(2);\n" ++
    "  s.a := 1;\n  diagnostic(\"z\", s);\n")
#guard observed dKid ==
  ["(record 11 3 M () (string \"x\") (int 0))", "(record 4 3 C$8 () (string \"w\") (int 8))",
   "(record 14 3 M () (string \"y\") (instance C$8 u))",
   "(record 4 3 C$2 () (string \"w\") (int 2))",
   "(record 19 3 M () (string \"z\") (instance C$2 s))", "ok"]

-- `T(D)` has two children `T(D - 1)`; the second is done. `D = 30` gives exactly 31 records.
def dTree (d : Nat) : String :=
  "module T(comptime D: Nat) {\n  input a: Bool;\n  output q: Bool;\n  diagnostic(\"d\", D);\n" ++
  "  comptime if (D == 0) {\n    q := a;\n  } else {\n    instance u = T(D - 1);\n" ++
  "    instance v = T(D - 1);\n    u.a := a;\n    v.a := a;\n    q := u.q && v.q;\n  }\n}\n" ++
  dMod s!"  instance t = T({d});\n  t.a := c;\n"
#guard observed (dTree 30) ==
  (List.range 31).reverse.map (fun i => s!"(record 4 3 T${i} () (string \"d\") (int {i}))") ++
    ["ok"]

/-!
The command `observe` (section 8): the record lines, then the outcome. It runs the stages of
`elab`. A rejection at any stage prints the records before its first error, then the error
line, with the exit code 1. A success prints only the records, with the exit code 0.
-/
def observeOut (src : String) (fuel : Nat := 100000000) : String × UInt32 :=
  let (text, o) := Cli.observeText { budget := { fuel } } src "M"
  (text ++ (match o with
    | .ok t => t
    | .error e => Cli.errorLine e ++ "\n"
    | .reject l => l ++ "\n"
    | .usage m => s!"usage: {m}\n"
    | .defect m => s!"defect: {m}\n"), Cli.exitCode o)

#guard observeOut dDeep ==
  ("(record 1 23 M ((call k 8 11) (call g 3 30) (call h 2 41)) (string \"h\") (int 3))\n" ++
    "(record 9 3 M () (string \"m\") (int 3))\n", 0)
#guard observeOut (dMod "  let x = 1;\n") == ("", 0)
-- A parse error has no record.
#guard observeOut "module M() {\n  input c: Bool;\n  output o: Bool\n}\n" ==
  ("error[S001]: 4:1: expected `;`\n", 1)
-- An error after two records.
def dAfter : String :=
  dMod "  diagnostic(\"a\", 1);\n  diagnostic(\"b\", (c, 2));\n  diagnostic(5, 1);\n"
#guard observeOut dAfter ==
  ("(record 5 3 M () (string \"a\") (int 1))\n" ++
    "(record 6 3 M () (string \"b\") (tuple ((hw bool) (int 2))))\n" ++
    "error[S010]: 7:3: the message of `diagnostic` is a String, not Int\n", 1)
-- An `S018` at the end of the body comes after the records of the body.
#guard observeOut (dMod "  wire w: Bool;\n  diagnostic(\"a\", 1);\n") ==
  ("(record 6 3 M () (string \"a\") (int 1))\nerror[S018]: 5:3: `w` has no binding; " ++
    "bind it with `w := ...;`, or remove its declaration\n", 1)
-- An `S015` in the lowering keeps the records of the elaboration.
def dLow : String := dMod "  diagnostic(\"a\", d);\n" |>.replace "  o := 0;\n" "  o := d +% 1;\n"
#guard observeOut dLow 143 == ("(record 5 3 M () (string \"a\") (hw (uint 8)))\n", 0)
#guard observeOut dLow 142 ==
  ("(record 5 3 M () (string \"a\") (hw (uint 8)))\n" ++
    "error[S015]: 1:1: the fuel cannot pay 1 unit(s) of the lowering; 0 remain; raise --fuel\n",
      1)
#guard (Cli.usage.splitOn "|observe FILE --top T|").length == 2

/-!
An enum module argument (slice 3) needs its exact enum type, and it gives the digest form of the
emitted name (section 7.1). A binding of an enum port binds each leaf of the enum: `tag`, then
`payload` when `P` is not 0.
-/
def enumOps : String := "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n"
def enumArg (a : String) : String :=
  enumOps ++ "module M(comptime e: Op) {\n}\n" ++ s!"module T() \{\n  instance a = M({a});\n}\n"
#guard order (enumArg "Op()") "T" ==
  ["M$0h" ++ Names.sha16 "(instantiation root M ((enum (enum root Op ()) 0 (uint 8 0))))", "T"]
#guard cost (enumArg "1") "T" == "S010 5:3"
def enumLet (e : String) : String :=
  e ++ "module M() {\n  input a: Op;\n  output b: Bool;\n  let x = a;\n  b := true;\n}\n"
#guard names (enumLet enumOps) "M" "M" == ["x$tag", "x$payload"]
#guard names (enumLet "enum Op: UInt[2] { A = 0 }\n") "M" "M" == ["x$tag"]

/-! The text of a hardware value: each node with its operation and its operands. -/
def opText : Eval.Op → String
  | .ref p => s!"ref {Names.encode p.name}"
  | .pack w => s!"pack {w}"
  | .extract o w => s!"extract {o} {w}"
  | .share k => s!"share {k}"
  | .mux => "mux"
  | .resize => "resize"
  | .onehot => "onehot"
  | .rest => "rest"
  | _ => "op"

mutual
  def hwText : Eval.Hw → String
    | .node _ _ _ (.lit v) _ => v.serialize
    | .node _ _ _ op args => "(" ++ " ".intercalate (opText op :: hwTexts args) ++ ")"

  def hwTexts : List Eval.Hw → List String
    | [] => []
    | h :: hs => hwText h :: hwTexts hs
end

/-!
The number of nodes of a hardware value when each shared operand counts once. The lowering
binds such an operand once to a temporary (section 7.4). `seen` holds the marks that counted before.
-/
mutual
  def dagSize (seen : List Nat) : Eval.Hw → Nat × List Nat
    | .node _ _ _ op args =>
      match op with
      | .share k =>
        if seen.contains k then (1, seen)
        else
          let (n, s) := dagSizes (k :: seen) args
          (1 + n, s)
      | _ =>
        let (n, s) := dagSizes seen args
        (1 + n, s)

  def dagSizes (seen : List Nat) : List Eval.Hw → Nat × List Nat
    | [] => (0, seen)
    | h :: hs =>
      let (n, s) := dagSize seen h
      let (m, t) := dagSizes s hs
      (n + m, t)
end

/-! The named bindings of the top instantiation `M` with the text of their values. -/
def hwLets (src : String) : List String :=
  ((topBody src "M").map fun b =>
    b.lets.toList.map fun l => s!"{Names.encode l.path.name} = {hwText l.value}").getD []

def enumPair : String :=
  "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n"
def hwEnum (body : String) : String :=
  enumPair ++ "module M() {\n  input x: UInt[8];\n  input c: Bool;\n  input y: UInt[4];\n" ++
  "  input e: Op;\n  output o: Bool;\n" ++ body ++ "  o := true;\n}\n"
def hwUnits (body : String) : Nat := elabUnits (hwEnum body) "M"

/-!
A variant constructor with a hardware payload value gives a hardware enum. Its parts are the static
tag and one `pack` node of the payload leaves in packing order (D7). A static leaf is a constant,
and a leaf of a reference refers to its name, also through a struct and an array. A part without a
leaf, here `()`, adds no operand. The static tag needs no `let`, so the binding names only the
payload.
-/
#guard hwLets (hwEnum "  let a = Op::Load(x);\n") == ["a$payload = (pack 8 (ref x))"]
#guard hwLets (hwEnum "  let a = Op::Pair(c, y);\n") == ["a$payload = (pack 8 (ref c) (ref y))"]
#guard hwLets (hwEnum "  let a = Op::Pair(true, y);\n") ==
  ["a$payload = (pack 8 (bool true) (ref y))"]
#guard hwLets (hwEnum "  let a = Op::Pair(c, 3);\n") ==
  ["a$payload = (pack 8 (ref c) (uint 4 3))"]
#guard hwLets ("struct S { a: UInt[3], b: (Bool, ()) }\n" ++
  "enum E: UInt[1] { A(S, [UInt[2]; 2]) = 1 }\n" ++
  "module M() {\n  input s: S;\n  input v: [UInt[2]; 2];\n  output o: Bool;\n" ++
  "  let a = E::A(s, v);\n  o := true;\n}\n") ==
  ["a$payload = (pack 8 (ref s$a) (ref s$b$0e) (ref v$0e) (ref v$1e))"]

/-!
A hardware constructor charges as a static one: the payload values, their copies, and their typed
uses. Then the size of the result charges from the stored sizes. These are the node 1, the tag 1,
and the pack node 1 with the size of each leaf. `Op::Load(x)` thus charges 3 more than `Op::Add`:
the name 1, its copy 1, and the larger result 4. `Op::Pair(c, y)` charges 6 more: two names, two
copies, and the result 5. The pack node makes no hardware operation here, because the lowering
charges each core node of a pack (section 7.4).
-/
#guard hwUnits "  let a = Op::Load(x);\n" == hwUnits "  let a = Op::Add;\n" + 3
#guard hwUnits "  let a = Op::Pair(c, y);\n" == hwUnits "  let a = Op::Add;\n" + 6
#guard hwUnits "  let a = Op::Load(3);\n" == hwUnits "  let a = Op::Add;\n" + 5
#guard elabOnly (hwEnum "  let a = Op::Load(y);\n") "M" == "S010 8:11"

/-!
`reinterpret(UInt[W + P], e)` of a hardware enum packs its leaves `tag` and `payload` (section
7.4). A reference gives both leaves by name. `reinterpret(E, b)` makes `(extract b 0 W)` and
`(extract b W P)`. Both leaves read `b`, so `b` gets one mark of a shared operand, unless it is a
core name or a constant (G8). With `P` 0, no conversion makes a node. A hardware conversion
charges only its node, its name, its arguments, and their copies: 10 more than `Op::Add`.
-/
#guard hwLets (hwEnum "  let a = reinterpret(UInt[10], e);\n") ==
  ["a = (pack 10 (ref e$tag) (ref e$payload))"]
#guard hwUnits "  let a = reinterpret(UInt[10], e);\n" == hwUnits "  let a = Op::Add;\n" + 10
#guard hwLets (hwEnum "  let a = reinterpret(UInt[10], Op::Load(x));\n") ==
  ["a = (pack 10 (uint 2 1) (pack 8 (ref x)))"]
#guard hwLets (hwEnum "  let b = resize(UInt[10], x);\n  let a = reinterpret(Op, b);\n") ==
  ["b = (resize (ref x))", "a$tag = (extract 0 2 (ref b))", "a$payload = (extract 2 8 (ref b))"]
#guard hwLets (hwEnum "  let a = reinterpret(Op, resize(UInt[10], x));\n") ==
  ["a$tag = (extract 0 2 (share 0 (resize (ref x))))",
   "a$payload = (extract 2 8 (share 0 (resize (ref x))))"]
def flagE (body : String) : String :=
  "enum E: UInt[2] { A = 0, B = 1 }\nmodule M() {\n  input c: Bool;\n  input e: E;\n" ++
  "  input u: UInt[2];\n  output o: Bool;\n" ++ body ++ "  o := true;\n}\n"
#guard hwLets (flagE "  let a = reinterpret(UInt[2], e);\n  let b = reinterpret(E, u +% 1);\n") ==
  ["a = (ref e$tag)", "b$tag = (op (ref u) (uint 2 1))"]
#guard elabOnly (hwEnum "  let a = reinterpret(Op, x);\n") "M" == "S010 8:11"
#guard elabOnly (hwEnum "  let a = reinterpret(UInt[8], e);\n") "M" == "S010 8:11"

/-!
A hardware enum value has the depth 3, as a static one has (section 5.5). A constructor with a
hardware payload and a hardware unpack check it before the value exists: `S015` at the node.
-/
#guard (cost (hwEnum "  let a = Op::Load(x);\n") "M" (depth := 3)).startsWith "total"
#guard cost (hwEnum "  let a = Op::Load(x);\n") "M" (depth := 2) == "S015 8:11"
#guard (cost (hwEnum "  let a = reinterpret(Op, resize(UInt[10], x));\n") "M"
  (depth := 3)).startsWith "total"
#guard cost (hwEnum "  let a = reinterpret(Op, resize(UInt[10], x));\n") "M" (depth := 2) ==
  "S015 8:11"

/-!
A read of an aggregate port, a register, a wire, or a child output makes a value. Its depth is
the depth of its zero, 3 for an enum or a struct of scalars (section 5.5). The read checks it. A
port that no read uses makes no value. A hardware `if` of two port reads fails at the first read.
-/
#guard (cost (hwEnum "  let a = e;\n") "M" (depth := 3)).startsWith "total"
#guard cost (hwEnum "  let a = e;\n") "M" (depth := 2) == "S015 8:11"
#guard (cost (hwEnum "  let a = if (c) { e } else { e };\n") "M" (depth := 3)).startsWith "total"
#guard cost (hwEnum "  let a = if (c) { e } else { e };\n") "M" (depth := 2) == "S015 8:20"
#guard (cost (hwEnum "") "M" (depth := 2)).startsWith "total"

def structPort (body : String) : String :=
  "struct S { a: UInt[8] }\nmodule M() {\n  input c: Bool;\n  input s: S;\n  input t: S;\n" ++
  "  wire w: S;\n  output o: S;\n" ++ body ++ "}\n"
#guard (cost (structPort "  w := s;\n  o := w;\n") "M" (depth := 3)).startsWith "total"
#guard cost (structPort "  w := s;\n  o := w;\n") "M" (depth := 2) == "S015 8:8"
#guard cost (structPort "  o := w;\n  w := s;\n") "M" (depth := 2) == "S015 8:3"
#guard (cost (structPort "  w := s;\n  o := if (c) { s } else { t };\n") "M"
  (depth := 3)).startsWith "total"
#guard cost (structPort "  w := t;\n  o := if (c) { s } else { t };\n") "M" (depth := 2) ==
  "S015 8:8"

/-!
A binder of a `match` arm makes a value from the payload bits, so it checks its depth at the
binder. Here the payload `[S; 1]` has the depth 3, and its value the depth 4.
-/
def deepBinder : String :=
  "struct S { a: UInt[8] }\nenum E: UInt[1] { A = 0, B([S; 1]) = 1 }\nmodule M() {\n" ++
  "  input u: UInt[9];\n  output o: UInt[8];\n" ++
  "  o := match (reinterpret(E, u)) { E::B(x) => x[0].a, _ => 0 };\n}\n"
#guard (cost deepBinder "M" (depth := 4)).startsWith "total"
#guard cost deepBinder "M" (depth := 3) == "S015 6:41"

/-!
A read of a child output, a register, and an empty input checks the depth of its zero too
(`readRef`). The child elaborates at its `instance` statement one level deeper, so its port type
fails first. The reset value `S()` of a register checks the same depth before a read. An empty
input makes its zero only at a read, so it fails at the name.
-/
def childOut : String :=
  "struct S { a: UInt[8] }\nmodule C() {\n  input i: S;\n  output q: S;\n  q := i;\n}\n" ++
  "module M() {\n  input s: S;\n  output o: S;\n  instance u = C();\n  u.i := s;\n  o := u.q;\n}\n"
#guard (cost childOut "M" (depth := 3)).startsWith "total"
#guard cost childOut "M" (depth := 2) == "S015 3:12"
def regRead : String :=
  "struct S { a: UInt[8] }\nmodule M() {\n  output o: S;\n  reg r: S = S();\n  r := r;\n" ++
  "  o := r;\n}\n"
#guard (cost regRead "M" (depth := 3)).startsWith "total"
#guard cost regRead "M" (depth := 2) == "S015 4:14"
def emptyRead : String := "struct S { a: () }\nmodule M() {\n  input x: S;\n  let y = x;\n}\n"
#guard (cost emptyRead "M" (depth := 3)).startsWith "total"
#guard cost emptyRead "M" (depth := 2) == "S015 4:11"

/-!
Nested conversions stay linear (G8). Each `reinterpret(E, b)` marks its operand once, so `k` nested
round trips make `k` marks. The lowering binds each mark once. With each mark counted once, a round
trip adds 5 nodes: a `pack`, two `extract` nodes, and two uses of one mark. Without the marks, the
leaves would hold `2^k` copies of `x`.
-/
def roundTrips : Nat → String → String
  | 0, b => b
  | k + 1, b => s!"reinterpret(Op, reinterpret(UInt[10], {roundTrips k b}))"
def tripNodes (k : Nat) : Nat :=
  match topBody (hwEnum s!"  let a = {roundTrips k "reinterpret(Op, resize(UInt[10], x))"};\n")
      "M" with
  | some b => (dagSizes [] (b.lets.toList.map (·.value))).1
  | none => 0
#guard tripNodes 0 == 6
#guard tripNodes 1 == 6 + 5
#guard tripNodes 20 == 6 + 20 * 5

/-!
The charge of nested round trips is linear too. Each mark charges the size of its operand once.
A value that holds the mark counts it as a core name, so each round trip adds 29 units, up to
`k = 30`.
-/
def tripUnits (k : Nat) : Nat :=
  hwUnits s!"  let a = {roundTrips k "reinterpret(Op, resize(UInt[10], x))"};\n"
#guard (List.range 30).all fun k => tripUnits (k + 1) == tripUnits k + 29
#guard tripUnits 30 == 1011

/-!
A hardware `if` with enum arms joins the two enum types, 1 plus 1. Then it walks them as a container
pair (section 7.4): the root, then `tag`, then `payload`, 1 each. A static enum opens into its
parts. Each leaf pair makes one `mux`, also a pair of two static leaves. With `P` 0, the walk visits
only the root and `tag`. Thus `if (c) { Op::Add } else { e }` charges its node, `c`, the arms 5, the
join 2, the walk 3, and two `mux` nodes 8. Two different enums, and an enum and another type, have
no join (`S010`).
-/
#guard hwLets (hwEnum "  let a = if (c) { Op::Load(x) } else { e };\n") ==
  ["a$tag = (mux (ref c) (uint 2 1) (ref e$tag))",
   "a$payload = (mux (ref c) (pack 8 (ref x)) (ref e$payload))"]
#guard hwUnits "  let a = if (c) { Op::Add } else { e };\n" + 4 ==
  hwUnits "  let a = Op::Add;\n" + (1 + 1 + 5 + 2 + 3 + 8)
#guard hwLets (hwEnum "  let a = if (c) { Op::Add } else { Op::Load(3) };\n") ==
  ["a$tag = (mux (ref c) (uint 2 0) (uint 2 1))",
   "a$payload = (mux (ref c) (uint 8 0) (uint 8 3))"]
#guard hwLets (flagE "  let a = if (c) { E::A } else { e };\n") ==
  ["a$tag = (mux (ref c) (uint 2 0) (ref e$tag))"]
#guard hwLets (hwEnum "  let a = if (x == 1) { Op::Load(x) } else { e };\n") ==
  ["a$tag = (mux (share 0 (op (ref x) (uint 8 1))) (uint 2 1) (ref e$tag))",
   "a$payload = (mux (share 0 (op (ref x) (uint 8 1))) (pack 8 (ref x)) (ref e$payload))"]

/-!
A shared condition charges once. `!c` charges its node 1 and its hardware operation 2, and its
mark charges the size 2 of `(! c)`. A copy of the result counts the mark as the core name `c`.
-/
def ifC (c : String) : String := s!"  let a = if ({c}) \{ Op::Load(x) } else \{ e };\n"
#guard hwUnits (ifC "!c") == hwUnits (ifC "c") + 3 + 2
#guard hwUnits (ifC "!c" ++ "  let b = a;\n") - hwUnits (ifC "!c") ==
  hwUnits (ifC "c" ++ "  let b = a;\n") - hwUnits (ifC "c")
#guard elabOnly (hwEnum "  let a = if (c) { Op::Add } else { 1 };\n") "M" == "S010 8:11"
#guard elabOnly ("enum F: UInt[2] { A = 0 }\n" ++
  hwEnum "  let a = if (c) { Op::Add } else { F::A };\n") "M" == "S010 9:11"

/-!
Two static enums in a static pair of a hardware `if`, here in two lists, compare by their tags
and payloads. Different enums are `S011` at the `if`, as each static pair with different sides,
and equal ones give the value.
-/
def enumLists (b : String) : String :=
  hwEnum ("  let mut p = list(Op);\n  push(p, Op::Add);\n  let mut q = list(Op);\n" ++
    s!"  push(q, {b});\n  let k = if (c) \{ p } else \{ q };\n")
#guard elabOnly (enumLists "Op::Load(1)") "M" == "S011 12:11"
#guard elabOnly (enumLists "Op::Pair(false, 0)") "M" == "S011 12:11"
#guard (elabOnly (enumLists "Op::Add") "M").startsWith "ok"

/-!
A register of an enum type takes a static enum as its reset value, and a `:=` binding takes a
hardware enum. A wire of an enum type reads as a reference to its leaves.
-/
#guard ((topBody (hwEnum "  reg r: Op = Op::Pair(true, 3);\n  r := Op::Load(x);\n") "M").map
  (·.regs.toList.map (·.init.serialize))) == some ["(enum (enum root Op ()) 2 (uint 8 7))"]
#guard hwLets
  (hwEnum "  wire w: Op;\n  w := Op::Pair(c, y);\n  let a = reinterpret(UInt[10], w);\n") ==
  ["a = (pack 10 (ref w$tag) (ref w$payload))"]

/-!
A hardware `match` gives one `onehot` node for each leaf: the selects, then the values. The select
of `_` is a `rest` node over the other selects.
-/
#guard hwLets (hwEnum "  let a = match (c) { true => x, _ => resize(UInt[8], y) };\n") ==
  ["a = (onehot (share 0 (op (ref c) (bool true))) (rest (share 0 (op (ref c) (bool true)))) " ++
    "(ref x) (resize (ref y)))"]

/-!
A handle type is not hardware data (section 5.1). A port, a `reg`, a `wire`, and a memory word of
a handle type are `S010` at the statement, and the text names the data type to use. A container
that holds a handle type keeps the text of its position.
-/
def handleMods : String := "module D() {\n}\n"
#guard cost (memBody "  reg r: Reg[UInt[8]] = 0;\n") "M" == "S010 2:3"
#guard said (memBody "  reg r: Reg[UInt[8]] = 0;\n") ==
  "`Reg[UInt[8]]` is a handle type, not hardware data; use its data type `UInt[8]`"
#guard cost (memBody "  wire w: Wire[Bool];\n") "M" == "S010 2:3"
#guard cost (memBody "  input i: Input[Bool];\n") "M" == "S010 2:3"
#guard said (handleMods ++ memBody "  output o: Instance[D];\n") ==
  "`Instance[D]` is a handle type, not hardware data; an instance has no data type, so read " ++
    "its outputs as `u.q`"
#guard cost (memBody "  mem m: [Reg[UInt[8]]; 4];\n") "M" == "S010 2:3"
#guard said (memBody "  mem m: [Reg[UInt[8]]; 4];\n") ==
  "`Reg[UInt[8]]` is a handle type, not hardware data; use its data type `UInt[8]`"
#guard said (memBody "  wire w: [Reg[Bool]; 0];\n") ==
  "a port, a register, and a wire need a hardware data type, not [Reg[Bool]; 0]"

/-! The memory texts of a `mem` statement name their fix (section 6.2). -/
#guard said (memBody "  mem m: [Int; 4];\n") ==
  "a memory word is a nonempty hardware data type, not `Int`; use a type with at least one " ++
    "bit, for example `UInt[8]`"
#guard said (memBody "  mem m: [[UInt[65536]; 2]; 4];\n") ==
  "a memory word has at most 65536 bits, not 131072; split the word over more than one memory"
#guard said (memBody "  mem m: [Bool; 0];\n") ==
  "a memory depth is 1 to 16777216, not 0; use a depth in this range"
#guard said (memBody "  mem m: [Bool; true];\n") ==
  "a memory depth is a static integer, not a value of `Bool`; write an integer, for example `16`"
#guard said (memBody "  mem m: [Bool; []];\n") ==
  "a memory depth is a static integer, not `[]`; write an integer, for example `16`"
#guard said (memBody "  input x: UInt[4];\n  let h = x;\n  mem m: [Bool; h];\n") ==
  "a memory depth is static, not a value of `UInt[4]`; compute the depth from static values"

/-!
A hardware argument of a handle type is at the start of the use. It is not a type (`S010`), or
a memory depth that is not static (`S011`). An argument of `Instance` is static (`S011`).
-/
#guard cost (memBody "  input x: UInt[4];\n  let h = x;\n  let t = Reg[h];\n") "M" == "S010 4:11"
#guard said (memBody "  input x: UInt[4];\n  let h = x;\n  let t = Reg[h];\n") ==
  "the first argument of `Reg` is a type, not a value of `UInt[4]`; write a type, for example " ++
    "`Reg[UInt[8]]`"
#guard cost (memBody "  input x: UInt[4];\n  let h = x;\n  let t = Mem[Bool, h];\n") "M" ==
  "S011 4:11"
#guard (cost (memBody "  input x: UInt[4];\n  let h = 4;\n  let t = Mem[Bool, h];\n") "M")
  |>.startsWith "total"
#guard cost ("module C(comptime W: Nat) {\n}\n" ++
  memBody "  input x: UInt[4];\n  let h = x;\n  let t = Instance[C, h];\n") "M" == "S011 6:11"
#guard (cost ("module C(comptime W: Nat) {\n}\n" ++
  memBody "  input x: UInt[4];\n  let h = 4;\n  let t = Instance[C, h];\n") "M").startsWith "total"
/-! A parameter type error of `Instance[M, args]` is at its own node. -/
#guard cost ("module B(comptime x: UInt[0]) {\n}\n" ++ memBody "  let t = Instance[B, 1];\n") "M" ==
  "S012 1:22"

/-!
A typed `let` at a handle type keeps the handle, and it reads nothing (section 5.4). Thus `a := i`
binds `r` through `a`. An assignment to a `let mut` local of a handle type changes the handle,
so `b := i` binds `r`, not `q`. The handle of an instance holds its type `Instance[M, args]`, and
the handle of a child input its type `Input[T]`.
-/
def handleLets (body : String) : String :=
  "module C(comptime W: Nat) {\n  input x: UInt[8];\n}\n" ++
  "struct S { a: Reg[UInt[8]] }\n" ++
  "fn g(x: Reg[UInt[8]]) -> Bool { return true; }\n" ++
  "fn h(mut x: Reg[UInt[8]]) -> Bool { return true; }\n" ++
  "module M() {\n  input i: UInt[8];\n  output o: UInt[8];\n  reg r: UInt[8] = 0;\n" ++
  "  reg q: UInt[8] = 0;\n  reg s: UInt[4] = 0;\n  wire w: UInt[8];\n" ++
  "  instance u = C(8);\n  o := i;\n  q := i;\n  s := 0;\n  w := i;\n  u.x := i;\n" ++ body ++ "}\n"
#guard exact (handleLets "  let a: Reg[UInt[8]] = r;\n  a := i;\n") "M" 353
#guard exact (handleLets "  let mut b: Reg[UInt[8]] = q;\n  b = r;\n  b := i;\n") "M" 356
#guard exact
  (handleLets "  let e: Instance[C, 8] = u;\n  let f: Input[UInt[8]] = u.x;\n  r := i;\n") "M" 365

/-!
A handle of another handle type, an own input, and an own output are `S010` at the statement
(section 6.2). The value text names the handle type of the handle. The copy charges 1 before the
compare, so one unit less stops at the statement.
-/
def typedText (t a : String) : String :=
  s!"expected `{t}`, but the value is {a}; a handle type takes only a handle of exactly this " ++
    "type, so give such a handle or change the type"
def boxText (t a : String) : String :=
  s!"expected `{t}`, but the value is {a}; a value of `{t}` takes only handles of exactly its " ++
    "handle types, so give such a value or change the type"
def ownText : String :=
  "`o` is an output, and an output has no handle type; use `o` directly as data"
#guard said (handleLets "  let a: Reg[UInt[8]] = s;\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"
#guard cost (handleLets "  let a: Reg[UInt[8]] = s;\n") "M" (fuel := 161) == "S010 20:3"
#guard cost (handleLets "  let a: Reg[UInt[8]] = s;\n") "M" (fuel := 160) == "S015 20:3"
#guard said (handleLets "  let a: Reg[UInt[8]] = w;\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Wire[UInt[8]]`"
#guard said (handleLets "  let a: Reg[UInt[8]] = i;\n") ==
  typedText "Reg[UInt[8]]" "a value of `UInt[8]`"
#guard said (handleLets "  let a: Reg[UInt[8]] = o;\n") == ownText
#guard cost (handleLets "  let a: Reg[UInt[8]] = o;\n") "M" (fuel := 161) == "S010 20:3"
#guard cost (handleLets "  let a: Reg[UInt[8]] = o;\n") "M" (fuel := 160) == "S015 20:3"
#guard said (handleLets "  let a: Instance[C, 9] = u;\n") ==
  typedText "Instance[C, 9]" "a handle of `Instance[C, 8]`"
#guard cost (handleLets "  let a: Instance[C, 9] = u;\n") "M" (fuel := 158) == "S010 20:3"
#guard cost (handleLets "  let a: Instance[C, 9] = u;\n") "M" (fuel := 157) == "S015 20:3"
#guard said (handleLets "  let a: Input[UInt[4]] = u.x;\n") ==
  typedText "Input[UInt[4]]" "a handle of `Input[UInt[8]]`"
#guard said (memBody "  mem m: [UInt[8]; 4];\n  let a: Mem[UInt[8], 2] = m;\n") ==
  typedText "Mem[UInt[8], 2]" "a handle of `Mem[UInt[8], 4]`"
#guard cost (memBody "  mem m: [UInt[8]; 4];\n  let a: Mem[UInt[8], 2] = m;\n") "M" (fuel := 53) ==
  "S010 3:3"
#guard cost (memBody "  mem m: [UInt[8]; 4];\n  let a: Mem[UInt[8], 2] = m;\n") "M" (fuel := 52) ==
  "S015 3:3"
/-! The same handle type passes, and the compare adds no charge. -/
#guard cost (memBody "  mem m: [UInt[8]; 4];\n  let a: Mem[UInt[8], 4] = m;\n") "M" (fuel := 53) ==
  "S018 2:3"

/-! The arguments of `Instance` take the typed uses of the `instance` statement: one key. -/
def oneKey : String :=
  "module C(comptime W: UInt[8]) {\n}\nmodule M() {\n  instance u = C(UInt[8](1));\n" ++
  "  let a: Instance[C, 1] = u;\n  let b: Instance[C, 2] = u;\n}\n"
#guard said oneKey == typedText "Instance[C, 2]" "a handle of `Instance[C, 1]`"
#guard cost oneKey "M" (fuel := 123) == "S010 6:3"
#guard cost oneKey "M" (fuel := 122) == "S015 6:3"

/-! An assignment to a `let mut` local of a handle type has the same check at the assignment. -/
#guard said (handleLets "  let mut b: Reg[UInt[8]] = r;\n  b = w;\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Wire[UInt[8]]`"
#guard cost (handleLets "  let mut b: Reg[UInt[8]] = r;\n  b = w;\n") "M" (fuel := 164) ==
  "S010 21:3"
#guard cost (handleLets "  let mut b: Reg[UInt[8]] = r;\n  b = w;\n") "M" (fuel := 163) ==
  "S015 21:3"
#guard said (handleLets "  let mut b: Reg[UInt[8]] = r;\n  b = o;\n") == ownText

/-!
A `let mut` local without a type that holds a handle has its handle type. Thus an assignment to
it is the same typed use (section 5.4). The same handle type passes, and another value is `S010`
at the assignment. A local that holds an own output takes only an own output of its data type. The
copy charges 1 before the check, so one unit less stops at the assignment.
-/
def heldText (a : String) : String :=
  s!"the local holds the output `o`, so it takes only an output of `UInt[8]`, not {a}; use " ++
    "the output `o` directly"
#guard exact (handleLets "  let mut a = q;\n  a = r;\n  a := i;\n") "M" 345
#guard exact (handleLets "  let mut a = u;\n  a = u;\n  r := i;\n") "M" 345
#guard exact (handleLets "  let mut a = o;\n  a = o;\n  r := i;\n") "M" 345
#guard said (handleLets "  let mut a = r;\n  a = s;\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"
#guard cost (handleLets "  let mut a = r;\n  a = s;\n") "M" (fuel := 153) == "S010 21:3"
#guard cost (handleLets "  let mut a = r;\n  a = s;\n") "M" (fuel := 152) == "S015 21:3"
#guard said (handleLets "  let mut a = u;\n  a = w;\n") ==
  typedText "Instance[C, 8]" "a handle of `Wire[UInt[8]]`"
#guard said (handleLets "  let mut a = r;\n  a = 5;\n") ==
  typedText "Reg[UInt[8]]" "a value of `Int`"
#guard said (memBody "  mem m: [UInt[8]; 4];\n  let mut a = m;\n  a = m;\n  a = 5;\n") ==
  typedText "Mem[UInt[8], 4]" "a value of `Int`"
#guard said (handleLets "  let mut a = o;\n  a = r;\n") == heldText "a handle of `Reg[UInt[8]]`"
#guard cost (handleLets "  let mut a = o;\n  a = r;\n") "M" (fuel := 153) == "S010 21:3"
#guard cost (handleLets "  let mut a = o;\n  a = r;\n") "M" (fuel := 152) == "S015 21:3"
#guard said (handleLets "  let mut a = o;\n  a = 5;\n") == heldText "a value of `Int`"

/-!
An argument at a handle type gets the typed use at a handle type, at the call (section 5.6). A
`mut` actual needs the exact type of its formal, with the same text, and an own output there
names its fix. The copy charges first, so one unit less stops at the call. A `push` element has
the same check at the call.
-/
#guard exact (handleLets "  let a = g(r);\n  r := i;\n") "M" 361
#guard said (handleLets "  let a = g(s);\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"
#guard cost (handleLets "  let a = g(s);\n") "M" (fuel := 163) == "S010 20:11"
#guard cost (handleLets "  let a = g(s);\n") "M" (fuel := 162) == "S015 20:11"
#guard exact (handleLets "  let mut b: Reg[UInt[8]] = r;\n  let a = h(b);\n  r := i;\n") "M" 375
#guard said (handleLets "  let mut b = s;\n  let a = h(b);\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"
#guard cost (handleLets "  let mut b = s;\n  let a = h(b);\n") "M" (fuel := 165) == "S010 21:11"
#guard cost (handleLets "  let mut b = s;\n  let a = h(b);\n") "M" (fuel := 164) == "S015 21:11"
#guard said (handleLets "  let mut b = o;\n  let a = h(b);\n") == ownText

/-!
A `mut` actual of a handle type at a formal of a data type keeps the `mut` text. Only the type of
the formal decides (section 5.6).
-/
def dataFormal : String :=
  "fn d(mut x: UInt[8]) -> Bool { return true; }\n" ++
    handleLets "  let mut b = r;\n  let a = d(b);\n"
#guard said dataFormal == "a `mut` actual has the type Reg[UInt[8]], but its formal has UInt[8]"
#guard cost dataFormal "M" (fuel := 160) == "S010 22:11"
#guard cost dataFormal "M" (fuel := 159) == "S015 22:11"
#guard said (handleLets "  let mut xs = list(Reg[UInt[8]]);\n  xs.push(s);\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"
#guard cost (handleLets "  let mut xs = list(Reg[UInt[8]]);\n  xs.push(s);\n") "M"
  (fuel := 169) == "S010 21:3"
#guard cost (handleLets "  let mut xs = list(Reg[UInt[8]]);\n  xs.push(s);\n") "M"
  (fuel := 168) == "S015 21:11"

/-!
Formals and results of container types with the handle flag (section 5.6). `k` takes a tuple
with a handle position. `sw` swaps two handles of a `mut` tuple. `pr` returns a handle and a
read. `rt` returns a handle field of a struct. `gt` grows a list of types in a tuple with a
handle.
-/
def handleFormals (body : String) : String :=
  "fn k(x: (UInt[8], Reg[UInt[8]])) -> Bool { return true; }\n" ++
  "fn sw(mut x: (Reg[UInt[8]], Reg[UInt[8]])) -> Bool {\n" ++
  "  let t = x.0;\n  x.0 = x.1;\n  x.1 = t;\n  return true;\n}\n" ++
  "fn pr(x: Reg[UInt[8]]) -> (Reg[UInt[8]], UInt[8]) { return (x, read(x)); }\n" ++
  "fn rt(x: S) -> Reg[UInt[8]] { return x.a; }\n" ++
  "fn bad() -> Reg[UInt[8]] { return 3; }\n" ++
  "fn gt(mut x: (Reg[UInt[8]], List[Type])) -> Bool {\n" ++
  "  x.1.push([[[[UInt[8]; 1]; 1]; 1]; 1]);\n  return true;\n}\n" ++
  handleLets body

/-!
A handle position of a container type needs a handle of exactly its type (section 5.4). The text
names the type of the position and the leaf at it. All checks come first in packing order, then
the conversion charge, then the fit checks. Thus `(300, s)` is `S010`, and `(300, r)` is `S012`
after the charge. Nothing reads a handle at a data position. It is `S010` with the text "Handle
at a data leaf", and `read` in the literal is the fix.
-/
#guard exact (handleFormals "  let a = k((3, r));\n  r := i;\n") "M" 400
#guard said (handleFormals "  let a = k((300, s));\n") ==
  typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"
#guard cost (handleFormals "  let a = k((300, s));\n") "M" (fuel := 196) == "S010 34:11"
#guard cost (handleFormals "  let a = k((300, s));\n") "M" (fuel := 195) == "S015 34:11"
#guard said (handleFormals "  let a = k((300, r));\n") == "300 does not fit UInt[8]"
#guard cost (handleFormals "  let a = k((300, r));\n") "M" (fuel := 202) == "S012 34:11"
#guard cost (handleFormals "  let a = k((300, r));\n") "M" (fuel := 201) == "S015 34:11"
#guard said (handleFormals "  let a = k((r, r));\n") ==
  "expected `UInt[8]`, but the value is a handle of `Reg[UInt[8]]`; a literal element keeps " ++
    "its handle, so read it in the literal, for example `(r, read(r))`"
#guard cost (handleFormals "  let a = k((r, r));\n") "M" (fuel := 195) == "S010 34:11"
#guard cost (handleFormals "  let a = k((r, r));\n") "M" (fuel := 194) == "S015 34:11"
#guard (cost (handleFormals "  let a = k((read(r), r));\n  r := i;\n") "M").startsWith "total"

/-!
A `mut` formal of a container type passes the handles in and writes them back. A place of
another type is `S010` at the call, with the type of the formal and the value of the place.
-/
#guard exact (handleFormals "  let mut p = (r, q);\n  let a = sw(p);\n  r := i;\n") "M" 422
#guard said (handleFormals "  let mut p = (r, s);\n  let a = sw(p);\n") ==
  boxText "(Reg[UInt[8]], Reg[UInt[8]])" "a value of `(Reg[UInt[8]], Reg[UInt[4]])`"
#guard cost (handleFormals "  let mut p = (r, s);\n  let a = sw(p);\n") "M" (fuel := 202) ==
  "S010 35:11"
#guard cost (handleFormals "  let mut p = (r, s);\n  let a = sw(p);\n") "M" (fuel := 201) ==
  "S015 35:11"

/-!
A result of a handle type keeps the handle, and a `return` of another value is `S010` at the
statement. A result binds only its hardware leaves to `0ret` (section 7.3), so a handle result
binds nothing.
-/
#guard exact (handleFormals "  let a = pr(r);\n  r := a.1;\n") "M" 430
#guard names (handleFormals "  let a = pr(r);\n  r := a.1;\n") "M" "M" ==
  ["pr$0c$0ret$1e", "a$1e", "r", "q", "s", "w", "u"]
#guard exact (handleFormals "  let a = rt(S(r));\n  a := i;\n") "M" 387
#guard names (handleFormals "  let a = rt(S(r));\n  a := i;\n") "M" "M" ==
  ["r", "q", "s", "w", "u"]
#guard said (handleFormals "  let a = bad();\n") == typedText "Reg[UInt[8]]" "a value of `Int`"
#guard cost (handleFormals "  let a = bad();\n") "M" (fuel := 166) == "S010 10:28"
#guard cost (handleFormals "  let a = bad();\n") "M" (fuel := 165) == "S015 10:28"

/-!
The write-back of a value of a type with the handle flag checks the depth of the value. A static
value has the same check (section 5.4). The list of `gt` grows in the callee. Thus the depth 7
passes the `push` and stops at the write-back, at the call. The depth 8 passes.
-/
def growing : String :=
  handleFormals "  let mut t = ((r, list(Type)),);\n  let a = gt(t.0);\n  r := i;\n"
#guard cost growing "M" (depth := 7) == "S015 35:11"
#guard (cost growing "M" (depth := 8)).startsWith "total 504"

/-!
A container holds handle leaves (section 5.1). An element and a field of a handle type are `raw`
(section 9.2), so they keep the handle, and an index gives it back. A value without a hardware
leaf takes no version (section 7.3), so the first binding with a hardware leaf has none.
-/
#guard exact (handleLets "  r := i;\n  let a = S(r);\n") "M" 366
#guard names (handleLets "  r := i;\n  let a = S(r);\n") "M" "M" == ["r", "q", "s", "w", "u"]
#guard exact (handleLets "  let a = [q, r];\n  let b: Reg[UInt[8]] = a[1];\n  b := i;\n") "M" 369
#guard exact (handleLets "  r := i;\n  let a = [u, u];\n  let t = (u.x, w, r);\n") "M" 360
#guard names (handleLets "  r := i;\n  let mut a = (q, UInt[8](0));\n  a.1 = i;\n") "M" "M" ==
  ["a$1e", "r", "q", "s", "w", "u"]
#guard names (handleLets "  r := i;\n  let mut a = (q, UInt[8](0));\n  a = (q, i);\n") "M" "M" ==
  ["a$1e", "r", "q", "s", "w", "u"]
#guard exact (handleLets "  r := i;\n  let mut a = (q, UInt[8](0));\n  a = (q, i);\n") "M" 369
def fieldRegs (body : String) : String :=
  "struct T { a: [Reg[UInt[8]]; 1] }\n" ++ handleLets body
#guard exact (fieldRegs "  r := i;\n  let a = T([q]);\n  let b: Reg[UInt[8]] = a.a[0];\n") "M" 400
#guard cost (fieldRegs "  r := i;\n  let a = T([s]);\n") "M" (fuel := 190) == "S010 22:11"
#guard cost (fieldRegs "  r := i;\n  let a = T([s]);\n") "M" (fuel := 189) == "S015 22:11"

/-! An own output reads as data in a literal (section 5.1), so its element is a hardware leaf. -/
#guard exact (handleLets "  r := i;\n  let a = [o, i];\n") "M" 356
#guard names (handleLets "  r := i;\n  let a = [o, i];\n") "M" "M" ==
  ["a$0e", "a$1e", "r", "q", "s", "w", "u"]

/-!
Two handle types join only when they are equal (section 5.4). The join charges the sizes of
the pair first, so one unit less stops at the join. A domain is no element (section 6.2).
-/
#guard said (handleLets "  r := i;\n  let a = [r, s];\n") ==
  "`Reg[UInt[8]]` and `Reg[UInt[4]]` have no common type; a handle type joins only with the " ++
    "same handle type, so give both sides one type"
#guard cost (handleLets "  r := i;\n  let a = [r, s];\n") "M" (fuel := 160) == "S010 21:11"
#guard cost (handleLets "  r := i;\n  let a = [r, s];\n") "M" (fuel := 159) == "S015 21:11"
#guard cost (handleLets "  r := i;\n  let a = [r, w, q];\n") "M" (fuel := 161) == "S010 21:11"
#guard cost (handleLets "  r := i;\n  let a = [r, w, q];\n") "M" (fuel := 160) == "S015 21:11"
def domainElem (e : String) : String := s!"module M() domains(clk) \{\n  let a = {e};\n}\n"
#guard said (domainElem "[clk]") ==
  "the domain `clk` is not an element; a domain has no value, so remove it from the literal"
#guard cost (domainElem "[clk]") "M" (fuel := 30) == "S010 2:12"
#guard cost (domainElem "[clk]") "M" (fuel := 29) == "S015 2:12"
#guard cost (domainElem "(1, clk)") "M" (fuel := 32) == "S010 2:15"
#guard cost (domainElem "(1, clk)") "M" (fuel := 31) == "S015 2:15"

/-!
A handle leaf in the value of `diagnostic` renders by its kind and charges 0, as a hardware leaf
does (section 5.4). An array of one handle thus charges 1 for its measure, and a handle alone 0.
The byte charge pays for the text.
-/
#guard observed (handleLets "  r := i;\n  diagnostic(\"h\", [q, r]);\n") ==
  ["(record 21 3 M () (string \"h\") (array (reg (uint 8)) ((reg (uint 8) q) (reg (uint 8) r))))",
    "ok"]
#guard exact (handleLets "  r := i;\n  diagnostic(\"h\", [q, r]);\n") "M" 453
#guard exact (handleLets "  r := i;\n  diagnostic(\"h\", [q]);\n") "M" 427
#guard total (handleLets "  r := i;\n  diagnostic(\"h\", q);\n") "M" == 397

/-!
A module parameter of a handle type is `S011` at the `instance` statement (section 5.1): a static
position takes no handle. The check follows the parameter type, so one unit less stops there.
-/
def staticInst : String :=
  "module C(comptime t: Reg[UInt[8]]) {\n}\n" ++ memBody "  instance u = C(5);\n"
#guard said staticInst ==
  "a module argument takes only static values, so its type cannot be `Reg[UInt[8]]`, a type " ++
    "that holds a handle type; use a data type, for example `UInt[8]`"
#guard cost staticInst "M" (fuel := 41) == "S011 4:3"
#guard cost staticInst "M" (fuel := 40) == "S015 1:22"

/-! A handle as a module argument is `S011` before its typed use at a handle type (5.3). -/
#guard cost ("module C(comptime t: Reg[UInt[8]]) {\n}\n" ++
  memBody "  reg r: UInt[8] = 0;\n  r := r;\n  let h = r;\n  instance u = C(h);\n") "M" ==
  "S011 7:3"

/-!
`read(h)` reads a register or a wire as a `data` context does (section 5.4), also in the
receiver form. A local named `read` shadows the prelude function, so it binds the handle.
-/
def readLets (body : String) : String := handleLets ("  r := i;\n" ++ body)
#guard exact
  (readLets "  let a: UInt[8] = read(r);\n  let b = w.read();\n  let c = read(r) == r;\n") "M"
  382
#guard exact (readLets "  let read = r;\n  let a: Reg[UInt[8]] = read;\n") "M" 356

/-!
A child input is `S017`. An own output, an instance, an own input, a domain, and a memory are
`S010`. Each error is at the call, with its fix (section 6.2). The copy of the argument charges
before the check, so one unit less stops at the call.
-/
def readText (a h : String) : String := s!"`read` takes a register or a wire, not {a}; {h}"
def inputText : String :=
  "the input `x` of `u` is a target only; read the value that you bind to it"
def directly : String := "use the value directly, without `read`"
#guard said (readLets "  let a = read(u.x);\n") == inputText
#guard cost (readLets "  let a = read(u.x);\n") "M" (fuel := 156) == "S017 21:11"
#guard cost (readLets "  let a = read(u.x);\n") "M" (fuel := 155) == "S015 21:11"
#guard said (readLets "  let a = u.x.read();\n") == inputText
#guard cost (readLets "  let a = u.x.read();\n") "M" (fuel := 156) == "S017 21:11"
#guard cost (readLets "  let a = u.x.read();\n") "M" (fuel := 155) == "S015 21:11"
#guard said (readLets "  let a = read(o);\n") == readText "the output `o`" directly
#guard cost (readLets "  let a = read(o);\n") "M" (fuel := 155) == "S010 21:11"
#guard cost (readLets "  let a = read(o);\n") "M" (fuel := 154) == "S015 21:11"
#guard said (readLets "  let a = read(u);\n") ==
  readText "a handle of `Instance[C, 8]`" "read an output of the instance, for example `u.q`"
#guard cost (readLets "  let a = read(u);\n") "M" (fuel := 155) == "S010 21:11"
#guard cost (readLets "  let a = read(u);\n") "M" (fuel := 154) == "S015 21:11"
#guard said (readLets "  let a = read(i);\n") == readText "a value of `UInt[8]`" directly
#guard cost (readLets "  let a = read(i);\n") "M" (fuel := 155) == "S010 21:11"
#guard cost (readLets "  let a = read(i);\n") "M" (fuel := 154) == "S015 21:11"
#guard said (readLets "  let a = read(clock);\n") ==
  readText "the domain `clock`" "a domain has no value, so remove the `read`"
#guard cost (readLets "  let a = read(clock);\n") "M" (fuel := 155) == "S010 21:11"
#guard cost (readLets "  let a = read(clock);\n") "M" (fuel := 154) == "S015 21:11"
def readMem : String := memBody "  mem m: [UInt[8]; 4];\n  let a = read(m);\n"
#guard said readMem ==
  readText "a handle of `Mem[UInt[8], 4]`" "read a word with `read_port`"
#guard cost readMem "M" (fuel := 41) == "S010 3:11"
#guard cost readMem "M" (fuel := 40) == "S015 3:11"
#guard said (readLets "  let a = read(r, w);\n") ==
  "`read` takes 1 argument(s), but it has 2; write `read(h)` with one register or wire"

/-!
The result of `read` refers to the register, so `let x = read(r);` is a copy: it charges the
zero size of the type once, before the leaves bind. A part without a hardware leaf is a new
static value, so its binding is no copy, and the read charges its zero size once. Thus each
binding below grows by the zero size of `[Unit; 100]` less that of `[Unit; 0]`, 100 units.
-/
def readAgg (t body : String) : String :=
  s!"type P = {t};\nmodule M() \{\n  reg r: P = P();\n  r := r;\n" ++ body ++ "}\n"
def readGrowth (t0 t1 : String) : Int :=
  let used (t b : String) : Int := (total (readAgg t b) "M" : Int)
  let b := "  let x = read(r);\n"
  (used t1 b - used t1 "") - (used t0 b - used t0 "")
#guard readGrowth "(UInt[8], [Unit; 0])" "(UInt[8], [Unit; 100])" == 100
#guard readGrowth "[Unit; 0]" "[Unit; 100]" == 100
#guard exact (readAgg "(UInt[8], [Unit; 100])" "  let x = read(r);\n") "M" 443
#guard exact (readAgg "[Unit; 100]" "  let x = read(r);\n") "M" 376


/-!
A `data` context reads each register leaf and each wire leaf of a container of handles (section
5.4). It charges the recursive size of the value first. Thus one unit less stops at the node in
the `data` context, before any leaf error. These parts give their texts of section 6.2: a memory,
an instance, a child input, a record of handles, and a list of handles. The same holds one
container deeper. The arms of a hardware `if` and `match` and a data field read too. A static
`if` or `match` passes the handles on, so it reads nothing.
-/
def dataLets (body : String) : String :=
  "module C(comptime W: Nat) {\n  input x: UInt[8];\n}\n" ++
  "struct S { a: Reg[UInt[8]] }\nstruct P { a: [UInt[8]; 1] }\n" ++
  "module M() {\n  input c: Bool;\n  input i: UInt[8];\n  output o: Bool;\n" ++
  "  reg r: UInt[8] = 0;\n  reg q: UInt[8] = 0;\n  reg p: (UInt[8], Bool) = (0, false);\n" ++
  "  mem m: [UInt[8]; 4];\n  write_port(m, 0, i, c);\n  let k = read_port(m, 0, c);\n" ++
  "  instance u = C(8);\n  r := i;\n  q := i;\n  p := (i, c);\n  u.x := i;\n" ++ body ++ "}\n"
#guard exact (dataLets "  o := [r, q] == [q, r];\n") "M" 683
#guard exact (dataLets "  o := [p] == [p];\n") "M" 677
#guard exact (dataLets "  let a = if (c) { [r] } else { [q] };\n  o := a[0] == i;\n") "M" 675
#guard exact (dataLets "  let a = P([r]);\n  o := c;\n") "M" 677
#guard exact (dataLets "  let a = [r, q];\n  o := a[0] == i;\n") "M" 655
#guard exact (dataLets "  let a = if (true) { [m] } else { [m] };\n  o := c;\n") "M" 640
#guard exact (dataLets "  let a = match (true) { true => [u], _ => [u] };\n  o := c;\n") "M" 645
def memData : String := "`m` is a memory, not data; read a word with `read_port`"
#guard said (dataLets "  o := [m] == [m];\n") == memData
#guard cost (dataLets "  o := [m] == [m];\n") "M" (fuel := 230) == "S010 21:8"
#guard cost (dataLets "  o := [m] == [m];\n") "M" (fuel := 229) == "S015 21:8"
#guard said (dataLets "  o := [[m]] == [[m]];\n") == memData
#guard cost (dataLets "  o := [[m]] == [[m]];\n") "M" (fuel := 235) == "S010 21:8"
#guard cost (dataLets "  o := [[m]] == [[m]];\n") "M" (fuel := 234) == "S015 21:8"
#guard said (dataLets "  o := [u] == [u];\n") ==
  "`u` is an instance, not data; read its outputs as `u.q`"
#guard cost (dataLets "  o := [u] == [u];\n") "M" (fuel := 230) == "S010 21:8"
#guard cost (dataLets "  o := [u] == [u];\n") "M" (fuel := 229) == "S015 21:8"
#guard said (dataLets "  o := (u.x, 1) == (u.x, 1);\n") ==
  "the input `x` of `u` is a target only; read the value that you bind to it"
#guard cost (dataLets "  o := (u.x, 1) == (u.x, 1);\n") "M" (fuel := 235) == "S017 21:8"
#guard cost (dataLets "  o := (u.x, 1) == (u.x, 1);\n") "M" (fuel := 234) == "S015 21:8"
def recordData : String :=
  "a `data` context does not read the record of handles `S`; construct the data record from " ++
    "the fields, for example `P(read(h.a), read(h.b))`"
#guard said (dataLets "  o := S(r) == S(r);\n") == recordData
#guard cost (dataLets "  o := S(r) == S(r);\n") "M" (fuel := 252) == "S010 21:8"
#guard cost (dataLets "  o := S(r) == S(r);\n") "M" (fuel := 251) == "S015 21:8"
#guard said (dataLets "  o := (1, S(r)) == (1, S(r));\n") == recordData
#guard cost (dataLets "  o := (1, S(r)) == (1, S(r));\n") "M" (fuel := 261) == "S010 21:8"
#guard cost (dataLets "  o := (1, S(r)) == (1, S(r));\n") "M" (fuel := 260) == "S015 21:8"
def listLets (body : String) : String :=
  dataLets ("  let hs: List[Reg[UInt[8]]] = list(Reg[UInt[8]]);\n" ++ body)
def listData : String :=
  "a `data` context does not read the list of handles `List[Reg[UInt[8]]]`; read each " ++
    "element, for example `read(hs[0])`"
#guard said (listLets "  o := hs == hs;\n") == listData
#guard cost (listLets "  o := hs == hs;\n") "M" (fuel := 261) == "S010 22:8"
#guard cost (listLets "  o := hs == hs;\n") "M" (fuel := 260) == "S015 22:8"
#guard said (listLets "  diagnostic(hs, 1);\n  o := c;\n") == listData
#guard cost (listLets "  diagnostic(hs, 1);\n  o := c;\n") "M" (fuel := 266) == "S010 22:3"
#guard cost (listLets "  diagnostic(hs, 1);\n  o := c;\n") "M" (fuel := 265) == "S015 22:3"
#guard said (dataLets "  let a = if (c) { [m] } else { [m] };\n  o := c;\n") == memData
#guard cost (dataLets "  let a = if (c) { [m] } else { [m] };\n  o := c;\n") "M" (fuel := 231) ==
  "S010 21:11"
#guard cost (dataLets "  let a = if (c) { [m] } else { [m] };\n  o := c;\n") "M" (fuel := 230) ==
  "S015 21:11"
#guard cost (dataLets "  let a = match (c) { true => [u], _ => [u] };\n  o := c;\n") "M"
  (fuel := 236) == "S010 21:11"
#guard cost (dataLets "  let a = match (c) { true => [u], _ => [u] };\n  o := c;\n") "M"
  (fuel := 235) == "S015 21:11"
#guard said (dataLets "  let a = P([m]);\n  o := c;\n") == memData
#guard cost (dataLets "  let a = P([m]);\n  o := c;\n") "M" (fuel := 258) == "S010 21:13"
#guard cost (dataLets "  let a = P([m]);\n  o := c;\n") "M" (fuel := 257) == "S015 21:13"

/-!
A register leaf of an aggregate type reads as a reference. It charges the zero size of its type
before it goes into the result. Take the zero size of `[Unit; 100]` less that of `[Unit; 0]`.
The record `Q((r, 1))` grows by it twice, 200 units: once for the read, once for its own size.
-/
def fieldAgg (t body : String) : String :=
  s!"type T = {t};\nstruct Q \{ a: (T, Int) }\nmodule M() \{\n  input i: T;\n  reg r: T = T();\n" ++
    "  r := i;\n" ++ body ++ "}\n"
def leafGrowth (body : String) : Int :=
  let used (t b : String) : Int := (total (fieldAgg t b) "M" : Int)
  let t0 := "(UInt[8], [Unit; 0])"
  let t1 := "(UInt[8], [Unit; 100])"
  (used t1 body - used t1 "") - (used t0 body - used t0 "")
#guard leafGrowth "  let a = Q((r, 1));\n" == 200

/-!
The read of a leaf checks the depth of the result: the nodes above the leaf plus the depth of
`T()` (section 5.4). A tuple node has the depth 2 over a handle, so only this check sees the
depth of the result. It stops at the node in the `data` context.
-/
def deepLets (body : String) : String :=
  "type T = [[[UInt[8]; 1]; 1]; 1];\nmodule M() {\n  input c: Bool;\n  input i: T;\n" ++
    "  output o: Bool;\n  reg p: T = T();\n  p := i;\n" ++ body ++ "}\n"
#guard (cost (deepLets "  let a = ((p, 1), 1);\n  o := a == a;\n") "M" (depth := 6)).startsWith
  "total"
#guard cost (deepLets "  let a = ((p, 1), 1);\n  o := a == a;\n") "M" (depth := 5) == "S015 9:8"
#guard (cost (deepLets "  let a = ((p, 1), 1);\n  o := c;\n") "M" (depth := 4)).startsWith "total"

/-!
A list of handles is a list node (section 5.1). `list(T)` of a type with the handle flag gives an
empty one. `push` and `pop` change it and charge as on a static list (section 5.4). An index
and `len` refer to it with no charge, so their cost does not grow with the length. `grow` pushes
into a `mut` formal, and `deep` pushes into the inner list of a `mut` formal.
-/
def handleList (body : String) : String :=
  "type P = (Reg[UInt[8]], Type);\n" ++
  "fn grow(mut xs: List[Reg[UInt[8]]], x: Reg[UInt[8]]) -> Bool {\n  xs.push(x);\n" ++
  "  return true;\n}\n" ++
  "fn deep(mut x: List[List[P]], h: Reg[UInt[8]]) -> Bool {\n" ++
  "  x[0].push((h, [[[[UInt[8]; 1]; 1]; 1]; 1]));\n  return true;\n}\n" ++
  "module M() {\n  input c: Bool;\n  input i: UInt[8];\n  output o: UInt[8];\n" ++
  "  reg r: UInt[8] = 0;\n  reg q: UInt[8] = 0;\n  reg s: UInt[4] = 0;\n  q := i;\n  s := 0;\n" ++
  "  let mut xs = list(Reg[UInt[8]]);\n" ++ body ++ "}\n"
#guard exact (handleList ("  xs.push(r);\n  xs.push(q);\n  let b: Reg[UInt[8]] = xs[0];\n" ++
  "  let n = len(xs);\n  b := i;\n  o := i;\n")) "M" 253
#guard exact (handleList "  xs.push(r);\n  let h = xs.pop();\n  h := i;\n  o := i;\n") "M" 231
#guard exact (handleList "  xs.push(r);\n  xs[0] = q;\n  r := i;\n  o := i;\n") "M" 235
#guard exact (handleList "  let a = grow(xs, r);\n  r := i;\n  o := i;\n") "M" 269
#guard names (handleList "  xs.push(r);\n  let h = xs.pop();\n  h := i;\n  o := i;\n") "M" "M" ==
  ["r", "q", "s"]
def filled (n : Nat) (body : String) : Int :=
  total (handleList (s!"  comptime for k in 0..{n} \{\n    xs.push(r);\n  }\n" ++ body ++
    "  r := i;\n  o := i;\n")) "M"
#guard filled 1 "  let m = len(xs);\n" - filled 1 "" == 4
#guard filled 40 "  let m = len(xs);\n" - filled 40 "" == 4
#guard filled 1 "  let m = xs[0];\n" - filled 1 "" == 6
#guard filled 40 "  let m = xs[0];\n" - filled 40 "" == 6

/-!
Each error of `push` and `pop` on a list node comes at its step of section 5.4, and one unit
less stops before it. A `pop` of an empty list and an index out of range are `S013`. A hardware
arm cannot change the list (`S016`). An element with a hardware leaf is `S011`, also in a tuple
with a handle. An element of another handle type is `S010`.
-/
#guard cost (handleList "  let h = xs.pop();\n  r := i;\n  o := i;\n") "M" (fuel := 105) ==
  "S013 20:11"
#guard cost (handleList "  let h = xs.pop();\n  r := i;\n  o := i;\n") "M" (fuel := 104) ==
  "S015 20:14"
#guard cost (handleList "  xs.push(r);\n  let h = xs[1];\n  r := i;\n  o := i;\n") "M"
  (fuel := 112) == "S013 21:14"
#guard cost (handleList "  xs.push(r);\n  let h = xs[1];\n  r := i;\n  o := i;\n") "M"
  (fuel := 111) == "S015 21:14"
#guard cost (handleList "  o := if (c) { push(xs, r) } else { 2 };\n  r := i;\n") "M"
  (fuel := 108) == "S016 20:17"
#guard cost (handleList "  o := if (c) { push(xs, r) } else { 2 };\n  r := i;\n") "M"
  (fuel := 107) == "S015 20:26"
#guard cost (handleList "  xs.push(r);\n  o := if (c) { 3 } else { pop(xs) };\n  r := i;\n") "M"
  (fuel := 114) == "S016 21:28"
#guard cost (handleList "  xs.push(r);\n  o := if (c) { 3 } else { pop(xs) };\n  r := i;\n") "M"
  (fuel := 113) == "S015 21:28"
def hwElement : String := handleList "  let mut ys = list(P);\n  ys.push((r, i));\n  o := i;\n"
#guard cost hwElement "M" (fuel := 151) == "S011 21:11"
#guard cost hwElement "M" (fuel := 150) == "S015 21:11"
#guard said (handleList "  xs.push(s);\n") == typedText "Reg[UInt[8]]" "a handle of `Reg[UInt[4]]`"

/-!
The hardware leaf of a `push` element is `S011` before the compare of a handle type. A read at
a list of data that gives a hardware leaf is `S011` too (section 5.4, step 4).
-/
#guard cost (handleList "  xs.push(i);\n") "M" (fuel := 106) == "S011 20:11"
#guard cost (handleList "  xs.push(i);\n") "M" (fuel := 105) == "S015 20:11"
def readElement : String := handleList "  let mut ys = list(UInt[8]);\n  ys.push(r);\n"
#guard cost readElement "M" (fuel := 118) == "S011 21:11"
#guard cost readElement "M" (fuel := 117) == "S015 21:11"

/-!
A `push` checks the depth of the new element on its path (section 5.4). The type value of the
depth 5 makes a tuple of the depth 6, so the path of `ys` reaches the depth 7.
-/
def deepPush : String :=
  handleList ("  let mut ys = list(P);\n  ys.push((r, [[[[UInt[8]; 1]; 1]; 1]; 1]));\n" ++
    "  r := i;\n  o := i;\n")
#guard (cost deepPush "M" (depth := 7)).startsWith "total 349"
#guard cost deepPush "M" (depth := 6) == "S015 21:3"

/-!
The write-back of a list of lists of handles checks the depth of the value (section 5.4). The
inner list of `deep` grows to the depth 7 in the callee, so the `push` there needs the depth 8.
The write-back into `t.0` needs the depth 9, so the depth 8 stops at the write-back, at the call.
A list of `Reg[T]` alone cannot grow above the depth of its type, so `P` holds a `Type`.
-/
def deepBack : String :=
  handleList ("  let mut ys = list(P);\n  let mut t = (list(List[P]),);\n  t.0.push(ys);\n" ++
    "  let a = deep(t.0, r);\n  r := i;\n  o := i;\n")
#guard (cost deepBack "M" (depth := 9)).startsWith "total 454"
#guard cost deepBack "M" (depth := 8) == "S015 23:11"
#guard (match Cli.costText { budget := { fuel := 100000000, depth := 8 } } deepBack "M" with
  | .error e => e.msg
  | _ => "ok") == "the depth 9 goes above the nesting depth 8; raise --depth to at least 9"

/-!
A `pop` charges the size of its element. An element deeper than the element type can lower the
depth, so it also charges the size of the root (section 5.4). The deep element below thus adds
its size 8 to the `pop`.
-/
def popOf (pre : String) : Int :=
  let tail := "  r := i;\n  o := i;\n"
  (total (handleList ("  let mut ys = list(P);\n" ++ pre ++ "  let h = ys.pop();\n" ++ tail))
    "M" : Int) - total (handleList ("  let mut ys = list(P);\n" ++ pre ++ tail)) "M"
def deepElem : String := "  ys.push((r, [[UInt[8]; 1]; 1]));\n"
#guard popOf "  ys.push((r, Bool));\n" == 6
#guard popOf deepElem == 20
#guard popOf (deepElem ++ deepElem) == 28
#guard popOf (deepElem ++ "  ys.push((r, Bool));\n") == 6

/-!
`push` refreshes a list node by a delta, so `n` pushes cost `O(n)` (section 5.4). A list part of
a tuple charges the part count 2 of the tuple node at each `push`. A `pop` refreshes in the same
way.
-/
def pushes (pre step : String) (n : Nat) : Int :=
  total (handleList (pre ++ s!"  comptime for k in 0..{n} \{\n" ++ step ++ "  }\n" ++
    "  r := i;\n  o := i;\n")) "M"
#guard [10, 20, 40, 80].map (pushes "" "    xs.push(r);\n") == [299, 369, 509, 789]
#guard [10, 20, 40, 80].map (pushes "  let mut t = (r, xs);\n" "    t.1.push(q);\n") ==
  [336, 436, 636, 1036]
def filler (n : Nat) : String := s!"  comptime for k in 0..{n} \{\n    xs.push(r);\n  }\n"
#guard [10, 20, 40, 80].map (fun n => pushes (filler n) "    let h = xs.pop();\n" n) ==
  [366, 496, 756, 1276]

/-!
A static position takes no handle (section 5.1). A handle there is `S011` with the text "Handle
at a static position", which names its kind and its resource. Another value of a type with the
handle flag gives "Handles at a static position" with its type. Both come before the typed use,
and the check walks no value, so one unit less stops at the work before it.
-/
def targets (body : String) : String :=
  "module C(comptime W: Nat) {\n  input x: UInt[8];\n  output y: UInt[8];\n  y := x;\n}\n" ++
  "module K(comptime t: Int) {\n}\n" ++
  "struct S { a: Reg[UInt[8]] }\n" ++
  "comptime fn g(x: Int) -> Int { return 0; }\n" ++
  "module M() {\n  input i: UInt[8];\n  output o: UInt[8];\n  reg r: UInt[8] = 0;\n" ++
  "  reg q: UInt[8] = 0;\n  wire w: UInt[8];\n  instance u = C(8);\n  o := i;\n" ++
  "  w := i;\n" ++ body ++ "}\n"
def heldStatic (s k r : String) : String :=
  s!"{s} holds the {k} `{r}`, but it takes only static values; pass the data through " ++
    "a port, or use it in the module that declares it"
#guard said (targets "  u.x := i;\n  let h = r;\n  instance v = K(h);\n") ==
  heldStatic "a module argument" "register" "r"
#guard cost (targets "  u.x := i;\n  let h = r;\n  instance v = K(h);\n") "M" (fuel := 143) ==
  "S011 21:3"
#guard cost (targets "  u.x := i;\n  let h = r;\n  instance v = K(h);\n") "M" (fuel := 142) ==
  "S015 21:18"
#guard said (targets "  u.x := i;\n  let h = w;\n  instance v = K(h);\n") ==
  heldStatic "a module argument" "wire" "w"
#guard said (targets "  u.x := i;\n  let h = u;\n  instance v = K(h);\n") ==
  heldStatic "a module argument" "instance" "u"
#guard said (targets "  u.x := i;\n  let h = u.x;\n  instance v = K(h);\n") ==
  heldStatic "a module argument" "input" "u.x"
#guard said (targets "  u.x := i;\n  let h = r;\n  let t = Instance[K, h];\n") ==
  heldStatic "a module argument" "register" "r"
#guard said (targets ("  u.x := i;\n  mem m: [UInt[8]; 4];\n  write_port(m, 0, i, true);\n" ++
  "  let k = read_port(m, 0, true);\n  let h = m;\n  instance v = K(h);\n")) ==
  heldStatic "a module argument" "memory" "m"
#guard said (targets "  u.x := i;\n  let h = r;\n  let z = g(h);\n") ==
  heldStatic "an argument of a comptime fn" "register" "r"

/-!
An own output has no handle type, but it is not static either. Thus it gives the text "Handle
at a static position" too, with the kind `output`. A domain has no data, so it gives the text
"Domain at a static position" (section 6.2).
-/
#guard said (targets "  u.x := i;\n  let h = o;\n  instance v = K(h);\n") ==
  heldStatic "a module argument" "output" "o"
#guard cost (targets "  u.x := i;\n  let h = o;\n  instance v = K(h);\n") "M" (fuel := 143) ==
  "S011 21:3"
#guard cost (targets "  u.x := i;\n  let h = o;\n  instance v = K(h);\n") "M" (fuel := 142) ==
  "S015 21:18"
def domainArg : String :=
  "comptime fn g(x: Int) -> Int { return 0; }\nmodule M() domains(clk) {\n  let h = clk;\n" ++
    "  let z = g(h);\n}\n"
#guard said domainArg == "an argument of a comptime fn holds the domain `clk`, but a domain " ++
  "is never static; remove it from this static position"
#guard cost domainArg "M" (fuel := 36) == "S011 4:11"
#guard cost domainArg "M" (fuel := 35) == "S015 4:11"
#guard cost (targets "  u.x := i;\n  let h = r;\n  let z = g(h);\n") "M" (fuel := 147) ==
  "S011 21:11"
#guard cost (targets "  u.x := i;\n  let h = r;\n  let z = g(h);\n") "M" (fuel := 146) ==
  "S015 21:11"
#guard said (targets "  u.x := i;\n  let h = [r, q];\n  instance v = K(h);\n") ==
  "a module argument takes only static values, but a value of `[Reg[UInt[8]]; 2]` can hold " ++
    "handles; pass the data through a port, or use the handles in the module that declares them"
#guard cost (targets "  u.x := i;\n  let h = [r, q];\n  instance v = K(h);\n") "M" (fuel := 153) ==
  "S011 21:3"
#guard cost (targets "  u.x := i;\n  let h = [r, q];\n  instance v = K(h);\n") "M" (fuel := 152) ==
  "S015 21:18"
#guard said (targets "  u.x := i;\n  let h = (r, 1);\n  let z = g(h);\n") ==
  "an argument of a comptime fn takes only static values, but a value of `(Reg[UInt[8]], Int)` " ++
    "can hold handles; pass the data through a port, or use the handles in the module that " ++
    "declares them"

/-!
A `:=` target evaluates its indices, then walks its steps from the root outward (section 5.2).
An index step charges 1 and evaluates its index. In the walk, a field or a selector on a
container of handles charges 1, and each step on such a container checks and selects. A field of
an `Instance` handle selects a child input with no charge, also in a container. `S018` counts
the resource of the target, so a second binding through a container is `S018`.
-/
#guard exact (targets "  u.x := i;\n  let rs = [r, q];\n  rs[0] := i;\n  rs[1] := i;\n") "M" 332
#guard exact (targets "  u.x := i;\n  let t = (r, q);\n  t.1 := i;\n  t[0] := i;\n") "M" 324
#guard exact (targets "  u.x := i;\n  let s = S(r);\n  s.a := i;\n  q := i;\n") "M" 341
#guard exact (targets "  let us = [u];\n  us[0].x := i;\n  r := i;\n  q := i;\n") "M" 321
#guard exact (targets "  u.x := i;\n  let rss = [[r, q]];\n  rss[0][1] := i;\n  r := i;\n") "M" 337
#guard exact (targets ("  u.x := i;\n  let mut xs = list(Reg[UInt[8]]);\n  xs.push(q);\n" ++
  "  xs[0] := i;\n  r := i;\n")) "M" 339
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs[0] := i;\n  r := i;\n  q := i;\n")
  "M" == "S018 22:3"

/-!
Each error of a step comes at its step of section 5.2, and one unit less stops before it. The
index is static (`S011`), the base takes the step (`S010`), the index is an integer (`S010`), and
it is in range (`S013`). A step on a base without the handle flag, or on another handle, is
`S017` at the start of the target. It comes in the walk, after each index step charged and its
index evaluated. A child output and a selected part of another kind are `S017` there too.
-/
#guard cost (targets "  u.x := i;\n  let j = i;\n  let rs = [r, q];\n  rs[j] := i;\n") "M"
  (fuel := 157) == "S011 22:6"
#guard cost (targets "  u.x := i;\n  let j = i;\n  let rs = [r, q];\n  rs[j] := i;\n") "M"
  (fuel := 156) == "S015 22:6"
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs.0 := i;\n") "M" (fuel := 153) ==
  "S010 21:3"
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs.0 := i;\n") "M" (fuel := 152) ==
  "S015 21:3"
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs[true] := i;\n") "M" (fuel := 155) ==
  "S010 21:6"
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs[true] := i;\n") "M" (fuel := 154) ==
  "S015 21:6"
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs[2] := i;\n") "M" (fuel := 155) ==
  "S013 21:6"
#guard cost (targets "  u.x := i;\n  let rs = [r, q];\n  rs[2] := i;\n") "M" (fuel := 154) ==
  "S015 21:6"
def partAt : String :=
  "a `:=` target is a whole resource, not a part of a value; bind the whole resource, for " ++
    "example `r := P(a, b);`"
#guard said (targets "  u.x := i;\n  r[5] := i;\n") == partAt
#guard cost (targets "  u.x := i;\n  r[5] := i;\n") "M" (fuel := 142) == "S017 20:3"
#guard cost (targets "  u.x := i;\n  r[5] := i;\n") "M" (fuel := 141) == "S015 20:5"
#guard said (targets "  u.x := i;\n  u[0] := i;\n") == partAt
#guard said (targets "  u.x := i;\n  let x = [1, 2];\n  x[5] := i;\n") == partAt
#guard cost (targets "  u.x := i;\n  let x = [1, 2];\n  x[5] := i;\n") "M" (fuel := 151) ==
  "S017 21:3"
#guard cost (targets "  u.x := i;\n  let x = [1, 2];\n  x[5] := i;\n") "M" (fuel := 150) ==
  "S015 21:5"
def childOutput : String :=
  "`y` is an output of the child, not a target; the child drives its outputs, so bind an " ++
    "input of the child"
#guard said (targets "  u.y := i;\n") == childOutput
#guard said (targets "  let us = [u];\n  us[0].y := i;\n") == childOutput
#guard cost (targets "  let us = [u];\n  us[0].y := i;\n") "M" (fuel := 144) == "S017 20:3"
#guard cost (targets "  let us = [u];\n  us[0].y := i;\n") "M" (fuel := 143) == "S015 20:6"
def kindAt (a : String) : String :=
  s!"a `:=` target is a wire, a register, an own output, or a child input, not {a}; select one " ++
    "of these, or assign a local with `=`"
#guard said (targets "  u.x := i;\n  i := i;\n") == kindAt "a value of `UInt[8]`"
#guard said (targets "  u.x := i;\n  let a = (r, 1);\n  a.1 := i;\n") == kindAt "a value of `Int`"
#guard cost (targets "  u.x := i;\n  let a = (r, 1);\n  a.1 := i;\n") "M" (fuel := 148) ==
  "S017 21:3"
#guard cost (targets "  u.x := i;\n  let a = (r, 1);\n  a.1 := i;\n") "M" (fuel := 147) ==
  "S015 21:3"
#guard said (targets ("  u.x := i;\n  mem m: [UInt[8]; 4];\n  write_port(m, 0, i, true);\n" ++
  "  let k = read_port(m, 0, true);\n  let ms = [m];\n  ms[0] := i;\n")) ==
  kindAt "a handle of `Mem[UInt[8], 4]`"

/-!
A store into an array of handles copies the path, so it charges the size of its root (section
5.4, **Rebind**). Thus each store into an array of `n` registers costs `n` plus a constant, and
`n` stores cost `O(n^2)`, as their work does. A `mut` write-back into an element takes the same
path, so it charges the same size.
-/
def handleArray (n k : Nat) (step : String) : String :=
  "fn swap(mut x: Reg[UInt[8]], h: Reg[UInt[8]]) -> Bool {\n  x = h;\n  return true;\n}\n" ++
  "module M() {\n  input i: UInt[8];\n  output o: UInt[8];\n  reg r: UInt[8] = 0;\n" ++
  "  reg q: UInt[8] = 0;\n  r := i;\n  q := i;\n  o := i;\n" ++
  s!"  let mut rs = [{", ".intercalate (List.replicate n "r")}];\n" ++
  s!"  comptime for k in 0..{k} \{\n" ++ step ++ "  }\n}\n"
def perStore (step : String) (n : Nat) : Int :=
  (total (handleArray n 1 step) "M" : Int) - total (handleArray n 0 step) "M"
#guard [10, 20, 40].map (perStore "    rs[0] = q;\n") == [19, 29, 49]
#guard [10, 20, 40].map (fun n => total (handleArray n n "    rs[0] = q;\n") "M") ==
  [432, 902, 2442]
#guard [10, 20, 40].map (perStore "    let b = swap(rs[0], q);\n") == [54, 64, 84]
#guard exact (handleArray 10 10 "    let b = swap(rs[0], q);\n") "M" 782

/-!
A position of a type with the handle flag is `raw` (section 9.2), so its typed use reads nothing.
A handle there is `S010` with the text "Typed use at a container of handles". This holds at a typed
`let`, at an assignment to a local without a type, at a field, and at a `push` element. The
copy charges first, so one unit less stops at the statement.
-/
def flagLets (body : String) : String :=
  "struct T { a: [Reg[UInt[8]]; 1] }\n" ++ handleLets ("  mem m: [UInt[8]; 4];\n" ++ body)
def flagUse0 : String := flagLets "  let a: [Reg[UInt[8]]; 1] = r;\n"
#guard said flagUse0 == boxText "[Reg[UInt[8]]; 1]" "a handle of `Reg[UInt[8]]`"
#guard cost flagUse0 "M" (fuel := 181) == "S010 22:3"
#guard cost flagUse0 "M" (fuel := 180) == "S015 22:3"
def flagUse1 : String := flagLets "  let a: [Input[UInt[8]]; 1] = u.x;\n"
#guard said flagUse1 == boxText "[Input[UInt[8]]; 1]" "a handle of `Input[UInt[8]]`"
#guard cost flagUse1 "M" (fuel := 182) == "S010 22:3"
#guard cost flagUse1 "M" (fuel := 181) == "S015 22:3"
def flagUse2 : String := flagLets "  let a: [Mem[UInt[8], 4]; 1] = m;\n"
#guard said flagUse2 == boxText "[Mem[UInt[8], 4]; 1]" "a handle of `Mem[UInt[8], 4]`"
#guard cost flagUse2 "M" (fuel := 185) == "S010 22:3"
#guard cost flagUse2 "M" (fuel := 184) == "S015 22:3"
def flagUse3 : String := flagLets "  let mut a = [r];\n  a = r;\n"
#guard said flagUse3 == boxText "[Reg[UInt[8]]; 1]" "a handle of `Reg[UInt[8]]`"
#guard cost flagUse3 "M" (fuel := 164) == "S010 23:3"
#guard cost flagUse3 "M" (fuel := 163) == "S015 23:3"
def flagUse4 : String := flagLets "  let mut a = list([Reg[UInt[8]]; 1]);\n  a.push(r);\n"
#guard said flagUse4 == boxText "[Reg[UInt[8]]; 1]" "a handle of `Reg[UInt[8]]`"
#guard cost flagUse4 "M" (fuel := 191) == "S010 23:3"
#guard cost flagUse4 "M" (fuel := 190) == "S015 23:10"
def flagUse5 : String := flagLets "  let a = T(r);\n"
#guard said flagUse5 == boxText "[Reg[UInt[8]]; 1]" "a handle of `Reg[UInt[8]]`"
#guard cost flagUse5 "M" (fuel := 192) == "S010 22:11"
#guard cost flagUse5 "M" (fuel := 191) == "S015 22:11"

/-!
A read of an empty container of memories, instances, or inputs finds no leaf to report at. Its
result keeps the handle flag, so it is `S010` at the node with the text "Handles as data"
(section 5.4). The size charges first, so one unit less stops at the node. An empty array of
registers reads as an empty array of data.
-/
def handlesData (t : String) : String :=
  s!"a `data` context does not read `{t}`, a type that holds a memory, an instance, or an " ++
    "input; read the data of each element"
def emptyMems : String :=
  flagLets "  let e: [Mem[UInt[8], 4]; 0] = [];\n  let b: [UInt[8]; 0] = e;\n"
#guard said emptyMems == handlesData "[Mem[UInt[8], 4]; 0]"
#guard cost emptyMems "M" (fuel := 205) == "S010 23:3"
#guard cost emptyMems "M" (fuel := 204) == "S015 23:3"
def emptyInsts : String :=
  flagLets "  let e: [Instance[C, 8]; 0] = [];\n  o := if (i == 0) { e == e } else { false };\n"
#guard said emptyInsts == handlesData "[Instance[C, 8]; 0]"
#guard cost emptyInsts "M" (fuel := 191) == "S010 23:22"
#guard cost emptyInsts "M" (fuel := 190) == "S015 23:22"
def emptyInputs : String :=
  flagLets "  let e: [Input[UInt[8]]; 0] = [];\n  let t = (e, r);\n  let b = t == t;\n"
#guard said emptyInputs == handlesData "([Input[UInt[8]]; 0], Reg[UInt[8]])"
#guard cost emptyInputs "M" (fuel := 194) == "S010 24:11"
#guard cost emptyInputs "M" (fuel := 193) == "S015 24:11"
#guard (cost (handleLets ("  let e: [Reg[UInt[8]]; 0] = [];\n  let b: [UInt[8]; 0] = e;\n" ++
  "  r := i;\n")) "M").startsWith "total"

/-!
Helpers that declare resources (sections 5.6, 7.3, 9.4, and 9.5). A helper declares in the
instantiation of its caller. Each resource gets the call frame of the helper. The tests cover a
register, a loop, a recursion, an instance, the roles of a memory, and the version field `$1v`.
-/
def helperPaths : String :=
  "fn cell(x: UInt[8]) -> Reg[UInt[8]] {\n" ++
  "  reg r: UInt[8] = 0;\n" ++
  "  r := x;\n" ++
  "  return r;\n" ++
  "}\n" ++
  "fn loop(x: UInt[8]) -> UInt[8] {\n" ++
  "  comptime for i in 0..3 {\n" ++
  "    reg r: UInt[8] = 0;\n" ++
  "    r := x;\n" ++
  "  }\n" ++
  "  return x;\n" ++
  "}\n" ++
  "fn rec(comptime n: Nat, x: UInt[8]) -> UInt[8] {\n" ++
  "  reg r: UInt[8] = 0;\n" ++
  "  r := x;\n" ++
  "  comptime if (n > 0) {\n" ++
  "    let y = rec(n - 1, x);\n" ++
  "  }\n" ++
  "  return x;\n" ++
  "}\n" ++
  "fn twice(x: UInt[8]) -> UInt[8] {\n" ++
  "  comptime if (true) {\n" ++
  "    wire r: UInt[8];\n" ++
  "    r := x;\n" ++
  "  }\n" ++
  "  comptime if (true) {\n" ++
  "    wire r: UInt[8];\n" ++
  "    r := x;\n" ++
  "  }\n" ++
  "  return x;\n" ++
  "}\n" ++
  "fn mk(x: UInt[8]) -> UInt[8] {\n" ++
  "  mem m: [UInt[8]; 4];\n" ++
  "  write_port(m, 0, x, true);\n" ++
  "  let q = read_port(m, 0, true);\n" ++
  "  instance u = C(8);\n" ++
  "  u.p := x;\n" ++
  "  return u.q;\n" ++
  "}\n" ++
  "module C(comptime W: Nat) {\n" ++
  "  input p: UInt[W];\n" ++
  "  output q: UInt[W];\n" ++
  "  q := p;\n" ++
  "}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n" ++
  "  output o: UInt[8];\n" ++
  "  let a = cell(x);\n" ++
  "  let b = cell(x);\n" ++
  "  let c = loop(x);\n" ++
  "  let d = rec(1, x);\n" ++
  "  let e = twice(x);\n" ++
  "  o := mk(x);\n" ++
  "}\n"
#guard names helperPaths "M()" "M" == [
  "cell$0c$x", "cell$1c$x", "loop$2c$x", "loop$2c$0ret", "c", "rec$3c$x", "rec$3c$rec$0c$x",
  "rec$3c$rec$0c$0ret", "rec$3c$y", "rec$3c$0ret", "d", "twice$4c$x", "twice$4c$0ret", "e",
  "mk$5c$x", "mk$5c$q$data", "mk$5c$q$valid", "mk$5c$0ret", "cell$0c$r", "cell$1c$r",
  "loop$2c$i$0$r", "loop$2c$i$1$r", "loop$2c$i$2$r", "rec$3c$r", "rec$3c$rec$0c$r",
  "twice$4c$r", "twice$4c$r$1v", "mk$5c$u"]
#guard order helperPaths "M()" == ["C$8", "M"]
#guard (topBody helperPaths "M()").map (·.mems.toList.map (Names.encode ·.path.name)) ==
  some ["mk$5c$m"]
#guard match Cli.elabText {} helperPaths "M()" with
  | .ok t => ["(reg mk$5c$m$0rdata ", "(mem mk$5c$m ", "(inst mk$5c$u C$8 "].all (t.contains ·)
  | _ => false

/-!
An instance in a helper: the caller pays the statement, and the new child pays its body
(section 5.4). The child line equals the line of the same `instance` in the module body. A
second call reuses the done child, so its body runs once.
-/
def helperChild : String :=
  "module C(comptime W: Nat) {\n" ++
  "  input p: UInt[W];\n" ++
  "  output q: UInt[W];\n" ++
  "  q := p;\n" ++
  "}\n" ++
  "fn mk(x: UInt[8]) -> UInt[8] {\n" ++
  "  instance u = C(8);\n" ++
  "  u.p := x;\n" ++
  "  return u.q;\n" ++
  "}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n" ++
  "  output o: UInt[8];\n" ++
  "  o := mk(x);\n" ++
  "}\n"
def directChild : String :=
  "module C(comptime W: Nat) {\n" ++
  "  input p: UInt[W];\n" ++
  "  output q: UInt[W];\n" ++
  "  q := p;\n" ++
  "}\n" ++
  "module M() {\n" ++
  "  input x: UInt[8];\n" ++
  "  output o: UInt[8];\n" ++
  "  instance u = C(8);\n" ++
  "  u.p := x;\n" ++
  "  o := u.q;\n" ++
  "}\n"
#guard cost helperChild "M()" == "total 267\nC$8 47\nM 192\n"
#guard cost directChild "M()" == "total 217\nC$8 47\nM 142\n"
#guard exact helperChild "M()" 267
#guard order (helperChild.replace "o := mk(x);" "o := mk(x) +% mk(x);") "M()" == ["C$8", "M"]
#guard ((names (helperChild.replace "o := mk(x);" "o := mk(x) +% mk(x);") "M()" "M").filter
  (·.endsWith "$u")) == ["mk$0c$u", "mk$1c$u"]

/-! A register in a helper charges as in a module body, before its work. -/
def helperReg : String :=
  "fn cell(x: UInt[8]) -> UInt[8] {\n  reg r: UInt[8] = 0;\n  r := x;\n  return r;\n}\n" ++
  "module M() {\n  input x: UInt[8];\n  output o: UInt[8];\n  o := cell(x);\n}\n"
#guard cost helperReg "M()" == "total 184\nM 156\n"
#guard exact helperReg "M()" 184

/-!
The mode and the guard of a helper (section 9.4). The return of a `comptime fn` ends its mode,
and its arguments run in the mode of the caller. `{g}` of `S016` is the function of the
outermost call under the guard, also through a function value. A guard in the body of a helper
starts a new record. `{g}` of `S011` is the outermost `comptime fn`, and `{h}` holds the
statement. `S016` comes before `S011`, and `S011` before `S017`. A helper at a static position
that is not structural declares in the caller.
-/
def scopePre : String :=
  "fn g() -> Nat {\n" ++
  "  reg r: UInt[8] = 0;\n" ++
  "  r := r;\n" ++
  "  return 1;\n" ++
  "}\n" ++
  "fn k() -> Nat {\n" ++
  "  return 1;\n" ++
  "}\n" ++
  "fn outer() -> Nat {\n" ++
  "  return g();\n" ++
  "}\n" ++
  "fn own(c: Bool) -> UInt[8] {\n" ++
  "  return if (c) { UInt[8](g()) } else { 0 };\n" ++
  "}\n" ++
  "comptime fn cf(n: Nat) -> Nat {\n" ++
  "  return n;\n" ++
  "}\n" ++
  "comptime fn cg() -> Nat {\n" ++
  "  return g();\n" ++
  "}\n" ++
  "comptime fn ch() -> Nat {\n" ++
  "  return cg();\n" ++
  "}\n" ++
  "module C(comptime W: Nat) {\n" ++
  "  input p: UInt[W];\n" ++
  "  output q: UInt[W];\n" ++
  "  q := p;\n" ++
  "}\n"
def scope (body : String) (domains : String := "") : String :=
  scopePre ++ s!"module M(){domains} \{\n  input c: Bool;\n  input d: UInt[8];\n" ++
    "  output o: UInt[8];\n" ++ body ++ "  o := d;\n}\n"
def gArm (g : String) : String :=
  s!"a hardware arm has no graph effect such as `{g}`; call `{g}` before the `if` or `match`, " ++
    "and use its result in the arm"
def gType (g : String) : String :=
  s!"a type or a constant has no graph effect such as `{g}`; call it before and use the result"
def gStatic (g h : String) : String :=
  s!"the `comptime fn` `{g}` makes no hardware, but its call reaches this register in `{h}`; " ++
    s!"call `{h}` from a `fn` or a module body"
#guard said (scope "  let z = cf(1);\n  let y = g();\n") == "ok"
#guard said (scope "  let z = cf(g());\n") == "ok"
#guard said (scope "  let z = if (c) { UInt[8](k() + g()) } else { d };\n") == gArm "g"
#guard said (scope "  let z = if (c) { UInt[8](outer()) } else { d };\n") == gArm "outer"
#guard said (scope "  let z = own(c);\n") == gArm "g"
#guard said (scope "  let z = if (c) { own(c) } else { d };\n") == gArm "g"
#guard said (scope "  let fv = g;\n  let z = if (c) { UInt[8](fv()) } else { d };\n") == gArm "g"
#guard said (scope "  let x: UInt[g()] = 0;\n") == gType "g"
#guard said (scope "  let x = K;\n" ++ "const K: Nat = g();\n") == gType "g"
#guard elabOnly (scope "  let x: UInt[g()] = 0;\n") "M" == "S016 2:3"
#guard said (scope "  let z = ch();\n") == gStatic "ch" "g"
#guard elabOnly (scope "  let z = ch();\n") "M" == "S011 2:3"
#guard said (scope "  let x: UInt[ch()] = 0;\n") == gType "ch"
#guard said (scope "  let z = cg();\n" " domains()") == gStatic "cg" "g"
#guard said (scope "  let z = g();\n" " domains()") ==
  "a combinational module has no register; remove `domains()` from the module, or move the " ++
    "register to a clocked module"
#guard said (scope "  let z = cm();\n" " domains()" ++
  "fn cm() -> Nat { mem q: [UInt[8]; 4]; return 1; }\n") ==
  "a combinational module has no memory; remove `domains()` from the module, or move the " ++
    "memory to a clocked module"
#guard said (scope "  let z = ci();\n" " domains()" ++
  "fn ci() -> Nat { instance u = C(8); u.p := 1; return 1; }\n") ==
  "a combinational module has no clocked child `C`; remove `domains()` from the module, or " ++
    "move the instance to a clocked module"
def staticUses : String :=
  scope ("  comptime if (g() == 1) {}\n  static_assert(g() == 1, \"one\");\n" ++
    "  instance u = C(8 * g());\n  u.p := d;\n  comptime for i in 0..g() {}\n")
#guard said staticUses == "ok"
#guard ((names staticUses "M()" "M").filter (·.endsWith "$r")) ==
  ["g$0c$r", "g$2c$r", "g$3c$r", "g$4c$r"]

/-!
The `S018` texts of section 6.2. A second binding names the first binding and the declaration.
When one `:=` of a function body runs again for one resource, the text names the function. A
module body that runs one `:=` again in a `comptime for` keeps "Second binding". The port calls
follow the same rule. On a tie of positions, the first recorded error wins.
-/
def s018 (body : String) (pre : String := "") : String :=
  failure (pre ++ s!"module M() \{\n  input x: UInt[8];\n  input e: Bool;\n{body}}\n") 100000000
def twice (r b d : String) : String :=
  s!"`{r}` has a second binding; the first binding is at {b}, and the declaration is at {d}; " ++
    "remove one of the two bindings"
def twiceIn (r h : String) : String :=
  s!"`{r}` has a second binding, because the `:=` in `{h}` runs again for it; run the `:=` " ++
    s!"once for each resource, for example with one call of `{h}` for each"
def portIn (r g h : String) : String :=
  s!"the memory `{r}` has a second `{g}`, because the call in `{h}` runs again for it; run " ++
    s!"the call once for each memory, for example with one call of `{h}` for each"
def setFn : String :=
  "fn set(r: Reg[UInt[8]], x: UInt[8]) -> UInt[8] {\n  r := x;\n  return x;\n}\n"
#guard s018 "  output y: Bool;\n  y := true;\n  y := false;\n" ==
  s!"S018 6:3 {twice "y" "5:3" "4:3"}"
#guard s018 "  output y: Bool;\n  comptime for i in 0..2 {\n    y := true;\n  }\n" ==
  s!"S018 6:5 {twice "y" "6:5" "4:3"}"
#guard s018 ("  instance c = C();\n  c.p := x;\n  c.p := x;\n")
    "module C() {\n  input p: UInt[8];\n}\n" ==
  s!"S018 9:3 {twice "c.p" "8:3" "7:3"}"
#guard s018 "  reg r: UInt[8] = 0;\n  r := x;\n  let a = set(r, x);\n" setFn ==
  s!"S018 2:3 {twice "r" "9:3" "8:3"}"
#guard s018 "  reg r: UInt[8] = 0;\n  let a = set(r, x);\n  let b = set(r, x);\n" setFn ==
  s!"S018 2:3 {twiceIn "r" "set"}"
-- The tie: `q` gets its second binding first, so its text wins at the one `:=` of `set`.
#guard s018 ("  reg r: UInt[8] = 0;\n  reg q: UInt[8] = 0;\n  let a = set(r, x);\n" ++
    "  let b = set(q, x);\n  let c = set(q, x);\n  let d = set(r, x);\n") setFn ==
  s!"S018 2:3 {twiceIn "q" "set"}"
def bindIn : String :=
  "fn bind(u: Input[UInt[8]], x: UInt[8]) -> UInt[8] {\n  u := x;\n  return x;\n}\n" ++
  "module C() {\n  input p: UInt[8];\n}\n"
#guard s018 "  instance c = C();\n  let a = bind(c.p, x);\n  let b = bind(c.p, x);\n" bindIn ==
  s!"S018 2:3 {twiceIn "c.p" "bind"}"
#guard s018 "  wire w: UInt[8];\n" ==
  "S018 4:3 `w` has no binding; bind it with `w := ...;`, or remove its declaration"
#guard s018 "  instance c = C();\n" "module C() {\n  input p: UInt[8];\n}\n" ==
  "S018 7:3 the input `p` of the instance `c` has no binding; bind it with `c.p := ...;`"
#guard s018 "  mem m: [UInt[8]; 4];\n" ==
  "S018 4:3 the memory `m` has no `read_port`; call `read_port` on it once, or remove the memory"
#guard s018 "  mem m: [UInt[8]; 4];\n  let r = read_port(m, 0, e);\n" ==
  "S018 4:3 the memory `m` has no `write_port`; call `write_port` on it once, or remove the " ++
    "memory"
def memRw : String :=
  "  mem m: [UInt[8]; 4];\n  let r = read_port(m, 0, e);\n  write_port(m, 0, x, e);\n"
#guard s018 (memRw ++ "  let q = read_port(m, 1, e);\n") ==
  "S018 7:11 the memory `m` has a second `read_port`; the first call is at 5:11; call " ++
    "`read_port` once and keep its response in a `let`"
#guard s018 (memRw ++ "  write_port(m, 1, x, e);\n") ==
  "S018 7:3 the memory `m` has a second `write_port`; the first call is at 6:3; make one call, " ++
    "and select its address, data, and enable with a hardware `if`"
def memFns : String :=
  "fn rd(m: Mem[UInt[8], 4], e: Bool) -> UInt[8] {\n  return read_port(m, 0, e).data;\n}\n" ++
  "fn wr(m: Mem[UInt[8], 4], x: UInt[8], e: Bool) -> UInt[8] {\n" ++
  "  write_port(m, 0, x, e);\n  return x;\n}\n"
#guard s018 (memRw ++ "  let q = rd(m, e);\n") memFns ==
  "S018 2:10 the memory `m` has a second `read_port`; the first call is at 12:11; call " ++
    "`read_port` once and keep its response in a `let`"
#guard s018 ("  mem m: [UInt[8]; 4];\n  let a = rd(m, e);\n  let b = rd(m, e);\n" ++
    "  write_port(m, 0, x, e);\n") memFns ==
  s!"S018 2:10 {portIn "m" "read_port" "rd"}"
#guard s018 ("  mem m: [UInt[8]; 4];\n  let r = read_port(m, 0, e);\n  let a = wr(m, x, e);\n" ++
    "  let b = wr(m, x, e);\n") memFns ==
  s!"S018 5:3 {portIn "m" "write_port" "wr"}"

end Silicon.Source.Test.Elab
