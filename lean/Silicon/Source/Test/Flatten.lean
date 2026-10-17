-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Test.Elab

/-!
These tests check the lowering of `Source.Flatten` and the command `elab`. They check the exact
canonical `.sil` text of small designs and each operator row of section 7.4. They also check the
temporaries, `S020` with its position, and the charges of the lowering. Each design that `elab`
accepts passed `Core.check`.
-/

namespace Silicon.Source.Test.Flatten

open Silicon.Source

/-! The result of `elab`: the canonical `.sil` text, or the code and the position of the error. -/
def sil (src t : String) (fuel : Nat := 100000000) : String :=
  match Cli.elabText { budget := { fuel } } src t with
  | .ok text => text
  | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .reject line => line
  | .usage _ => "usage"
  | .defect m => s!"defect {m}"

/-! The text of `lines`, one line each. -/
def text (lines : List String) : String := String.join (lines.map (· ++ "\n"))

/-! The fuel of the elaboration alone, without the lowering. -/
def elabUsed (src t : String) : Nat :=
  match Cli.load 4096 src with
  | .error _ => 0
  | .ok (items, checked) =>
    match Cli.topSelection 4096 items checked t with
    | .error _ => 0
    | .ok (p, i, _, xs) =>
      match Elab.elaborate {} checked Names.sha16 p i xs with
      | .ok (_, used) => used
      | .error _ => 0

/-! The counter of the v0.1 README, at the top. -/
#guard sil Test.Elab.counter "Counter(4)" == text [
  "(design Counter$4",
  "  (module Counter$4",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output full (bits 1))",
  "    (output value (bits 4))",
  "    (reg count (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))",
  "    (next count (mux enable (add count (const 4 1)) count))",
  "    (assign full (icmp eq count (const 4 15)))",
  "    (assign value count)))"]

/-! A hierarchy with two instantiations of one module with different arguments. -/
def twoCounters : String :=
  (Test.Elab.counter.splitOn "module Main").head! ++
  "module Main() {\n" ++
  "    input enable: Bool;\n" ++
  "    output value: UInt[4];\n" ++
  "    instance a = Counter(4);\n" ++
  "    instance b = Counter(2);\n" ++
  "    a.enable := enable;\n" ++
  "    b.enable := !enable;\n" ++
  "    value := a.value;\n" ++
  "}\n"

#guard sil twoCounters "Main" == text [
  "(design Main",
  "  (module Counter$2",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output full (bits 1))",
  "    (output value (bits 2))",
  "    (reg count (bits 2) clock$0clk (reset sync clock$0rst (const 2 0)))",
  "    (next count (mux enable (add count (const 2 1)) count))",
  "    (assign full (icmp eq count (const 2 3)))",
  "    (assign value count))",
  "  (module Counter$4",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output full (bits 1))",
  "    (output value (bits 4))",
  "    (reg count (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))",
  "    (next count (mux enable (add count (const 4 1)) count))",
  "    (assign full (icmp eq count (const 4 15)))",
  "    (assign value count))",
  "  (module Main",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output value (bits 4))",
  "    (inst a Counter$4 (clock$0clk clock$0clk) (clock$0rst clock$0rst) (enable enable))",
  "    (inst b Counter$2 (clock$0clk clock$0clk) (clock$0rst clock$0rst) " ++
    "(enable (xor enable (const 1 1))))",
  "    (assign value a.value)))"]

/-! A `comptime for` unrolls into loop frames, and a hardware `if` is a `mux`. -/
def unroll : String :=
  "module R(comptime N: Nat) {\n" ++
  "  input x: UInt[4];\n  input e: Bool;\n  output y: UInt[4];\n" ++
  "  let mut acc = x;\n" ++
  "  comptime for i in 0..N {\n" ++
  "    reg r: UInt[4] = i;\n" ++
  "    r := if (e) { acc } else { r };\n" ++
  "    acc = acc +% r;\n" ++
  "  }\n" ++
  "  y := acc;\n" ++
  "}\n"

#guard sil unroll "R(2)" == text [
  "(design R$2",
  "  (module R$2",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input e (bits 1))",
  "    (input x (bits 4))",
  "    (output y (bits 4))",
  "    (reg i$0$r (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))",
  "    (reg i$1$r (bits 4) clock$0clk (reset sync clock$0rst (const 4 1)))",
  "    (let acc (bits 4) x)",
  "    (let i$0$acc (bits 4) (add acc i$0$r))",
  "    (let i$1$acc (bits 4) (add i$0$acc i$1$r))",
  "    (next i$0$r (mux e acc i$0$r))",
  "    (next i$1$r (mux e i$0$acc i$1$r))",
  "    (assign y i$1$acc)))"]

/-!
Each operator row of section 7.4. A combinational module has no domain ports. The design `ops`
covers the bitwise and the wrapping operators, `-`, `~`, a static shift count, and a narrower
count. It also covers `reinterpret`, and the `resize` of `SInt` to a larger width with a copied
leaf.
-/
#guard sil Test.Elab.ops "M" == text [
  "(design M",
  "  (module C",
  "    (input a (bits 1))",
  "    (output q (bits 1))",
  "    (assign q (xor a (const 1 1))))",
  "  (module M",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input c (bits 3))",
  "    (input e (bits 1))",
  "    (input s (bits 8))",
  "    (input x (bits 8))",
  "    (output b (bits 1))",
  "    (output y (bits 8))",
  "    (output z (bits 16))",
  "    (inst u C (a (or (and e (icmp ult x (const 8 5))) " ++
    "(and (icmp sge s (const 8 255)) (icmp ne x w)))))",
  "    (let k (bits 8) (mux e (const 8 1) (shl x (const 8 2))))",
  "    (let v (bits 8) (shrs (sub (const 8 0) s) (concat (const 5 0) c)))",
  "    (let w (bits 8) (or (and (sub (add x (const 8 1)) (mul x (const 8 3))) (not x)) " ++
    "(xor x (const 8 255))))",
  "    (assign b (mux e (const 1 1) (const 1 0)))",
  "    (assign y (mux u.q k s))",
  "    (assign z (concat (replicate (extract v 7 1) 8) v))))"]

/-!
The design `ops2` covers a wider count with the fill of each shift, the other predicates, `!`,
`resize` to a smaller and to a larger `UInt`, and equal widths. An operand that a rule uses twice
gets a temporary unless it is a leaf. A child input names its temporaries after `u$a`.
-/
def ops2 : String :=
  "module P() domains() {\n  input a: SInt[8];\n}\n" ++
  "module N() domains() {\n" ++
  "  input x: UInt[4];\n  input y: UInt[4];\n  input c: UInt[8];\n  input s: SInt[4];\n" ++
  "  input e: Bool;\n" ++
  "  output a: UInt[4];\n  output b: UInt[4];\n  output d: SInt[4];\n  output f: UInt[2];\n" ++
  "  output g: UInt[8];\n  output h: Bool;\n  output i: UInt[4];\n" ++
  "  a := (x +% y) << (c ^ 1);\n" ++
  "  b := x >> c;\n" ++
  "  d := (s +% 1) >> (c +% 2);\n" ++
  "  f := resize(UInt[2], x);\n" ++
  "  g := resize(UInt[8], x +% y);\n" ++
  "  h := !e && x <= y || x > y && s < 1 || s <= s && s > s;\n" ++
  "  i := x << y;\n" ++
  "  instance u = P();\n" ++
  "  u.a := resize(SInt[8], s +% 1);\n" ++
  "}\n"

#guard sil ops2 "N" == text [
  "(design N",
  "  (module N",
  "    (input c (bits 8))",
  "    (input e (bits 1))",
  "    (input s (bits 4))",
  "    (input x (bits 4))",
  "    (input y (bits 4))",
  "    (output a (bits 4))",
  "    (output b (bits 4))",
  "    (output d (bits 4))",
  "    (output f (bits 2))",
  "    (output g (bits 8))",
  "    (output h (bits 1))",
  "    (output i (bits 4))",
  "    (inst u P (a (concat (replicate (extract u$a$0t 3 1) 4) u$a$0t)))",
  "    (let a$0t (bits 8) (xor c (const 8 1)))",
  "    (let d$0t (bits 4) (add s (const 4 1)))",
  "    (let d$1t (bits 8) (add c (const 8 2)))",
  "    (let u$a$0t (bits 4) (add s (const 4 1)))",
  "    (assign a (mux (icmp uge a$0t (const 8 4)) (const 4 0) " ++
    "(shl (add x y) (extract a$0t 0 4))))",
  "    (assign b (mux (icmp uge c (const 8 4)) (const 4 0) (shru x (extract c 0 4))))",
  "    (assign d (mux (icmp uge d$1t (const 8 4)) (shrs d$0t (const 4 3)) " ++
    "(shrs d$0t (extract d$1t 0 4))))",
  "    (assign f (extract x 0 2))",
  "    (assign g (concat (const 4 0) (add x y)))",
  "    (assign h (or (or (and (xor e (const 1 1)) (icmp ule x y)) " ++
    "(and (icmp ugt x y) (icmp slt s (const 4 1)))) (and (icmp sle s s) (icmp sgt s s))))",
  "    (assign i (shl x y)))",
  "  (module P",
  "    (input a (bits 8))))"]

/-!
The case of section 11.3: 30 nested `>>` on `SInt[1]` with a `UInt[2]` count. Each source shift
gives exactly 2 `shrs`, and each inner shift is a temporary, so the output stays linear.
-/
def shifts : String :=
  let e := (List.range 30).foldl (fun e _ => s!"({e} >> c)") "x"
  "module S() {\n  input x: SInt[1];\n  input c: UInt[2];\n  output y: SInt[1];\n" ++
  s!"  y := {e};\n}\n"
#guard ((sil shifts "S").splitOn "shrs").length - 1 == 60
#guard ((sil shifts "S").splitOn "(let y$").length - 1 == 29

/-!
`S020`: a combinational cycle in the lowered design. The position is that of the cycle node with
the lowest source position. A `:=` binding makes the node of a wire, and an `instance` statement
makes the node of a child.
-/
def wires : String :=
  "module M() {\n  input a: Bool;\n  output y: Bool;\n  wire w: Bool;\n  wire v: Bool;\n" ++
  "  v := w && a;\n  w := v || a;\n  y := w;\n}\n"
#guard sil wires "M" == "S020 6:3"
def through : String :=
  "module P() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\n" ++
  "module T() domains() {\n  output y: Bool;\n  instance u = P();\n  u.a := u.q;\n" ++
  "  y := u.q;\n}\n"
#guard sil through "T" == "S020 8:3"

/-!
The charges of the lowering. `small` lowers with 58 units. The module node and its name charge
2, the domain ports 20, the four ports 8, and the design node with its name 2. The `assign`
statement and its name charge 2, and its value 24. The shift charges 6 for its nodes, `a +% b`
charges 5, and `c ^ 1` charges 4. Its temporary `y$0t` charges 3, and each of its two uses 3.
A domain port charges 1 for its node, and 9 for the bytes of `clock` and `0clk` or `0rst`.
-/
def small : String :=
  "module M() {\n  input a: UInt[2];\n  input b: UInt[2];\n  input c: UInt[3];\n" ++
  "  output y: UInt[2];\n  y := (a +% b) << (c ^ 1);\n}\n"
#guard Test.Elab.total small "M" == elabUsed small "M" + 58
#guard Test.Elab.exact small "M" (Test.Elab.total small "M")
#guard sil small "M" (Test.Elab.total small "M" - 1) == "S015 1:1"
#guard sil small "M" (elabUsed small "M" + 24) == "S015 3:3"

/-! Each field of a core name charges its bytes. A port name of 100 bytes occurs twice. -/
def named (x : String) : String :=
  s!"module M() domains() \{\n  input a: Bool;\n  output {x}: Bool;\n  {x} := a;\n}\n"
def lowering (src : String) : Nat := Test.Elab.total src "M" - elabUsed src "M"
#guard lowering (named (String.ofList (List.replicate 100 'q'))) == lowering (named "q") + 198

/-!
A loop value is a made integer field. It charges the square of its size in each name, so a large
loop value pays for its digits.
-/
def bigLoop : String :=
  "module M() {\n  input x: Bool;\n  output y: Bool;\n" ++
  "  comptime for i in (1 << 100000)..(1 << 100000) + 1 {\n    let t = x;\n    y := t;\n  }\n}\n"
#guard Test.Elab.total bigLoop "M" > elabUsed bigLoop "M" + 2 * 1563 * 1563

/-!
A node whose effective height reaches 64 binds to a temporary, and the temporary has the
effective height 1. The value of a statement does not bind. `chain k` is the chain of `k`
additions of `x`, so each 63 additions bind one temporary.
-/
def chain (k : Nat) (e : String) : String :=
  (List.range k).foldl (fun e _ => s!"({e} +% x)") e
def coreChain (k : Nat) (e : String) : String :=
  (List.range k).foldl (fun e _ => s!"(add {e} x)") e
def high (k : Nat) : String :=
  "module D() domains() {\n  input x: UInt[8];\n  output y: UInt[8];\n" ++
  s!"  y := {chain k "x"};\n}\n"
def deepText (lets : List String) (y : String) : String := text ([
  "(design D",
  "  (module D",
  "    (input x (bits 8))",
  "    (output y (bits 8))"] ++ lets ++ [s!"    (assign y {y})))"])
#guard sil (high 63) "D" == deepText [] (coreChain 63 "x")
#guard sil (high 64) "D" ==
  deepText [s!"    (let y$0t (bits 8) {coreChain 63 "x"})"] (coreChain 1 "y$0t")
#guard sil (high 127) "D" == deepText [s!"    (let y$0t (bits 8) {coreChain 63 "x"})",
  s!"    (let y$1t (bits 8) {coreChain 63 "y$0t"})"] (coreChain 1 "y$1t")
#guard sil (high 128) "D" == deepText [s!"    (let y$0t (bits 8) {coreChain 63 "x"})",
  s!"    (let y$1t (bits 8) {coreChain 63 "y$0t"})"] (coreChain 2 "y$1t")

/-! The `.sil` text `s` re-parses and passes `Core.check`. -/
def valid (s : String) : Bool :=
  match Core.parse s with
  | .ok d => (Core.check d).toBool
  | .error _ => false

/-! A 4096-high source expression binds 64 temporaries and lowers to valid text. -/
def highText : String := sil (high 4095) "D"
#guard (highText.splitOn "(let y$").length - 1 == 64
#guard valid highText

/-!
A spine of `n` additions whose step `i` adds the chain of `sib i` additions. A taller sibling
lifts the height of the spine past a multiple of 64. A rule on the full height thus binds no node
of the spine. The effective height still binds each 63 levels of the spine.
-/
def branchy (n : Nat) (sib : Nat → Nat) : String :=
  let e := (List.range n).foldl (fun e i => s!"({e} +% {chain (sib i) "x"})") "x"
  "module D() domains() {\n  input x: UInt[8];\n  output y: UInt[8];\n" ++
  s!"  y := {e};\n}\n"
def skip (i : Nat) : Nat :=
  if i == 61 then 64 else if i == 123 then 128 else if i == 185 then 192 else
  if i == 247 then 256 else 0
#guard valid (sil (branchy 257 skip) "D")

/-! Generated branching shapes all lower to text that re-parses and passes `Core.check`. -/
#guard [(300, fun i => i % 70), (300, fun i => i * 7 % 130), (260, fun i => (i * 37) % 66),
  (200, fun i => if i % 2 == 0 then 63 else 64), (257, fun i => skip i + i % 3)].all
  fun (n, f) => valid (sil (branchy n f) "D")

/-!
A core error other than `E008` in the lowered design is a defect of the reference elaborator,
and `elab` exits with code 3. This design refers to an undeclared name.
-/
def broken : String := text [
  "(design D",
  "  (module D",
  "    (output y (bits 8))",
  "    (assign y z)))"]
#guard match Core.parse broken with
  | .ok d =>
    match Flatten.checkDesign d with
    | .error (.defect m) => m.startsWith "error[" && Cli.exitCode (.defect m) == 3
    | _ => false
  | .error _ => false
#guard [Cli.exitCode (.ok ""), Cli.exitCode (.usage ""), Cli.exitCode (.defect "")] == [0, 2, 3]

/-! Each design of these tests that elaborates also passes `Core.check`. -/
#guard [(Test.Elab.counter, "Main"), (Test.Elab.helpers, "M"), (Test.Elab.keywords, "next"),
  (Test.Elab.branch, "M(3, 0)"), (Test.Elab.shared, "M(4)"), (Test.Elab.deepFirst, "Top"),
  (Test.Elab.other, "T"), (Test.Elab.digests, "T"), (Test.Elab.nested, "T"),
  (Test.Elab.ops, "M"), (ops2, "N"), (unroll, "R(3)"), (shifts, "S"), (small, "M")].all
  fun (src, t) => (sil src t).startsWith "(design "

/-!
A shared condition (`Op.share`, section 7.4) binds to one temporary in the statement that lowers
first. Its number comes after the temporaries of the condition itself: here `y$0e$0t` holds the
negation that the `resize` of `SInt` uses twice, so the condition is `y$0e$1t`. The later leaf
statement refers to it.
-/
def shared : String :=
  let p : Pos := ⟨1, 1⟩
  let r (x : String) (t : Ty) : Eval.Hw := .mk p t (.ref ⟨x, []⟩) []
  let neg := Eval.Hw.mk p (.sint 4) (.un .neg) [r "s" (.sint 4)]
  let c := Eval.Hw.mk p .bool (.bin .eq) [.mk p (.sint 8) .resize [neg], r "t" (.sint 8)]
  let m := Eval.Hw.mk p (.uint 8) .mux
    [.mk p .bool (.share 0) [c], r "a" (.uint 8), r "b" (.uint 8)]
  let run : Flatten.FM (List String) := do
    let e₀ ← Flatten.value ⟨"y", [.elem 0]⟩ m
    let e₁ ← Flatten.value ⟨"y", [.elem 1]⟩ m
    return [Core.Text.printExpr e₀, Core.Text.printExpr e₁] ++
      ((← get).temps.toList.map Core.Text.printStmt)
  match run.run { fuel := 1000 } with
  | .ok (xs, _) => text xs
  | .error _ => "error"
#guard shared == text [
  "(mux y$0e$1t a b)",
  "(mux y$0e$1t a b)",
  "(let y$0e$0t (bits 4) (sub (const 4 0) s))",
  "(let y$0e$1t (bits 1) (icmp eq (concat (replicate (extract y$0e$0t 3 1) 4) y$0e$0t) t))"]

/-!
Each leaf of an aggregate lowers to one core node, with the leaf name of section 7.3. The leaves
of a port follow in packing order, so `p$xs$0e` comes before `p$b`. A register leaf takes its
reset constant from the leaf of its value. A named binding takes one version for all its leaves,
as `q$1v$xs$0e` does. A call result names its leaves after `0ret`, and a static leaf gets no
name: the `:=` of `z$1e` lowers it to a constant.
-/
def leaves : String :=
  "struct S { xs: [UInt[8]; 2], b: Bool }\n" ++
  "fn f(x: UInt[8]) -> (UInt[8], Bool) {\n  return (x, true);\n}\n" ++
  "module M() {\n  input p: S;\n  input a: UInt[8];\n  output y: S;\n" ++
  "  output z: (UInt[8], Bool);\n  reg r: [UInt[4]; 3] = [1, 2, 3];\n  r := r;\n" ++
  "  let mut q = p;\n  q = S([a, a], p.b);\n  y := q;\n  z := f(a);\n}\n"
#guard sil leaves "M" == text [
  "(design M",
  "  (module M",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input a (bits 8))",
  "    (input p$xs$0e (bits 8))",
  "    (input p$xs$1e (bits 8))",
  "    (input p$b (bits 1))",
  "    (output y$xs$0e (bits 8))",
  "    (output y$xs$1e (bits 8))",
  "    (output y$b (bits 1))",
  "    (output z$0e (bits 8))",
  "    (output z$1e (bits 1))",
  "    (reg r$0e (bits 4) clock$0clk (reset sync clock$0rst (const 4 1)))",
  "    (reg r$1e (bits 4) clock$0clk (reset sync clock$0rst (const 4 2)))",
  "    (reg r$2e (bits 4) clock$0clk (reset sync clock$0rst (const 4 3)))",
  "    (let f$1c$0ret$0e (bits 8) f$1c$x)",
  "    (let f$1c$x (bits 8) a)",
  "    (let q$1v$b (bits 1) p$b)",
  "    (let q$1v$xs$0e (bits 8) a)",
  "    (let q$1v$xs$1e (bits 8) a)",
  "    (let q$b (bits 1) p$b)",
  "    (let q$xs$0e (bits 8) p$xs$0e)",
  "    (let q$xs$1e (bits 8) p$xs$1e)",
  "    (next r$0e r$0e)",
  "    (next r$1e r$1e)",
  "    (next r$2e r$2e)",
  "    (assign y$b q$1v$b)",
  "    (assign y$xs$0e q$1v$xs$0e)",
  "    (assign y$xs$1e q$1v$xs$1e)",
  "    (assign z$0e f$1c$0ret$0e)",
  "    (assign z$1e (const 1 1))))"]

/-!
A struct skips its empty fields. The other fields keep their names and their order.
-/
def emptyFields : String :=
  "struct E { a: Bool, z: (), e: [Bool; 0], c: UInt[2] }\n" ++
  "module M() domains() {\n  input p: E;\n  output y: E;\n  y := p;\n}\n"
#guard sil emptyFields "M" == text [
  "(design M",
  "  (module M",
  "    (input p$a (bits 1))",
  "    (input p$c (bits 2))",
  "    (output y$a (bits 1))",
  "    (output y$c (bits 2))",
  "    (assign y$a p$a)",
  "    (assign y$c p$c)))"]

/-!
Each leaf of a port charges 1 for its node, then the bytes of its name, before it exists. A leaf
of `x: [Bool; 3]` charges 3: its node, `x`, and `<k>e`. An empty port charges nothing. The walk
makes no list of the leaves, so a port with 2^40 leaves is `S015` at its declaration.
-/
def portOf (n : String) : String := s!"module M() domains() \{\n  input x: [Bool; {n}];\n}\n"
#guard lowering (portOf "3") == lowering (portOf "0") + 9
#guard lowering (portOf "0") == lowering "module M() domains() {\n}\n"
#guard sil (portOf "1 << 40") "M" (fuel := 10000) == "S015 2:3"

/-!
The condition of an aggregate `if` binds once to a temporary of the leaf statement that lowers
first. The second leaf statement refers to it, also in a child connection: `u$a$0e$0t`. The
table of shared conditions starts empty in each module, so `C` and `M` each bind their own. A
child output of an aggregate type lowers to one reference for each leaf.
-/
def shareLeaves : String :=
  "module C() domains() {\n  input c: Bool;\n  input a: (Bool, Bool);\n" ++
  "  output q: (Bool, Bool);\n  q := if (!c) { a } else { (c, c) };\n}\n" ++
  "module M() domains() {\n  input c: Bool;\n  input d: Bool;\n  input a: (Bool, Bool);\n" ++
  "  output y: (Bool, Bool);\n  output z: (Bool, Bool);\n  instance u = C();\n" ++
  "  u.c := c;\n  u.a := if (c && d) { a } else { (d, d) };\n" ++
  "  y := if (c || d) { a } else { u.q };\n  z := u.q;\n}\n"
#guard sil shareLeaves "M" == text [
  "(design M",
  "  (module C",
  "    (input a$0e (bits 1))",
  "    (input a$1e (bits 1))",
  "    (input c (bits 1))",
  "    (output q$0e (bits 1))",
  "    (output q$1e (bits 1))",
  "    (let q$0e$0t (bits 1) (xor c (const 1 1)))",
  "    (assign q$0e (mux q$0e$0t a$0e c))",
  "    (assign q$1e (mux q$0e$0t a$1e c)))",
  "  (module M",
  "    (input a$0e (bits 1))",
  "    (input a$1e (bits 1))",
  "    (input c (bits 1))",
  "    (input d (bits 1))",
  "    (output y$0e (bits 1))",
  "    (output y$1e (bits 1))",
  "    (output z$0e (bits 1))",
  "    (output z$1e (bits 1))",
  "    (inst u C (a$0e (mux u$a$0e$0t a$0e d)) (a$1e (mux u$a$0e$0t a$1e d)) (c c))",
  "    (let u$a$0e$0t (bits 1) (and c d))",
  "    (let y$0e$0t (bits 1) (or c d))",
  "    (assign y$0e (mux y$0e$0t a$0e u.q$0e))",
  "    (assign y$1e (mux y$0e$0t a$1e u.q$1e))",
  "    (assign z$0e u.q$0e)",
  "    (assign z$1e u.q$1e)))"]

/-!
An empty port, register, wire, and child port lower to no core node. Each still has its one
binding. A combinational child keeps its empty module.
-/
def emptyAll : String :=
  "module C() domains() {\n  input p: ();\n  output q: [Bool; 0];\n  q := [];\n}\n" ++
  "module M() {\n  input e: [(); 4];\n  output o: [(); 4];\n  reg r: [Bool; 0] = [];\n" ++
  "  wire w: ((), [UInt[8]; 0]);\n  instance u = C();\n  u.p := ();\n  o := e;\n  r := r;\n" ++
  "  w := ((), []);\n}\n"
#guard sil emptyAll "M" == text [
  "(design M",
  "  (module C)",
  "  (module M",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (inst u C)))"]

/-!
A cycle through one leaf is `S020` at the binding (section 7.5). A dependency between two
different leaves of one wire is not a cycle.
-/
def wire2 (v : String) : String :=
  "module M() domains() {\n  input c: Bool;\n  wire w: (Bool, Bool);\n" ++
  s!"  w := {v};\n  output y: Bool;\n  y := w.1;\n}\n"
#guard sil (wire2 "(c, w.0)") "M" == text [
  "(design M",
  "  (module M",
  "    (input c (bits 1))",
  "    (output y (bits 1))",
  "    (let w$0e (bits 1) c)",
  "    (let w$1e (bits 1) w$0e)",
  "    (assign y w$1e)))"]
#guard sil (wire2 "(w.0, c)") "M" == "S020 4:3"
#guard sil (wire2 "(w.1, w.0)") "M" == "S020 4:3"

/-!
The chain of `==` on an aggregate is as long as its leaf count. Its left spine lowers in a loop,
so a long chain needs no deep recursion. Each 63 links bind one temporary by the height rule.
The interpreter of these tests has a large stack, so these guards check the result, not the
depth of the stack.
-/
def eqLeaves (n : Nat) : String :=
  s!"module M() domains() \{\n  input a: [Bool; {n}];\n  input b: [Bool; {n}];\n" ++
  "  output y: Bool;\n  y := a == b;\n}\n"
#guard valid (sil (eqLeaves 2048) "M")
def andChain (n : Nat) : String :=
  let p : Pos := ⟨1, 1⟩
  let r (x : String) : Eval.Hw := .mk p .bool (.ref ⟨x, []⟩) []
  let h := (List.range n).foldl (fun e _ => Eval.Hw.mk p .bool (.bin .and) [e, r "b"]) (r "a")
  match (Flatten.lower ⟨"y", []⟩ true h).run { fuel := 100000000 } with
  | .ok (_, s) => s!"ok {s.temps.size}"
  | .error _ => "error"
#guard andChain 100000 == "ok 1587"

/-!
The memory block of section 7.6. The memory has the depth `n` and the word type `w`. It has one
read and one write, and `r` binds the response.
-/
def memory (name w : String) (n : Nat) (a : Nat) : String :=
  s!"module M() \{\n  input ra: UInt[{a}];\n  input re: Bool;\n  input wa: UInt[{a}];\n" ++
  s!"  input wd: {w};\n  input we: Bool;\n  output v: Bool;\n" ++
  s!"  mem {name}: [{w}; {n}];\n  let r = read_port({name}, ra, re);\n" ++
  s!"  write_port({name}, wa, wd, we);\n  v := r.valid;\n}\n"

/-! The lowered design before the canonical sort: the statements in the order of the lowering. -/
def raw (src t : String) : String :=
  match Cli.elabChecked {} src t Names.sha16 with
  | .ok c => Core.print c.design
  | .error _ => "error"

/-! The ports and the domain of `memory`, in layout order. -/
def memPorts (a w : Nat) : List String := [
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  s!"    (input ra (bits {a}))",
  "    (input re (bits 1))",
  s!"    (input wa (bits {a}))",
  s!"    (input wd (bits {w}))",
  "    (input we (bits 1))",
  "    (output v (bits 1))"]

/-!
The block of one memory in the order of the lowering. The memory comes first, then the two
response registers and the request `let` values. The two `next` statements and the write come
last. A depth of `2^A` has the `valid` bit `(const 1 1)`.
-/
#guard raw (memory "m" "UInt[8]" 4 2) "M" == text ([
  "(design M",
  "  (module M"] ++ memPorts 2 8 ++ [
  "    (mem m (bits 8) 4 clock$0clk)",
  "    (reg m$0rdata (bits 8) clock$0clk (reset sync clock$0rst (const 8 0)))",
  "    (reg m$0rvalid (bits 1) clock$0clk (reset sync clock$0rst (const 1 0)))",
  "    (let m$0ren (bits 1) re)",
  "    (let m$0raddr (bits 2) ra)",
  "    (next m$0rdata (mux m$0ren (read m m$0raddr) m$0rdata))",
  "    (next m$0rvalid (and m$0ren (const 1 1)))",
  "    (write m 0 wa wd (and we (xor clock$0rst (const 1 1))))",
  "    (let r$data (bits 8) (extract m$0rdata 0 8))",
  "    (let r$valid (bits 1) m$0rvalid)",
  "    (assign v r$valid)))"])

/-!
The memories lower after the registers and before the named `let` values, in declaration order.
-/
def twoMems : String :=
  "module M() {\n  input a: UInt[1];\n  input e: Bool;\n  output y: Bool;\n" ++
  "  reg q: Bool = false;\n  mem b: [Bool; 2];\n  mem a1: [Bool; 2];\n" ++
  "  let x = b.read_port(a, e);\n  b.write_port(a, e, e);\n" ++
  "  let z = a1.read_port(a, e);\n  a1.write_port(a, e, e);\n" ++
  "  q := x.data;\n  y := z.valid;\n}\n"
#guard ((raw twoMems "M").splitOn "\n").filterMap (fun l =>
    let w := (l.trimAsciiStart.toString.splitOn " ").take 2
    if l.startsWith "    (" && !l.startsWith "    (input" && !l.startsWith "    (output" then
      some (" ".intercalate w) else none) == [
  "(reg q", "(mem b", "(reg b$0rdata", "(reg b$0rvalid", "(let b$0ren", "(let b$0raddr",
  "(next b$0rdata", "(next b$0rvalid", "(write b", "(mem a1", "(reg a1$0rdata",
  "(reg a1$0rvalid", "(let a1$0ren", "(let a1$0raddr", "(next a1$0rdata", "(next a1$0rvalid",
  "(write a1", "(let x$data", "(let x$valid", "(let z$data", "(let z$valid", "(next q",
  "(assign y"]

/-! A depth that is not `2^A`, such as 3, 1, or 5, compares the read address with the depth. -/
#guard (sil (memory "m" "UInt[8]" 3 2) "M").splitOn "\n" |>.contains
  "    (next m$0rvalid (and m$0ren (icmp ult m$0raddr (const 2 3))))"
#guard (sil (memory "m" "UInt[8]" 1 1) "M").splitOn "\n" |>.contains
  "    (next m$0rvalid (and m$0ren (icmp ult m$0raddr (const 1 1))))"
#guard (sil (memory "m" "UInt[8]" 2 1) "M").splitOn "\n" |>.contains
  "    (next m$0rvalid (and m$0ren (const 1 1)))"
#guard (sil (memory "m" "UInt[8]" 5 3) "M").splitOn "\n" |>.contains
  "    (next m$0rvalid (and m$0ren (icmp ult m$0raddr (const 3 5))))"

/-!
A word of a record: each leaf is an `extract` at the sum of the widths of the earlier leaves.
The write data is the `concat` chain with the first leaf in the least significant bits. A
second `read_port` is `S018` at the call.
-/
def recordWord : String :=
  "struct W { a: UInt[3], b: Bool, c: SInt[4] }\n" ++
  "module M() {\n  input ra: UInt[2];\n  input re: Bool;\n  input wd: W;\n" ++
  "  output o: W;\n  output q: SInt[4];\n  mem m: [W; 3];\n" ++
  "  let r = m.read_port(ra, re);\n  m.write_port(ra, wd, re);\n" ++
  "  o := r.data;\n  q := m.read_port(ra, re).data.c;\n}\n"
#guard sil recordWord "M" == "S018 12:8"
def recordWord1 : String := recordWord.replace "m.read_port(ra, re).data.c" "r.data.c"
#guard ((sil recordWord1 "M").splitOn "\n").filter (fun l =>
    (l.splitOn "extract").length > 1 || (l.splitOn "(write").length > 1) == [
  "    (let r$data$a (bits 3) (extract m$0rdata 0 3))",
  "    (let r$data$b (bits 1) (extract m$0rdata 3 1))",
  "    (let r$data$c (bits 4) (extract m$0rdata 4 4))",
  "    (write m 0 ra (concat wd$c (concat wd$b wd$a)) (and re (xor clock$0rst (const 1 1))))"]

/-!
An array word: the element `k` is at the offset `k * w`. A static leaf of the data is a constant.
-/
def arrayWord : String :=
  "module M() {\n  input a: UInt[2];\n  input x: UInt[5];\n  output q: UInt[5];\n" ++
  "  mem m: [[UInt[5]; 3]; 4];\n  let r = m.read_port(a, true);\n" ++
  "  m.write_port(a, [x, 7, x], true);\n  q := r.data[2];\n}\n"
#guard ((sil arrayWord "M").splitOn "\n").filter (fun l =>
    (l.splitOn "extract").length > 1 || (l.splitOn "(write").length > 1 ||
    (l.splitOn "$0r").length > 1 && l.startsWith "    (let") == [
  "    (let m$0raddr (bits 2) a)",
  "    (let m$0ren (bits 1) (const 1 1))",
  "    (let r$data$0e (bits 5) (extract m$0rdata 0 5))",
  "    (let r$data$1e (bits 5) (extract m$0rdata 5 5))",
  "    (let r$data$2e (bits 5) (extract m$0rdata 10 5))",
  "    (let r$valid (bits 1) m$0rvalid)",
  "    (write m 0 a (concat x (concat (const 5 7) x)) " ++
    "(and (const 1 1) (xor clock$0rst (const 1 1))))"]

/-!
A word of 200 leaves: the spine of the write data binds `m$<k>t` each time it reaches the height
64. The first temporary holds the leaves 0 to 63, and each later one holds 63 more leaves and
the earlier temporary. The temporaries of the address come first, and those of the enable last.
-/
def wideWord : String :=
  "module M() {\n  input x: [Bool; 200];\n  input a: UInt[3];\n  input c: UInt[8];\n" ++
  "  output v: Bool;\n  mem m: [[Bool; 200]; 8];\n" ++
  "  let r = m.read_port(a >> (c +% c), true);\n" ++
  "  m.write_port(a >> (c +% c), x, (a >> (c +% c)) == a);\n  v := r.valid;\n}\n"

/-! The chain of the leaves `x$<lo>e` to `x$<hi>e` over `base`. -/
def cat (lo hi : Nat) (base : String) : String :=
  (List.range (hi + 1 - lo)).foldl (fun e i => s!"(concat x${lo + i}e {e})") base

/-! The shift `a >> (c +% c)` with the temporary `t` for its count. -/
def shiftBy (t : String) : String :=
  s!"(mux (icmp uge {t} (const 8 3)) (const 3 0) (shru a (extract {t} 0 3)))"

#guard ((sil wideWord "M").splitOn "\n").filter (fun l =>
    l.startsWith "    (write" || l.startsWith "    (let m$0raddr" ||
    ["0", "1", "2", "3", "4"].any (fun k => l.startsWith s!"    (let m${k}t")) == [
  s!"    (let m$0raddr (bits 3) {shiftBy "m$0raddr$0t"})",
  "    (let m$0raddr$0t (bits 8) (add c c))",
  "    (let m$0t (bits 8) (add c c))",
  s!"    (let m$1t (bits 64) {cat 1 63 "x$0e"})",
  s!"    (let m$2t (bits 127) {cat 64 126 "m$1t"})",
  s!"    (let m$3t (bits 190) {cat 127 189 "m$2t"})",
  "    (let m$4t (bits 8) (add c c))",
  s!"    (write m 0 {shiftBy "m$0t"} {cat 190 199 "m$3t"} " ++
    s!"(and (icmp eq {shiftBy "m$4t"} a) (xor clock$0rst (const 1 1))))"]

/-!
A user name alone that equals a core keyword gets the field `0k`, and its role names do not.
The source keyword `mem` cannot name a memory.
-/
#guard ((sil (memory "add" "UInt[8]" 4 2) "M").splitOn "\n").filter (fun l =>
    l.startsWith "    (mem" || l.startsWith "    (next" || l.startsWith "    (write") == [
  "    (mem add$0k (bits 8) 4 clock$0clk)",
  "    (next add$0rdata (mux add$0ren (read add$0k add$0raddr) add$0rdata))",
  "    (next add$0rvalid (and add$0ren (const 1 1)))",
  "    (write add$0k 0 wa wd (and we (xor clock$0rst (const 1 1))))"]
#guard ((sil (memory "read" "UInt[8]" 4 2) "M").splitOn "\n").filter (fun l =>
    l.startsWith "    (mem" || l.startsWith "    (reg") == [
  "    (reg read$0rdata (bits 8) clock$0clk (reset sync clock$0rst (const 8 0)))",
  "    (reg read$0rvalid (bits 1) clock$0clk (reset sync clock$0rst (const 1 0)))",
  "    (mem read$0k (bits 8) 4 clock$0clk)"]
#guard sil (memory "mem" "UInt[8]" 4 2) "M" == "S001 8:7"

/-!
The lowering of `memory` with the depth 4 charges 245 units. The module charges 2, the domain
20, the ports 17, and the block 164. The response lets charge 31, the binding 9, and the design
2. A fuel one unit below the total
gives `S015` at the top selection.
-/
#guard lowering (memory "m" "UInt[8]" 4 2) == 245
#guard sil (memory "m" "UInt[8]" 4 2) "M" (Test.Elab.total (memory "m" "UInt[8]" 4 2) "M" - 1) ==
  "S015 1:1"

/-!
The constructor of a hardware enum (section 7.4). The static tag needs no statement. The payload
is the `concat` chain of its leaves, the first leaf in the low bits, inside zero high bits when
the leaves are narrower than `P`. One leaf of `P` bits is that leaf. The high bits charge 2, a
`concat` and a `const`, and each other `concat` node charges 1. `Op::Pair(c, y)` thus charges 5
more than `Op::Load(x)`: these 3 nodes and one more leaf. A hardware `if` muxes each leaf.
-/
def enumLets (src : String) : List String :=
  ((sil src "M").splitOn "\n").filter (·.startsWith "    (let ")
def opLets (body : String) : List String := enumLets (Test.Elab.hwEnum body)
def opUnits (body : String) : Nat := lowering (Test.Elab.hwEnum body)
#guard opLets "  let a = Op::Load(x);\n" == ["    (let a$payload (bits 8) x)"]
#guard opLets "  let a = Op::Pair(c, y);\n" ==
  ["    (let a$payload (bits 8) (concat (const 3 0) (concat y c)))"]
#guard opUnits "  let a = Op::Pair(c, y);\n" == opUnits "  let a = Op::Load(x);\n" + 5
#guard opLets "  let a = if (c) { Op::Load(x) } else { Op::Pair(c, y) };\n" == [
  "    (let a$payload (bits 8) (mux c x (concat (const 3 0) (concat y c))))",
  "    (let a$tag (bits 2) (mux c (const 2 1) (const 2 2)))"]

/-!
A payload of 70 leaves is one `concat` chain. The loop builds it from the first leaf, and the
chain so far binds to a temporary when its height reaches 64.
-/
def wideEnum : String :=
  "enum W: UInt[1] { A([Bool; 70]) = 1 }\nmodule M() {\n  input x: [Bool; 70];\n" ++
  "  output o: Bool;\n  let a = W::A(x);\n  o := true;\n}\n"
#guard enumLets wideEnum == [
  "    (let a$payload (bits 70) " ++ cat 64 69 "a$payload$0t" ++ ")",
  "    (let a$payload$0t (bits 64) " ++ cat 1 63 "x$0e" ++ ")"]

/-!
`reinterpret` between an enum and its bits (section 7.4). The pack is `(concat payload tag)`. The
unpack is `(extract b 0 W)` and `(extract b W P)`. Both leaves refer to a core name `b`. Another
`b` binds to one temporary of the leaf statement that lowers first (G8), so a round trip refers to
it twice.
-/
#guard opLets "  let d = Op::Pair(c, y);\n  let a = reinterpret(UInt[10], d);\n" == [
  "    (let a (bits 10) (concat d$payload (const 2 2)))",
  "    (let d$payload (bits 8) (concat (const 3 0) (concat y c)))"]
#guard opLets "  let b = resize(UInt[10], x);\n  let a = reinterpret(Op, b);\n" == [
  "    (let a$payload (bits 8) (extract b 2 8))",
  "    (let a$tag (bits 2) (extract b 0 2))",
  "    (let b (bits 10) (concat (const 2 0) x))"]
#guard opLets "  let a = reinterpret(Op, resize(UInt[10], x));\n" == [
  "    (let a$payload (bits 8) (extract a$tag$0t 2 8))",
  "    (let a$tag (bits 2) (extract a$tag$0t 0 2))",
  "    (let a$tag$0t (bits 10) (concat (const 2 0) x))"]
#guard opLets "  let a = reinterpret(UInt[10], reinterpret(Op, resize(UInt[10], x)));\n" == [
  "    (let a (bits 10) (concat (extract a$0t 2 8) (extract a$0t 0 2)))",
  "    (let a$0t (bits 10) (concat (const 2 0) x))"]

/-!
`k` nested round trips bind `k` more temporaries, one for each shared operand. Each level adds
21 units: the temporary 6, the `concat` 1, two `extract` nodes 2, and two references to the
temporary 12. The output and the charge thus stay linear, where copies would give `2^k` nodes.
-/
def trips (k : Nat) : String :=
  let b := "reinterpret(Op, resize(UInt[10], x))"
  Test.Elab.hwEnum s!"  let a = {Test.Elab.roundTrips k b};\n"
#guard (List.range 20).all fun k => (enumLets (trips k)).length == k + 3
#guard (List.range 20).all fun k => lowering (trips (k + 1)) == lowering (trips k) + 21

/-!
With `P` 0, a conversion makes no core node: the unpack is `b`, and the pack is the tag.
-/
#guard enumLets (Test.Elab.flagE
    "  let a = reinterpret(E, u +% 1);\n  let b = reinterpret(UInt[2], a);\n") == [
  "    (let a$tag (bits 2) (add u (const 2 1)))",
  "    (let b (bits 2) a$tag)"]

end Silicon.Source.Test.Flatten
