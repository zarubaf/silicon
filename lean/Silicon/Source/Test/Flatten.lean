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

end Silicon.Source.Test.Flatten
