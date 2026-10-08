import Silicon.Core.Check
import Silicon.Core.Text

/-! These tests check error codes, source lines, and pass order. -/
namespace Silicon.Core.Test.Check

private def result (source : String) : Option (ErrorCode × Nat) :=
  match parse source >>= check with
  | .ok _ => none
  | .error e => some (e.code, e.pos.line)

#guard result "(design top (module top (input x (bits 1))\n(input x (bits 1))))" ==
  some (.E002, 2)
#guard result "(design top (module top\n(let x (bits 1) missing)))" == some (.E003, 2)
#guard result "(design top (module top\n(let x (bits 2) (const 1 0))))" == some (.E004, 2)
#guard result "(design top (module top\n(input x (bits 0))))" == some (.E005, 2)
#guard result "(design top (module top (input clk clock)\n(reg r (bits 1) clk)))" ==
  some (.E006, 2)
#guard result "(design top (module top\n(output q (bits 1))))" == some (.E007, 2)
#guard result "(design top (module top\n(let x (bits 1) x)))" == some (.E008, 2)
#guard result "(design top (module top (input clk clock)\n(input other clock)))" ==
  some (.E009, 2)
#guard result "(design top (module top\n(inst u top)))" == some (.E010, 2)
#guard result ("(design top (module child (input x (bits 1)))\n" ++
  "(module top (inst u child)))") == some (.E011, 2)
#guard result ("(design top (module top (input clk clock)\n" ++
  "(mem m (bits 1) 2 clk)\n(write m 1 (const 1 0) (const 1 0) (const 1 0))))") ==
  some (.E012, 2)
#guard result "(design top (module top)\n(extern child (output q (bits 1))))" ==
  some (.E013, 2)

/-! A prior pass wins even when its error occurs later in the file. -/
#guard result ("(design top (module top\n(let x (bits 2) (const 1 0))\n" ++
  "(let y (bits 1) missing)))") == some (.E003, 3)

/-! The counter uses a reset, a forward reference, and one state update. -/
#guard result ("(design counter (module counter (input clk clock) (input rst (bits 1)) " ++
  "(input en (bits 1)) (output q (bits 8)) " ++
  "(reg r (bits 8) clk (reset sync rst (const 8 0))) " ++
  "(let inc (bits 8) (add r (const 8 1))) (next r (mux en inc r)) (assign q r)))") == none

/-! Separate output dependencies permit a handshake between sibling instances. -/
#guard result ("(design top " ++
  "(module child (input x (bits 1)) (output q (bits 1)) (output r (bits 1)) " ++
  "(assign q (const 1 0)) (assign r x)) " ++
  "(module top (inst a child (x b.q)) (inst b child (x a.q))))") == none

/-! Feedback through an instance or a memory address remains a cycle. -/
#guard result ("(design top (module child (input x (bits 1)) (output q (bits 1)) " ++
  "(assign q x))\n(module top\n(inst u child (x u.q))))") == some (.E008, 3)
#guard result ("(design top (module top (input clk clock) (mem m (bits 1) 2 clk)\n" ++
  "(let a (bits 1) (read m a))))") == some (.E008, 2)
#guard result "(design top (module top\n(input silicon_x (bits 1))))" == some (.E002, 2)

/-! Atom positions survive line breaks inside declaration and expression forms. -/
#guard result "(design top (module top (input\nsilicon_x (bits 1))))" == some (.E002, 2)
#guard result "(design top (module top (input x (bits\n0))))" == some (.E005, 2)
#guard result "(design top (module top (let x (bits 1) (const 1\n2))))" == some (.E005, 2)
#guard result "(design\nmissing (module top))" == some (.E003, 2)
#guard result ("(design top (module top) (extern child (input x (bits 1)) " ++
  "(output q (bits 1)) (deps q (x\nx))))") == some (.E013, 2)

/-! Clock connections obey the name pass before the clock and connection passes. -/
#guard result ("(design top (module child (input clk clock)) " ++
  "(module top (inst u child (clk missing))))") == some (.E003, 1)
#guard result ("(design top (module child (input clk clock)) " ++
  "(module top (input clk clock) (inst u child (clk (not clk)))))") == some (.E009, 1)
#guard result ("(design top (module child (input clk clock)) " ++
  "(module top (inst u child (clk (const 1 0)))))") == some (.E011, 1)
#guard result ("(design top (module child (input clk clock)) " ++
  "(module top (input clk clock) (inst u child (clk clk))))") == none
#guard result "(design top (module top (output clk clock) (let x (bits 1) clk)))" ==
  some (.E009, 1)

/-! The type pass reports only forms whose operands have valid types. -/
#guard result ("(design top (module top (let x (bits 2) (add\n" ++
  "(mux (const 2 0) (const 1 0) (const 1 0)) (const 3 0)))))") == some (.E004, 2)
#guard result ("(design top (module top (let x (bits 1) (extract (const 1 0) 1 1))))") ==
  some (.E004, 1)
#guard result ("(design top (module top (let x (bits 1) (replicate (const 1 0) 0))))") ==
  some (.E005, 1)
#guard result ("(design top (module top (let x (bits 1) " ++
  "(concat (const 65536 0) (const 1 0)))))") == some (.E004, 1)

/-! Missing and duplicate equations share a pass and compete by source position. -/
#guard result ("(design top (module top (input clk clock) (mem m (bits 1) 2 clk)\n" ++
  "(write m 0 (const 2 0)\n(add (const 1 0) (const 2 0)) (const 1 0))))") ==
  some (.E004, 3)
#guard result ("(design top (module child (input x (bits 1))) " ++
  "(module top (inst u child\n(x (const 2 0)))))") == some (.E004, 2)
#guard result ("(design top (module top (input clk clock) (reg r (bits 1) clk\n" ++
  "(reset sync (const 2 0) (const 1 0))) (next r (const 1 0))))") == some (.E004, 2)

#guard result ("(design top (module top (input clk clock)\n(output q (bits 1))\n" ++
  "(reg r (bits 1) clk)))") == some (.E007, 2)
#guard result ("(design top (module top (input clk clock) (reg r (bits 1) clk)\n" ++
  "(next r (const 1 0))\n(next r (const 1 0))))") == some (.E006, 3)
#guard result ("(design top (module top (output q (bits 1))\n" ++
  "(assign q (const 1 0))\n(assign q (const 1 0))))") == some (.E007, 3)
#guard result ("(design top (module top (input clk clock) (mem m (bits 1) 2 clk)\n" ++
  "(write m 0 (const 1 0) (const 1 0) (const 1 0))\n" ++
  "(write m 0 (const 1 0) (const 1 0) (const 1 0))))") == some (.E012, 3)

/-! Cycle errors exclude nodes that only depend on a cycle. -/
#guard result ("(design top (module top\n(let early (bits 1) a)\n" ++
  "(let a (bits 1) b)\n(let b (bits 1) a)))") == some (.E008, 3)
#guard result ("(design top (module top\n(inst early child))\n" ++
  "(module child\n(inst cycle child)))") == some (.E010, 4)

/-! Memory address widths round up and stay at least one. -/
#guard result ("(design top (module top (input clk clock) " ++
  "(mem m (bits 1) 3 clk) (let x (bits 1) (read m (const 1 0)))))") == some (.E004, 1)
#guard result ("(design top (module top (input clk clock) " ++
  "(mem m (bits 1) 1 clk) (let x (bits 1) (read m (const 1 0)))))") == none

/-! All items receive checks, including an item outside the top hierarchy. -/
#guard result ("(design top (module top)\n(module unused (let x (bits 1) missing)))") ==
  some (.E003, 2)
#guard result ("(design top (module top) (extern child (input clk clock) " ++
  "(output q (bits 1)) (deps q (\nclk))))") == some (.E013, 2)
#guard result ("(design top (module top) (extern child (output q (bits 1)) " ++
  "(deps q ())\n(deps q ())))") == some (.E013, 2)

/-! Elaboration puts children first even when the file lists the parent first. -/
#guard ((parse "(design top (module top (inst u child)) (module child))" >>= check).toOption.map
  fun d => d.bodies.map (·.source.name)) == some ["child", "top"]

/-! Extern dependency tables follow port order, not dependency entry order. -/
#guard ((parse ("(design top (module top) (extern child " ++
  "(input a (bits 1)) (input b (bits 1)) (output q (bits 1)) (output r (bits 1)) " ++
  "(deps r ()) (deps q (b a))))")).toOption.map
  fun d => Typed.designDeps d (d.items.length + 1) "child") ==
  some (some [("q", ["a", "b"]), ("r", [])])

end Silicon.Core.Test.Check
