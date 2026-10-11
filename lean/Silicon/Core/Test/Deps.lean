-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Deps
import Silicon.Core.Text

/-! These tests check port dependencies and memory address cycles. -/
namespace Silicon.Core.Test.Deps

private def moduleOf (source : String) : Module :=
  match parse ("(design top " ++ source ++ ")") with
  | .ok { items := [.module m], .. } => m
  | _ => default

private def stateModule : Module := moduleOf
  ("(module top (input clk clock) (input x (bits 1)) (output q (bits 1)) " ++
   "(reg r (bits 1) clk (reset sync x x)) (next r x) (assign q r))")

#guard Deps.infer stateModule (fun _ => none) == [("q", [])]

/-! Child outputs read only the connections in their dependency lists. -/
private def parent : Module := moduleOf
  ("(module top (input clk clock) (input z (bits 1)) (input a (bits 1)) " ++
   "(output second (bits 1)) (output first (bits 1)) " ++
   "(assign first u.q) (assign second u.r) " ++
   "(inst u child (clk clk) (x (and a z)) (y u.r)))")

#guard Deps.infer parent (fun n =>
  if n == "child" then some [("q", ["x"]), ("r", [])] else none) ==
  [("second", []), ("first", ["z", "a"])]

/-! An extern supplies its declared dependencies through the same interface. -/
private def external : Extern :=
  ⟨⟨1, 1, []⟩, "child",
    [⟨⟨1, 1, []⟩, .input, "clk", .clock⟩, ⟨⟨1, 1, []⟩, .input, "x", .bits 1⟩,
     ⟨⟨1, 1, []⟩, .input, "y", .bits 1⟩, ⟨⟨1, 1, []⟩, .output, "q", .bits 1⟩,
     ⟨⟨1, 1, []⟩, .output, "r", .bits 1⟩],
    [⟨⟨1, 1, []⟩, "q", ["x"]⟩, ⟨⟨1, 1, []⟩, "r", []⟩]⟩

#guard Deps.infer parent (fun n =>
  if n == external.name then some (external.deps.map fun d => (d.output, d.inputs))
  else none) == [("second", []), ("first", ["z", "a"])]

/-! All operand reads remain dependencies, even if a constant fixes the result. -/
private def expressions : Module := moduleOf
  ("(module top (input clk clock) (input z (bits 1)) (input a (bits 1)) " ++
   "(input unused (bits 1)) (output q (bits 1)) " ++
   "(assign q (mux (icmp eq z z) (extract (replicate (not v) 1) 0 1) " ++
   "(read ram a))) (let v (bits 1) (and a (const 1 0))) " ++
   "(mem ram (bits 1) 2 clk) (write ram 0 unused unused unused))")

#guard Deps.infer expressions (fun _ => none) == [("q", ["z", "a"])]
#guard Deps.infer { expressions with body := expressions.body.reverse } (fun _ => none) ==
  [("q", ["z", "a"])]

/-! A memory address can make an edge from a value to itself. -/
private def selfRead : Module := moduleOf
  ("(module top (input clk clock) (output q (bits 1)) " ++
   "(mem m (bits 1) 2 clk) (let a (bits 1) (read m a)) (assign q a))")

#guard ((Deps.graph selfRead (fun _ => none)).lookup (.name "a")) ==
  some [.name "a"]
#guard Deps.infer selfRead (fun _ => none) == [("q", [])]

/-! A child's memory address retains feedback through its parent connection. -/
private def child : Module := moduleOf
  ("(module child (input clk clock) (input addr (bits 1)) (output q (bits 1)) " ++
   "(mem m (bits 1) 2 clk) (assign q (read m addr)))")

private def feedback : Module := moduleOf
  ("(module top (input clk clock) (input x (bits 1)) (output q (bits 1)) " ++
   "(assign q u.q) (inst u child (clk clk) (addr (or u.q x))))")

private def children (n : String) : Option Deps :=
  if n == "child" then some (Deps.infer child (fun _ => none)) else none

#guard Deps.infer child (fun _ => none) == [("q", ["addr"])]
#guard ((Deps.graph feedback children).lookup (.port "u" "q")) ==
  some [.port "u" "q", .name "x"]
#guard Deps.infer feedback children == [("q", ["x"])]

/-! Long paths and repeated branches retain an input exactly once. -/
private def chain : Module :=
  let p : Pos := ⟨1, 1, []⟩
  let name := fun n : Nat => "v" ++ toString n
  { pos := p, name := "top",
    ports := [⟨p, .input, name 0, .bits 1⟩, ⟨p, .output, "q", .bits 1⟩],
    body := .assign p "q" (.ref p (name 40)) ::
      (List.range 40).map fun n =>
        .let_ p (name (n + 1)) 1 (.bin p .or (.ref p (name n)) (.ref p (name n))) }

#guard Deps.infer chain (fun _ => none) == [("q", ["v0"])]
#guard ((Deps.graph stateModule (fun _ => none)).lookup (.name "q")) == some []

/-! A constant address reads no input. Clocks cannot enter a dependency list. -/
private def fixedAddress : Module := moduleOf
  ("(module top (input clk clock) (input x (bits 1)) (output q (bits 1)) " ++
   "(mem m (bits 1) 2 clk) (write m 0 x x x) (assign q (read m (const 1 0))))")

#guard Deps.infer fixedAddress (fun _ => none) == [("q", [])]
#guard Deps.infer parent (fun _ => some [("q", ["clk"]), ("r", [])]) ==
  [("second", []), ("first", [])]

end Silicon.Core.Test.Deps
