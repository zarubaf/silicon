-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli
import Silicon.Source.Test.Elab
import Silicon.Core.Interp.Named

/-!
These tests check the source vectors of section 11.2 of the front-end spec. They cover the port
schema, the values of each type, and the faults of an input line. They also run the counter and
registers with a nonzero reset value.
-/

namespace Silicon.Source.Test.Vectors

open Silicon.Source

/-!
The output lines of `run` for the input lines `lines`, from the zero state. A fault of an input
line gives its message instead.
-/
def run (src t : String) (lines : List String) : String :=
  match Cli.runSetup {} src t with
  | .error (.error e) => s!"{e.code} {e.pos.line}:{e.pos.col}"
  | .error _ => "failure"
  | .ok (s, d) =>
    if h : d.design.externs = [] then
      match lines.mapM (Vectors.parseLine s) with
      | .ok ins => String.join ((Core.namedRun d ins h).map (Vectors.printLine s))
      | .error m => m
    else "extern"

/-! The source names and the core names of the schema of `src` with the top `t`. -/
def names (src t : String) : List (String × String) × List (String × String) :=
  match Cli.runSetup {} src t with
  | .ok (s, _) =>
    let pair (e : Vectors.Entry) := (e.name, e.core)
    (s.inputs.map pair, s.outputs.map pair)
  | .error _ => ([], [])

/-! The text of `lines`, one line each. -/
def text (lines : List String) : String := String.join (lines.map (· ++ "\n"))

/-!
The reset comes first, then the inputs in byte order of their names. A keyword port keeps its
source name in a vector, and its core name has `$0k`.
-/
def ports : String :=
  "module P() {\n  input zz: Bool;\n  input add: UInt[4];\n  input a_b: Bool;\n" ++
  "  output y: UInt[4];\n  output mux: Bool;\n  y := add;\n  mux := zz && a_b;\n}\n"

#guard names ports "P" ==
  ([("clock$0rst", "clock$0rst"), ("a_b", "a_b"), ("add", "add$0k"), ("zz", "zz")],
   [("mux", "mux$0k"), ("y", "y")])
#guard run ports "P" ["in=(clock$0rst false a_b true add 9 zz true)"] ==
  "out=(mux true y 9)\n"

/-! A combinational top has no reset entry. -/
def comb : String :=
  "module C() domains() {\n  input a: SInt[4];\n  output b: SInt[4];\n  b := -a;\n}\n"

#guard names comb "C" == ([("a", "a")], [("b", "b")])
#guard run comb "C" ["in=(a -8)", "in=(a 7)", "in=(a 0)", "in=(a -0)", "in=(a -1)"] ==
  text ["out=(b -8)", "out=(b -7)", "out=(b 0)", "out=(b 0)", "out=(b 1)"]

/-! The values of each type. An input value can have leading zeros. -/
#guard (Vectors.parseValue "x" .bool "true").toOption == some 1
#guard (Vectors.parseValue "x" .bool "false").toOption == some 0
#guard (Vectors.parseValue "x" .bool "1").toOption == none
#guard (Vectors.parseValue "x" (.uint 8) "255").toOption == some 255
#guard (Vectors.parseValue "x" (.uint 8) "007").toOption == some 7
#guard (Vectors.parseValue "x" (.uint 8) "256").toOption == none
#guard (Vectors.parseValue "x" (.uint 8) "-1").toOption == none
#guard (Vectors.parseValue "x" (.uint 8) "+1").toOption == none
#guard (Vectors.parseValue "x" (.sint 8) "-128").toOption == some 128
#guard (Vectors.parseValue "x" (.sint 8) "-1").toOption == some 255
#guard (Vectors.parseValue "x" (.sint 8) "127").toOption == some 127
#guard (Vectors.parseValue "x" (.sint 8) "128").toOption == none
#guard (Vectors.parseValue "x" (.sint 8) "-129").toOption == none
#guard (Vectors.parseValue "x" (.sint 8) "-").toOption == none
#guard (Vectors.parseValue "x" (.sint 1) "-1").toOption == some 1
#guard (Vectors.parseValue "x" (.sint 1) "1").toOption == none
#guard [Vectors.valueText .bool 1, Vectors.valueText (.uint 8) 255, Vectors.valueText (.sint 8) 255,
  Vectors.valueText (.sint 8) 128, Vectors.valueText (.sint 8) 127] ==
  ["true", "255", "-1", "-128", "127"]

/-! The faults of an input line, with the tokenization of a core vector. -/
#guard run comb "C" ["in=(a 1"] == "expected in=(...)"
#guard run comb "C" ["in=()"] == "missing input"
#guard run comb "C" ["in=(a 1 b 2)"] == "extra input tokens"
#guard run comb "C" ["in=(b 1)"] == "expected input a"
#guard run comb "C" ["in=(a 1)\r"] == "invalid input line ending"
#guard run comb "C" ["in=(a 8)"] == "input a exceeds its width"
#guard run ports "P" ["in=(clock$0rst false add 1 a_b true zz true)"] == "expected input a_b"
#guard run ports "P" ["in=(a_b true add 1 zz true)"] == "expected input clock$0rst"
#guard run ports "P" [" in=(\tclock$0rst  false a_b false add 1 zz false ) "] ==
  "out=(mux false y 1)\n"

/-! The counter of the v0.1 README counts after its reset and wraps at its width. -/
def counterRun : String :=
  run Test.Elab.counter "Counter(2)" [
    "in=(clock$0rst true enable true)", "in=(clock$0rst false enable true)",
    "in=(clock$0rst false enable true)", "in=(clock$0rst false enable false)",
    "in=(clock$0rst false enable true)", "in=(clock$0rst false enable true)",
    "in=(clock$0rst false enable true)"]

#guard counterRun == text [
  "out=(full false value 0)", "out=(full false value 0)", "out=(full false value 1)",
  "out=(full false value 2)", "out=(full false value 2)", "out=(full true value 3)",
  "out=(full false value 0)"]

/-! The counter as a child of `Main`: the reset of the domain reaches the child. -/
#guard run Test.Elab.counter "Main" [
  "in=(clock$0rst true enable true)", "in=(clock$0rst false enable true)",
  "in=(clock$0rst false enable true)"] ==
  text ["out=(value 0)", "out=(value 0)", "out=(value 1)"]

/-!
The registers of section 11.2. Before the first reset edge, each register has the value 0 of the
test convention. After it, `r` has its reset value 42 and `q` of type `SInt[8]` has -1.
-/
def regs : String :=
  "module Regs() {\n  input load: Bool;\n  output u: UInt[8];\n  output s: SInt[8];\n" ++
  "  reg r: UInt[8] = 42;\n  reg q: SInt[8] = -1;\n" ++
  "  r := if (load) { r +% 1 } else { r };\n  q := if (load) { q -% 1 } else { q };\n" ++
  "  u := r;\n  s := q;\n}\n"

#guard run regs "Regs" [
  "in=(clock$0rst false load true)", "in=(clock$0rst false load false)",
  "in=(clock$0rst true load true)", "in=(clock$0rst false load false)",
  "in=(clock$0rst false load true)", "in=(clock$0rst false load true)"] == text [
  "out=(s 0 u 0)", "out=(s -1 u 1)", "out=(s -1 u 1)", "out=(s -1 u 42)",
  "out=(s -1 u 42)", "out=(s -2 u 43)"]

/-! A source that the reference elaborator rejects gives its first error. -/
#guard run "module R() domains() {\n  reg r: Bool = false;\n}\n" "R" [] == "S017 2:3"

end Silicon.Source.Test.Vectors
