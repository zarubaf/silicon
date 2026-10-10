import Silicon.Source.Test.Flatten

/-!
These tests check `validate` (section 8 of the front-end spec). An output equal to the reference
gives `ok`, also in another order of items and statements. A changed byte gives the first line
that differs. A core error of the output, and a rejection of the source, give their error lines.
-/

namespace Silicon.Source.Test.Validate

open Silicon.Source

/-! The printed result of `validate` and its exit code. -/
def validate (src t out : String) : String × UInt32 :=
  let r := Cli.validateText {} src t out
  let text := match r with
    | .ok text => text
    | .error e => s!"{e.code} {e.pos.line}:{e.pos.col}"
    | .reject line => line
    | .usage _ => "usage"
    | .defect m => s!"defect {m}"
  (text, Cli.exitCode r)

def text := Flatten.text

def reference : String := Flatten.sil Flatten.twoCounters "Main"

/-! The output of the reference elaborator itself validates. -/
#guard validate Flatten.twoCounters "Main" reference == ("ok\n", 0)
#guard validate Test.Elab.counter "Counter(8)" (Flatten.sil Test.Elab.counter "Counter(8)") ==
  ("ok\n", 0)

/-! A changed byte gives the first line that differs, with both lines, and exit code 1. -/
#guard validate Flatten.twoCounters "Main" (reference.replace "(const 4 15)" "(const 4 14)") ==
  ("mismatch at line 20: expected `    (assign full (icmp eq count (const 4 15)))`, " ++
    "found `    (assign full (icmp eq count (const 4 14)))`", 1)

/-! A line that only one text has shows `<end>` on the other side. -/
#guard Cli.mismatch ["a", "b"] ["a"] 1 == "mismatch at line 2: expected `b`, found <end>"
#guard Cli.mismatch ["a"] ["a", "b"] 1 == "mismatch at line 2: expected <end>, found `b`"

/-! An extra module is a mismatch, also when the core checker accepts it. -/
#guard (validate Flatten.twoCounters "Main"
  (reference.replace "  (module Main" "  (module Extra)\n  (module Main")).2 == 1

/-!
Another order of the items, the statements, and the connections is equivalent. `validate`
compares the canonical texts, so it gives `ok`.
-/
def reordered : String := text [
  "(design Main",
  "  (module Main",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output value (bits 4))",
  "    (assign value a.value)",
  "    (inst b Counter$2 (enable (xor enable (const 1 1))) (clock$0rst clock$0rst)",
  "      (clock$0clk clock$0clk))",
  "    (inst a Counter$4 (clock$0clk clock$0clk) (enable enable) (clock$0rst clock$0rst)))",
  "  (module Counter$4",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output full (bits 1))",
  "    (output value (bits 4))",
  "    (assign value count)",
  "    (assign full (icmp eq count (const 4 15)))",
  "    (next count (mux enable (add count (const 4 1)) count))",
  "    (reg count (bits 4) clock$0clk (reset sync clock$0rst (const 4 0))))",
  "  (module Counter$2",
  "    (input clock$0clk clock)",
  "    (input clock$0rst (bits 1))",
  "    (input enable (bits 1))",
  "    (output full (bits 1))",
  "    (output value (bits 2))",
  "    (next count (mux enable (add count (const 2 1)) count))",
  "    (reg count (bits 2) clock$0clk (reset sync clock$0rst (const 2 0)))",
  "    (assign value count)",
  "    (assign full (icmp eq count (const 2 3)))))"]

#guard reordered != reference
#guard validate Flatten.twoCounters "Main" reordered == ("ok\n", 0)

/-! Another port order is another interface, so it is a mismatch. -/
#guard (validate Flatten.twoCounters "Main" (reordered.replace
  "    (output full (bits 1))\n    (output value (bits 4))"
  "    (output value (bits 4))\n    (output full (bits 1))")).2 == 1

/-! An output that the core parser or the core checker rejects gives its core error line. -/
#guard validate Flatten.twoCounters "Main" (reference.replace "(assign value a.value)" "(assign") ==
  ("error[E001]: 29:12: unexpected token", 1)
#guard validate Flatten.twoCounters "Main"
  (reference.replace "(assign value a.value)" "(assign value a.nothing)") ==
  ("error[E003]: 29:19: expected an instance output", 1)

/-! A source that the reference elaborator rejects gives its error, before the output is read. -/
#guard validate "module R() domains() {\n  reg r: Bool = false;\n}\n" "R" "" == ("S017 2:3", 1)
#guard validate Flatten.twoCounters "Main(1)" reference == ("S007 1:1", 1)
#guard validate Flatten.twoCounters "Nothing" reference == ("usage", 2)

end Silicon.Source.Test.Validate
