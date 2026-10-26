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

/-!
The schema has one entry for each leaf of a port, in packing order. An entry names the port, then
`.field` for a record field and `.index` for an array index or a tuple element. The core name
uses the leaf fields of section 7.3 instead. A keyword port with leaves keeps its source name:
`add.a` is the leaf `a` of `add`, and no name has `0k`.
-/
def leafPorts : String :=
  "struct S { a: Bool, b: UInt[4] }\n" ++
  "struct P { hdr: (UInt[4], Bool), data: [S; 2] }\n" ++
  "module L() domains() {\n  input xs: [UInt[4]; 2];\n  input t: (Bool, SInt[4]);\n" ++
  "  input add: S;\n  input pkt: P;\n  output y: P;\n  output mux: [Bool; 1];\n" ++
  "  y := pkt;\n  mux := [add.a];\n}\n"

#guard names leafPorts "L" ==
  ([("add.a", "add$a"), ("add.b", "add$b"), ("pkt.hdr.0", "pkt$hdr$0e"),
    ("pkt.hdr.1", "pkt$hdr$1e"), ("pkt.data.0.a", "pkt$data$0e$a"),
    ("pkt.data.0.b", "pkt$data$0e$b"), ("pkt.data.1.a", "pkt$data$1e$a"),
    ("pkt.data.1.b", "pkt$data$1e$b"), ("t.0", "t$0e"), ("t.1", "t$1e"),
    ("xs.0", "xs$0e"), ("xs.1", "xs$1e")],
   [("mux.0", "mux$0e"), ("y.hdr.0", "y$hdr$0e"), ("y.hdr.1", "y$hdr$1e"),
    ("y.data.0.a", "y$data$0e$a"), ("y.data.0.b", "y$data$0e$b"),
    ("y.data.1.a", "y$data$1e$a"), ("y.data.1.b", "y$data$1e$b")])

/-!
An empty port and an empty leaf have no entry. A record skips its empty fields, and the others
keep their order.
-/
def emptyPorts : String :=
  "struct E { a: Bool, z: (), e: [Bool; 0], c: (UInt[2], ()) }\n" ++
  "module M() {\n  input u: ();\n  input n: [UInt[8]; 0];\n  input p: E;\n" ++
  "  output o: ();\n  output y: E;\n  o := ();\n  y := p;\n}\n"

#guard names emptyPorts "M" ==
  ([("clock$0rst", "clock$0rst"), ("p.a", "p$a"), ("p.c.0", "p$c$0e")],
   [("y.a", "y$a"), ("y.c.0", "y$c$0e")])
#guard run emptyPorts "M" ["in=(clock$0rst false p.a true p.c.0 2)"] ==
  "out=(y.a true y.c.0 2)\n"
#guard run emptyPorts "M" ["in=(clock$0rst false p$a true p.c.0 2)"] == "expected input p.a"

/-!
A vector runs through an aggregate design by leaf. The register `r` of a record type takes the
reset value of each leaf, and `swap` exchanges the elements of a tuple. Each leaf value has the
form of its scalar type.
-/
def aggRun : String :=
  "struct R { n: UInt[4], s: SInt[4], f: Bool }\n" ++
  "module A() {\n  input t: (UInt[4], UInt[4]);\n  input v: R;\n" ++
  "  output swap: (UInt[4], UInt[4]);\n" ++
  "  output q: R;\n  output eq: Bool;\n  reg r: R = R(5, -2, true);\n  r := v;\n" ++
  "  swap := (t.1, t.0);\n  q := r;\n  eq := r == v;\n}\n"

#guard run aggRun "A" [
  "in=(clock$0rst true t.0 1 t.1 2 v.n 3 v.s -4 v.f false)",
  "in=(clock$0rst false t.0 9 t.1 0 v.n 3 v.s -4 v.f false)",
  "in=(clock$0rst false t.0 9 t.1 0 v.n 7 v.s 7 v.f true)",
  "in=(clock$0rst false t.0 9 t.1 0 v.n 7 v.s 7 v.f true)"] == text [
  "out=(eq false q.n 0 q.s 0 q.f false swap.0 2 swap.1 1)",
  "out=(eq false q.n 5 q.s -2 q.f true swap.0 0 swap.1 9)",
  "out=(eq false q.n 3 q.s -4 q.f false swap.0 0 swap.1 9)",
  "out=(eq true q.n 7 q.s 7 q.f true swap.0 0 swap.1 9)"]
#guard run aggRun "A" ["in=(clock$0rst true t.0 1 t.1 2 v.n 3 v.s -9 v.f false)"] ==
  "input v.s exceeds its width"

/-! A source that the reference elaborator rejects gives its first error. -/
#guard run "module R() domains() {\n  reg r: Bool = false;\n}\n" "R" [] == "S017 2:3"

/-!
An enum port has the entries `<port>.tag` and `<port>.payload`, and an empty payload has no
entry (section 11.2). Each value is a `UInt`, so a tag needs no variant. A register of an enum
resets each leaf.
-/
def enums : String :=
  "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\nenum F: UInt[1] { A = 0, B = 1 }\n" ++
  "module E() {\n  input op: Op;\n  input f: F;\n  output q: Op;\n  output g: F;\n" ++
  "  reg r: Op = Op::Load(7);\n  r := op;\n  q := r;\n  g := f;\n}\n"

#guard names enums "E" ==
  ([("clock$0rst", "clock$0rst"), ("f.tag", "f$tag"), ("op.tag", "op$tag"),
    ("op.payload", "op$payload")],
   [("g.tag", "g$tag"), ("q.tag", "q$tag"), ("q.payload", "q$payload")])
#guard run enums "E" [
    "in=(clock$0rst true f.tag 1 op.tag 3 op.payload 200)",
    "in=(clock$0rst false f.tag 0 op.tag 3 op.payload 200)",
    "in=(clock$0rst false f.tag 1 op.tag 0 op.payload 9)"] == text [
  "out=(g.tag 1 q.tag 0 q.payload 0)",
  "out=(g.tag 0 q.tag 1 q.payload 7)",
  "out=(g.tag 1 q.tag 3 q.payload 200)"]
#guard run enums "E" ["in=(clock$0rst false f.tag 2 op.tag 0 op.payload 0)"] ==
  "input f.tag exceeds its width"

/-!
Family entries (sections 7.5 and 11.2). The layout sorts by the name, then by the key as a
number, so `req[2]` comes before `req[10]`. The scalar port `r` sorts before the family `req`
by its name. An entry has the core name `req$10f` and the entry `req[10]`, and its leaves have
the entries `p[1].a` and `p[1].b`. An empty entry has no entry.
-/
def families : String :=
  "struct P {\n  a: UInt[4],\n  b: Bool,\n}\n" ++
  "module F() {\n  comptime for i in 0..3 {\n    input req[10 - 4 * i]: UInt[4];\n  }\n" ++
  "  input r: Bool;\n  input p[1]: P;\n  input e[0]: ();\n" ++
  "  output g[10]: UInt[4];\n  output g[2]: UInt[4];\n" ++
  "  g[10] := req[10] +% p[1].a;\n  g[2] := if (r && p[1].b) { req[6] } else { req[2] };\n}\n"

#guard names families "F" ==
  ([("clock$0rst", "clock$0rst"), ("p[1].a", "p$1f$a"), ("p[1].b", "p$1f$b"), ("r", "r"),
    ("req[2]", "req$2f"), ("req[6]", "req$6f"), ("req[10]", "req$10f")],
   [("g[2]", "g$2f"), ("g[10]", "g$10f")])
#guard run families "F" [
    "in=(clock$0rst false p[1].a 4 p[1].b true r true req[2] 1 req[6] 2 req[10] 3)",
    "in=(clock$0rst false p[1].a 15 p[1].b true r false req[2] 1 req[6] 2 req[10] 3)"] == text [
  "out=(g[2] 2 g[10] 7)",
  "out=(g[2] 1 g[10] 2)"]

/-!
Public names (sections 5.6 and 11.2). A vector names a port with an `as` key by its public name,
also a port of a helper and an entry of a `PortKey`. The layout sorts by the public name, so
`_z` comes before `b0`, and `w$0k` is the core name of the public name `w`.
-/
def keyed : String :=
  "module K() {\n  input x: UInt[4] as \"b0\";\n  input y: UInt[4] as \"_z\";\n" ++
  "  output o: UInt[4] as PortKey(\"g\", true, 7);\n  o := x +% y +% lane(1);\n}\n" ++
  "fn lane(comptime i: Nat) -> UInt[4] {\n  input l: UInt[4] as \"assign\";\n  return l;\n}\n"

#guard names keyed "K" ==
  ([("clock$0rst", "clock$0rst"), ("_z", "_z"), ("assign", "assign$0k"), ("b0", "b0")],
   [("g[7]", "g$7f")])
#guard run keyed "K" ["in=(clock$0rst false _z 1 assign 2 b0 3)"] == "out=(g[7] 6)\n"

/-!
Each field name of a generated record type is a user field of a leaf name, as in a declared
struct (section 7.2). Thus the field `a` of the port `p` is the core port `p$a`.
The source vectors name it `p.a`. A field name that is a core keyword gets no `0k`, because the
leaf name has two fields. A nested generated record adds one user field for each level.
-/
def genLeaves (fs : List (String × Ty)) : List (String × String) :=
  let (s, t) := ({} : Eval.Specs).generate fs {}
  let q : Elab.PortDecl := ⟨"p", 0, none, true, t, ⟨1, 1⟩⟩
  (Id.run (Layout.foldPort (Elab.fieldsOf s (Elab.leafFields s)) q #[]
    (fun es l => pure (es.push (l.entry, Names.encode l.name))) fun es _ => pure es)).toList
#guard genLeaves [("a", .uint 8), ("b", .bool)] == [("p.a", "p$a"), ("p.b", "p$b")]
#guard genLeaves [("mux", .bool)] == [("p.mux", "p$mux")]
#guard genLeaves [("a", .array .bool 2)] == [("p.a.0", "p$a$0e"), ("p.a.1", "p$a$1e")]
#guard genLeaves [] == []
def nestedLeaves : List (String × String) :=
  let (s, inner) := ({} : Eval.Specs).generate [("c", .bool)] {}
  let (s, t) := s.generate [("a", inner)] {}
  let q : Elab.PortDecl := ⟨"p", 0, none, false, t, ⟨1, 1⟩⟩
  (Id.run (Layout.foldPort (Elab.fieldsOf s (Elab.leafFields s)) q #[]
    (fun es l => pure (es.push (l.entry, Names.encode l.name))) fun es _ => pure es)).toList
#guard nestedLeaves == [("p.a.c", "p$a$c")]

end Silicon.Source.Test.Vectors
