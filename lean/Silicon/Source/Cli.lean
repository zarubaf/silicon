-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Parse
import Silicon.Source.Check
import Silicon.Source.Vectors
import Silicon.Core.Main

/-! The `silicon-check` commands of the front end. The output follows the core IR spec. -/
namespace Silicon.Source.Cli

def errorLine (e : Error) : String :=
  s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}"

def usage : String :=
  "usage: silicon-check {parse FILE|eval FILE EXPR|cost FILE --top T|elab FILE --top T|" ++
  "observe FILE --top T|run FILE --top T|validate FILE --top T OUT} [--fuel N] [--depth N] " ++
  "[--syntax-depth N]"

/-! The positional arguments and the flags of a command. -/
structure Opts where
  args : List String := []
  syntaxDepth : Nat := Lex.defaultSyntaxDepth
  budget : Eval.Budget := {}
  top : Option String := none

/-!
The arguments and the flags, in any order. `--syntax-depth N` takes a number from 1 to
`Lex.maxSyntaxDepth`. `--fuel N` and `--depth N` take a number. Another flag gives `none`.
-/
def opts : List String → Opts → Option Opts
  | [], o => some { o with args := o.args.reverse }
  | "--syntax-depth" :: n :: rest, o => do
    let d ← n.toNat?
    if 0 < d && d ≤ Lex.maxSyntaxDepth then opts rest { o with syntaxDepth := d } else none
  | "--fuel" :: n :: rest, o => do opts rest { o with budget.fuel := ← n.toNat? }
  | "--depth" :: n :: rest, o => do opts rest { o with budget.depth := ← n.toNat? }
  | "--top" :: t :: rest, o => opts rest { o with top := some t }
  | a :: rest, o => if a.startsWith "--" then none else opts rest { o with args := a :: o.args }

/-!
The result of a command: its output, the first error, a rejection of `validate`, a usage error,
or a defect of the reference elaborator. A rejection is a core error or a mismatch line.
-/
inductive Outcome where
  | ok (text : String)
  | error (e : Error)
  | reject (line : String)
  | usage (msg : String)
  | defect (msg : String)

/-! The parsed items and the checked items of a source text. -/
def load (depth : Nat) (source : String) : Except Error (List Item × Array Resolve.Item) := do
  let items ← Parse.parseSource depth source
  return (items, ← Check.check (← Resolve.resolve items))

/-! `eval`: the value of `expr` in the file scope of `source`, and the used fuel. -/
def evalText (o : Opts) (source expr : String) : Except Error (Value × Nat) := do
  let (items, checked) ← load o.syntaxDepth source
  let e ← Resolve.resolveExpr items (← Parse.parseExpr o.syntaxDepth expr)
  Check.checkExpr checked e
  Eval.evalExpr o.budget checked e

/-! A literal argument of a top selection: a number, a negative number, a Boolean, or a string. -/
def literal : Source.Expr → Option Resolve.Expr
  | .num p v => some (.num p v)
  | .bool p v => some (.bool p v)
  | .str p v => some (.str p v)
  | .unary p .neg (.num q v) => some (.unary p .neg (.num q v))
  | _ => none

/-!
The top selection `t`: a module name, then literal arguments in parentheses. The result is the
position of the selection, the module item, its parameters, and the arguments. Else a usage
error.
-/
def topSelection (depth : Nat) (items : List Item) (checked : Array Resolve.Item) (t : String) :
    Except String (Pos × Nat × List Resolve.Param × List Resolve.Expr) := do
  let bad := s!"the top selection `{t}` is not a module name with literal arguments"
  let (p, m, xs) ← match Parse.parseExpr depth t with
    | .ok (.call p (.name _ m) xs) => pure (p, m, xs)
    | .ok (.name p m) => pure (p, m, [])
    | _ => throw bad
  let some xs := xs.mapM literal | throw bad
  let isTop : Item → Bool
    | .module _ n .. => n.name == m
    | _ => false
  match items.findIdx? isTop with
  | some i =>
    match checked[i]? with
    | some (.module _ _ ps _ _) => return (p, i, ps, xs)
    | _ => throw s!"`{m}` is not a module of the file"
  | none => throw s!"`{m}` is not a module of the file"

/-!
The elaboration of the top selection `t` and its lowering with `Source.Flatten`. The result
is the design, the lowered design, and the used fuel, or the outcome of the first failure. The
records of the elaboration come with both outcomes. Only the elaboration makes records
(section 8). The core check of pass 6 is not part of it, because it charges no fuel.
-/
def observeRun (o : Opts) (source t : String) (digest : String → String) :
    Array Eval.Record × Except Outcome (Elab.Design × Flatten.Lowered × Nat) :=
  match load o.syntaxDepth source with
  | .error e => (#[], .error (.error e))
  | .ok (items, checked) =>
    match topSelection o.syntaxDepth items checked t with
    | .error msg => (#[], .error (.usage msg))
    | .ok (p, i, ps, xs) =>
      if ps.length != xs.length then
        let msg := s!"the top takes {ps.length} argument(s), but it has {xs.length}"
        (#[], .error (.error ⟨.S007, p, msg⟩))
      else
        let r := Elab.observe o.budget checked digest p i xs
        (r.1, match r.2 with
          | .error e => .error (.error e)
          | .ok (d, used) =>
            match Flatten.flatten (o.budget.fuel - used) p d with
            | .ok (l, lowered) => .ok (d, l, used + lowered)
            | .error (.source e) => .error (.error e)
            | .error (.defect msg) => .error (.defect msg))

/-! The elaboration of the top selection `t` and its lowering, without the records. -/
def elabRun (o : Opts) (source t : String) (digest : String → String) :
    Except Outcome (Elab.Design × Flatten.Lowered × Nat) :=
  (observeRun o source t digest).2

/-!
`cost`: the fuel that the elaboration of the top selection uses, with the lowering, and the
units of each instantiation. It does not run the core check, so an `S020` design has a cost.
-/
def costText (o : Opts) (source t : String) (digest : String → String := Names.sha16) :
    Outcome :=
  match elabRun o source t digest with
  | .ok (d, l, used) =>
    let insts := d.insts.zipWith (fun i u => { i with units := u }) l.units
    .ok (Elab.costLines { d with insts } used)
  | .error out => out

/-! An elaborated design that passed the check of pass 6, with its typed design. -/
structure Checked where
  elaborated : Elab.Design
  design : Core.Design
  typed : Core.Typed.Design
  accepted : Core.check design = .ok typed

/-! The check of pass 6 on the lowered design of an elaboration, or the outcome of its failure. -/
def checkLowered : Except Outcome (Elab.Design × Flatten.Lowered × Nat) → Except Outcome Checked
  | .ok (d, l, _) =>
    match Flatten.checkDesign l.design with
    | .ok ⟨typed, h⟩ => .ok ⟨d, l.design, typed, h⟩
    | .error (.source e) => .error (.error e)
    | .error (.defect msg) => .error (.defect msg)
  | .error out => .error out

/-! The elaboration of the top selection `t`, its lowering, and the check of pass 6. -/
def elabChecked (o : Opts) (source t : String) (digest : String → String) :
    Except Outcome Checked :=
  checkLowered (elabRun o source t digest)

/-!
`observe` (section 8): the record lines, then the outcome after them. It runs the stages of
`elab`: the elaboration, the lowering, and the check of pass 6. Only the elaboration makes
records, so a rejection at any stage keeps the records before its error. A success has no
other output.
-/
def observeText (o : Opts) (source t : String) (digest : String → String := Names.sha16) :
    String × Outcome :=
  let (rs, r) := observeRun o source t digest
  let text := rs.foldl (fun s line => s ++ line ++ "\n") ""
  match checkLowered r with
  | .ok _ => (text, .ok "")
  | .error out => (text, out)

/-! The canonical text of a design. -/
def canonicalText (d : Core.Design) : String := Core.print (Core.canonicalize d)

/-! `elab`: the canonical text of the lowered design. -/
def elabText (o : Opts) (source t : String) (digest : String → String := Names.sha16) :
    Outcome :=
  match elabChecked o source t digest with
  | .ok c => .ok (canonicalText c.design)
  | .error out => out

/-!
The first line that differs between the reference lines and the output lines, from the line
number `n`. A missing line shows as `<end>`.
-/
def mismatch : List String → List String → Nat → String
  | r :: rs, o :: os, n => if r == o then mismatch rs os (n + 1) else diff n (quote r) (quote o)
  | r :: _, [], n => diff n (quote r) "<end>"
  | [], o :: _, n => diff n "<end>" (quote o)
  | [], [], n => diff n "<end>" "<end>"
where
  quote (line : String) : String := s!"`{line}`"
  diff (n : Nat) (r o : String) : String := s!"mismatch at line {n}: expected {r}, found {o}"

/-!
`validate` (section 8) elaborates the source with the reference elaborator. It parses and checks
the compiler output `out` with the core checker. Then it compares the canonical texts.
-/
def validateText (o : Opts) (source t out : String) (digest : String → String := Names.sha16) :
    Outcome :=
  match elabChecked o source t digest with
  | .error r => r
  | .ok c =>
    match Core.parse out with
    | .error e => .reject (Core.errorLine e)
    | .ok raw =>
      match Core.check raw with
      | .error e => .reject (Core.errorLine e)
      | .ok _ =>
        let ref := canonicalText c.design
        let got := canonicalText raw
        if ref == got then .ok "ok\n"
        else .reject (mismatch (ref.splitOn "\n") (got.splitOn "\n") 1)

/-!
The setup of `run`: the port schema of the top and the checked design. A schema that does not
fit the lowered design is a defect.
-/
def runSetup (o : Opts) (source t : String) (digest : String → String := Names.sha16) :
    Except Outcome (Vectors.Schema × Core.Semantics.CertifiedDesign) := do
  let c ← elabChecked o source t digest
  let some s := Vectors.schema c.elaborated | throw (.defect "the top is not a done instantiation")
  unless Vectors.fits s c.design do throw (.defect "the port schema does not fit the top")
  return (s, Core.Semantics.CertifiedDesign.ofCheck c.design c.typed c.accepted)

/-!
The outcome of `eval`. The result charges the length in bytes of its serialization against the
fuel that remains. When the fuel cannot pay it, the result is `S015` at `1:1` (section 8). Only
the charge is normative, so the reference makes the text first.
-/
def evalOutcome (o : Opts) (source expr : String) : Outcome :=
  match evalText o source expr with
  | .ok (v, used) =>
    let text := v.serialize
    let left := o.budget.fuel - used
    if left < text.utf8ByteSize then
      .error ⟨.S015, ⟨1, 1⟩,
        s!"the fuel cannot pay {text.utf8ByteSize} unit(s) of the result; {left} remain"⟩
    else .ok (text ++ "\n")
  | .error e => .error e

/-! The parse result of `parse`: the AST dump. -/
def parseOutcome (o : Opts) (source : String) : Outcome :=
  match Parse.parseSource o.syntaxDepth source with
  | .ok items => .ok (Print.dump items)
  | .error e => .error e

/-!
The exit code of an outcome (section 8). A result gives 0, and a design error gives 1. A usage
error gives 2, and a defect of the reference elaborator gives 3.
-/
def exitCode : Outcome → UInt32
  | .ok _ => 0
  | .error _ | .reject _ => 1
  | .usage _ => 2
  | .defect _ => 3

/-! Prints an outcome. The result is the exit code, or the message of a usage error. -/
def emit (out : Outcome) : IO (Except String UInt32) := do
  match out with
  | .ok text => (← IO.getStdout).putStr text
  | .error e => (← IO.getStdout).putStrLn (errorLine e)
  | .reject line => (← IO.getStdout).putStrLn line
  | .usage msg => return .error msg
  | .defect msg => (← IO.getStderr).putStrLn s!"defect of the reference elaborator: {msg}"
  return .ok (exitCode out)

/-! Runs the front-end command `cmd`. The result is the exit code, or a usage error. -/
def execute (cmd : String) (rest : List String) : IO (Except String UInt32) := do
  let some o := opts rest {} | return .error usage
  match cmd, o.args, o.top with
  | "parse", [file], none => emit (parseOutcome o (← IO.FS.readFile file))
  | "eval", [file, expr], none => emit (evalOutcome o (← IO.FS.readFile file) expr)
  | "cost", [file], some t => emit (costText o (← IO.FS.readFile file) t)
  | "elab", [file], some t => emit (elabText o (← IO.FS.readFile file) t)
  | "observe", [file], some t =>
    let (text, out) := observeText o (← IO.FS.readFile file) t
    (← IO.getStdout).putStr text
    emit out
  | "validate", [file, out], some t =>
    emit (validateText o (← IO.FS.readFile file) t (← IO.FS.readFile out))
  | "run", [file], some t =>
    match runSetup o (← IO.FS.readFile file) t with
    | .ok (s, d) =>
      return .ok (← Core.Cli.runWith (fun _ => Vectors.parseLine s) (Vectors.printLine s) d)
    | .error out => emit out
  | _, _, _ => return .error usage

end Silicon.Source.Cli
