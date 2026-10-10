import Silicon.Source.Parse
import Silicon.Source.Check
import Silicon.Source.Flatten

/-! The `silicon-check` commands of the front end. The output follows the core IR spec. -/
namespace Silicon.Source.Cli

def errorLine (e : Error) : String :=
  s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}"

def usage : String :=
  "usage: silicon-check {parse FILE|eval FILE EXPR|cost FILE --top T|elab FILE --top T} " ++
  "[--fuel N] [--depth N] [--syntax-depth N]"

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
The result of a command: its output, the first error, a usage error, or a defect of the
reference elaborator.
-/
inductive Outcome where
  | ok (text : String)
  | error (e : Error)
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
is the design, the lowered design, and the used fuel, or the outcome of the first failure.
The core check of pass 6 is not part of it, because it charges no fuel.
-/
def elabRun (o : Opts) (source t : String) (digest : String → String) :
    Except Outcome (Elab.Design × Flatten.Lowered × Nat) :=
  match load o.syntaxDepth source with
  | .error e => .error (.error e)
  | .ok (items, checked) =>
    match topSelection o.syntaxDepth items checked t with
    | .error msg => .error (.usage msg)
    | .ok (p, i, ps, xs) =>
      if ps.length != xs.length then
        let msg := s!"the top takes {ps.length} argument(s), but it has {xs.length}"
        .error (.error ⟨.S007, p, msg⟩)
      else match Elab.elaborate o.budget checked digest p i xs with
        | .error e => .error (.error e)
        | .ok (d, used) =>
          match Flatten.flatten (o.budget.fuel - used) p d with
          | .ok (l, lowered) => .ok (d, l, used + lowered)
          | .error (.source e) => .error (.error e)
          | .error (.defect msg) => .error (.defect msg)

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

/-! `elab`: the canonical text of the lowered design. -/
def elabText (o : Opts) (source t : String) (digest : String → String := Names.sha16) :
    Outcome :=
  match elabRun o source t digest with
  | .ok (_, l, _) =>
    match Flatten.checkDesign l.design with
    | .ok () => .ok (Core.print (Core.canonicalize l.design))
    | .error (.source e) => .error e
    | .error (.defect msg) => .defect msg
  | .error out => out

def evalOutcome (o : Opts) (source expr : String) : Outcome :=
  match evalText o source expr with
  | .ok (v, _) => .ok (v.serialize ++ "\n")
  | .error e => .error e

/-! The parse result of `parse`: the AST dump. -/
def parseOutcome (o : Opts) (source : String) : Outcome :=
  match Parse.parseSource o.syntaxDepth source with
  | .ok items => .ok (Print.dump items)
  | .error e => .error e

/-! Prints an outcome. The result is the exit code, or the message of a usage error. -/
def emit : Outcome → IO (Except String UInt32)
  | .ok text => do (← IO.getStdout).putStr text; return .ok 0
  | .error e => do (← IO.getStdout).putStrLn (errorLine e); return .ok 1
  | .usage msg => return .error msg
  | .defect msg => return .error s!"defect of the reference elaborator: {msg}"

/-! Runs the front-end command `cmd`. The result is the exit code, or a usage error. -/
def execute (cmd : String) (rest : List String) : IO (Except String UInt32) := do
  let some o := opts rest {} | return .error usage
  match cmd, o.args, o.top with
  | "parse", [file], none => emit (parseOutcome o (← IO.FS.readFile file))
  | "eval", [file, expr], none => emit (evalOutcome o (← IO.FS.readFile file) expr)
  | "cost", [file], some t => emit (costText o (← IO.FS.readFile file) t)
  | "elab", [file], some t => emit (elabText o (← IO.FS.readFile file) t)
  | _, _, _ => return .error usage

end Silicon.Source.Cli
