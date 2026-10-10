import Silicon.Source.Parse

/-! The `silicon-check` commands of the front end. The output follows the core IR spec. -/
namespace Silicon.Source.Cli

def errorLine (e : Error) : String :=
  s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}"

/-! `parse F.si`: the AST dump, or the first error with exit code 1. -/
def parse (depth : Nat) (file : String) : IO UInt32 := do
  let source ← IO.FS.readFile file
  let stdout ← IO.getStdout
  match Parse.parseSource depth source with
  | .error e =>
    stdout.putStrLn (errorLine e)
    return 1
  | .ok items =>
    stdout.putStr (Print.dump items)
    return 0

/-!
The file and the syntax depth of the arguments of `parse`. The flag `--syntax-depth N` comes
before or after the file. `N` is a positive number. Other arguments give `none`.
-/
def parseArgs : List String → Option (String × Nat)
  | [file] => some (file, Parse.defaultSyntaxDepth)
  | [file, "--syntax-depth", n] | ["--syntax-depth", n, file] =>
    match n.toNat? with
    | some d => if d > 0 then some (file, d) else none
    | none => none
  | _ => none

end Silicon.Source.Cli
