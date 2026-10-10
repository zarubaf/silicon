import Silicon.Source.Parse

/-! The `silicon-check` commands of the front end. The output follows the core IR spec. -/
namespace Silicon.Source.Cli

def errorLine (e : Error) : String :=
  s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}"

/-! `parse F.si`: the AST dump, or the first error with exit code 1. -/
def parse (file : String) : IO UInt32 := do
  let source ← IO.FS.readFile file
  let stdout ← IO.getStdout
  match Parse.parseSource source with
  | .error e =>
    stdout.putStrLn (errorLine e)
    return 1
  | .ok items =>
    stdout.putStr (Print.dump items)
    return 0

end Silicon.Source.Cli
