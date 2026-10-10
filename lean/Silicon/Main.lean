import Silicon.Core.Main
import Silicon.Source.Cli

/-!
The root of `silicon-check`. It dispatches each command to the core IR or to the front end,
so the `Core` modules import nothing from `Source`. It imports no proof module.
-/
namespace Silicon

def main (args : List String) : IO UInt32 := do
  try
    let code ← match args with
      | ["check", file] => Core.Cli.execute .check file
      | ["run", file] => Core.Cli.execute .run file
      | ["lower", file] => Core.Cli.execute .lower file
      | ["lower", "--models", file] => Core.Cli.execute .models file
      | ["parse", file] => Source.Cli.parse file
      | _ => Core.Cli.usageError "usage: silicon-check {check|run|lower [--models]|parse} FILE"
    (← IO.getStdout).flush
    return code
  catch e => Core.Cli.usageError e.toString

end Silicon

def main (args : List String) : IO UInt32 := Silicon.main args
