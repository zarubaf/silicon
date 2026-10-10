import Silicon.Core.Vectors
import Silicon.Core.Text
import Silicon.Core.Canonical.WellFormed
import Silicon.Core.Interp.Named
import Silicon.Core.Lower
import Silicon.Core.Mlir.Print
import Silicon.Source.Cli

/-! The command line checks source positions before execution or lowering. -/
namespace Silicon.Core.Cli

open Semantics NamedRun

private def designError (e : Error) : IO UInt32 := do
  (← IO.getStdout).putStrLn (errorLine e)
  return 1

private def usageError (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn message
  return 2

private def run (d : CertifiedDesign) : IO UInt32 := do
  if noExterns : d.design.externs = [] then
    let env := emptyEnv d noExterns
    let m := top d noExterns
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    let mut state := Interp.zeroState d env noExterns m.val m.property
    repeat
      let line ← stdin.getLine
      if line.isEmpty then return 0
      let line := if line.endsWith "\n" then (line.dropEnd 1).toString else line
      match parseInputLine m.val line with
      | .error message => return ← usageError message
      | .ok values =>
        let result := Interp.step d env m.val m.property state (inputValues m.val values)
        stdout.putStr (printOutputLine (outputValues m.val result.2))
        stdout.flush
        state := result.1
    return 0
  else
    match lowest : Check.lowest (d.design.externs.map fun e =>
        ⟨.E014, e.pos, "no environment for extern"⟩) with
    | some e => designError e
    | none => False.elim (by
        cases h : d.design.externs with
        | nil => exact noExterns h
        | cons e es => simp [h, Check.lowest] at lowest)

private def canonicalTyped (d : Design) (t : Typed.Design) (h : check d = .ok t) :
    Typed.Design :=
  match hc : check (canonicalize d) with
  | .ok result => result
  | .error _ => False.elim (by
      obtain ⟨result, accepted⟩ := canonicalize_check d t h
      rw [hc] at accepted
      contradiction)

private inductive Command where
  | check | run | lower | models

private def execute (command : Command) (file : String) : IO UInt32 := do
  let source ← IO.FS.readFile file
  match parse source with
  | .error e => designError e
  | .ok raw =>
    match accepted : check raw with
    | .error e => designError e
    | .ok typed =>
      match command with
      | .check =>
        (← IO.getStdout).putStrLn "ok"
        return 0
      | .run => run (CertifiedDesign.ofCheck raw typed accepted)
      | .lower | .models =>
        let canonical := canonicalTyped raw typed accepted
        let mlir := match command with
          | .models => ⟨(memoryConfigs canonical).map (Mlir.Item.module ∘ memModel)⟩
          | _ => lower canonical
        (← IO.getStdout).putStr (Mlir.print mlir)
        return 0

def main (args : List String) : IO UInt32 := do
  try
    let code ← match args with
      | ["check", file] => execute .check file
      | ["run", file] => execute .run file
      | ["lower", file] => execute .lower file
      | ["lower", "--models", file] => execute .models file
      | ["parse", file] => Source.Cli.parse file
      | _ => usageError "usage: silicon-check {check|run|lower [--models]|parse} FILE"
    (← IO.getStdout).flush
    return code
  catch e => usageError e.toString

end Silicon.Core.Cli

def main (args : List String) : IO UInt32 := Silicon.Core.Cli.main args
