-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Vectors
import Silicon.Core.Text
import Silicon.Core.Canonical.WellFormed
import Silicon.Core.Interp.Named
import Silicon.Core.Lower
import Silicon.Core.Mlir.Print

/-!
The core IR commands of `silicon-check`. They check source positions before execution or
lowering. `Silicon.Main` dispatches the command line to them.
-/
namespace Silicon.Core.Cli

open Semantics NamedRun

private def designError (e : Error) : IO UInt32 := do
  (← IO.getStdout).putStrLn (errorLine e)
  return 1

def usageError (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn message
  return 2

/-!
Runs `d` on the input lines of stdin. `parse` reads the values of one line, and `print` gives the
output line of the output values.
-/
def runWith (parse : Typed.Module → String → Except String (List (String × Nat)))
    (print : List (String × Nat) → String) (d : CertifiedDesign) : IO UInt32 := do
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
      match parse m.val line with
      | .error message => return ← usageError message
      | .ok values =>
        let result := Interp.step d env m.val m.property state (inputValues m.val values)
        stdout.putStr (print (outputValues m.val result.2))
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

inductive Command where
  | check | run | lower | models

def execute (command : Command) (file : String) : IO UInt32 := do
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
      | .run =>
        runWith parseInputLine printOutputLine (CertifiedDesign.ofCheck raw typed accepted)
      | .lower | .models =>
        let canonical := canonicalTyped raw typed accepted
        let mlir := match command with
          | .models => ⟨(memoryConfigs canonical).map (Mlir.Item.module ∘ memModel)⟩
          | _ => lower canonical
        (← IO.getStdout).putStr (Mlir.print mlir)
        return 0

end Silicon.Core.Cli
