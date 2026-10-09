import Silicon.Core.Mlir.Semantics
import Silicon.Core.Mlir.WellFormed
import Silicon.Core.Lower
import Silicon.Core.Check
import Silicon.Core.Text

namespace Silicon.Core.Test.MlirSemantics

open Mlir

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def bits (w n : Nat) : Mlir.Value := .bits w (BitVec.ofNat w n)
private def shiftEnv (amount : Nat) : String → Option Mlir.Value
  | "a" => some (bits 8 128)
  | "b" => some (bits 8 amount)
  | _ => none

#guard (Op.comb .shl "a" "b" 8).eval (shiftEnv 8) = some (bits 8 0)
#guard (Op.comb .shru "a" "b" 8).eval (shiftEnv 8) = some (bits 8 0)
#guard (Op.comb .shrs "a" "b" 8).eval (shiftEnv 8) = some (bits 8 255)
#guard (Op.comb .shl "a" "b" 8).eval (shiftEnv 255) = some (bits 8 0)
#guard (Op.comb .shru "a" "b" 8).eval (shiftEnv 255) = some (bits 8 0)
#guard (Op.comb .shrs "a" "b" 8).eval (shiftEnv 255) = some (bits 8 255)

private def arrayEnv : String → Option Mlir.Value
  | "arr" => some (.array 16 8 fun i => BitVec.ofNat 8 i.val)
  | "idx" => some (bits 4 15)
  | "v" => some (bits 8 42)
  | _ => none

#guard (Op.arrayGet "arr" "idx" 16 8 4).eval arrayEnv = some (bits 8 15)
#guard (do
  let arr ← (Op.arrayInject "arr" "idx" "v" 16 8 4).eval arrayEnv
  (Op.arrayGet "arr" "idx" 16 8 4).eval
    (fun name => if name == "arr" then some arr else arrayEnv name)) = some (bits 8 42)
#guard (do
  let arr ← (Op.arrayInject "arr" "idx" "v" 16 8 4).eval arrayEnv
  (Op.arrayGet "arr" "idx" 16 8 4).eval
    (fun name => if name == "arr" then some arr
      else if name == "idx" then some (bits 4 3) else arrayEnv name)) = some (bits 8 3)

private def counterSource : String := "(design counter (module counter
  (input clk clock) (input rst (bits 1)) (input en (bits 1)) (output q (bits 8))
  (reg r (bits 8) clk (reset sync rst (const 8 0)))
  (let inc (bits 8) (add r (const 8 1)))
  (next r (mux en inc r)) (assign q r)))"

private def counterDesign : Mlir.Design :=
  match parse counterSource >>= check with
  | .ok t => lower t
  | .error _ => ⟨[]⟩

private def counter : Mlir.Module :=
  (counterDesign.findModule "counter").getD ⟨"missing", [], [], []⟩

#guard counter.name == "counter"
#guard counter.outputs == ["silicon_reg_r"]

private def inputs (reset : Nat) : String → Option Mlir.Value
  | "clk" => some .clock
  | "rst" => some (bits 1 reset)
  | "en" => some (bits 1 1)
  | _ => none

private def state : ModuleState := ⟨fun _ name =>
  if name == "silicon_reg_r" then some (bits 8 3) else none⟩

private def values (reset : Nat) : Valuation := fun _ name =>
  match name with
  | "silicon_reg_r" => some (bits 8 3)
  | "silicon_t0" => some (bits 8 0)
  | "silicon_t1" => some (bits 8 1)
  | "inc" | "silicon_t2" => some (bits 8 4)
  | _ => inputs reset name

private def counterBody : Mlir.Module :=
  ⟨"counter", [⟨.input, "clk", .clock⟩, ⟨.input, "rst", .int 1⟩,
    ⟨.input, "en", .int 1⟩, ⟨.output, "q", .int 8⟩],
    [(["silicon_t0"], .constant 8 0), (["silicon_t1"], .constant 8 1),
     (["inc"], .comb .add "silicon_reg_r" "silicon_t1" 8),
     (["silicon_t2"], .mux "en" "inc" "silicon_reg_r" (.int 8)),
     (["silicon_reg_r"], .compreg "silicon_t2" "clk"
       (some ("rst", "silicon_t0")) (.int 8))], ["silicon_reg_r"]⟩

#guard counter = counterBody

private theorem counterSolution (reset : Nat) :
    IsHierarchySolution counterDesign counterBody state (inputs reset) (values reset) := by
  constructor
  · simp [LocalSolution, counterBody, Module.inputPorts, Module.outputPorts,
      inputs, values, state, ModuleState.regs, Op.eval, bits, Env.bits, Env.typed,
      Value.asBits, Value.ty, CombOp.core, Semantics.evalOp, Semantics.evalMux]
  · intro path parent found inst callee args member
    cases path with
    | nil =>
      simp [Module.atPath] at found
      subst parent
      simp [counterBody, Module.findInstance] at member
    | cons name path =>
      simp [Module.atPath, counterBody, Module.findInstance] at found

example : IsSolution counterDesign counterBody state (inputs 0) (values 0 []) := by
  exact ⟨values 0, rfl, counterSolution 0⟩

example : IsSolution counterDesign counterBody state (inputs 1) (values 1 []) := by
  exact ⟨values 1, rfl, counterSolution 1⟩

#guard (nextHierarchyState counterDesign counter state (values 0)).regs "silicon_reg_r" =
  some (bits 8 4)
#guard (nextHierarchyState counterDesign counter state (values 1)).regs "silicon_reg_r" =
  some (bits 8 0)

#guard (values 0 [] "silicon_reg_r") = some (bits 8 3)
example : (nextState counterDesign counterBody state (values 0 [])).regs "silicon_reg_r" =
  some (bits 8 4) := by rfl
example : (nextState counterDesign counterBody state (values 1 [])).regs "silicon_reg_r" =
  some (bits 8 0) := by rfl

#guard (Op.constant 3 8).eval (fun _ => none) = none
#guard (Op.comb .add "a" "b" 4).eval (shiftEnv 1) = none
#guard (Op.extract "a" 7 8 2).eval (shiftEnv 1) = none
#guard (Op.replicate "a" 8 15).eval (shiftEnv 1) = none
#guard (Op.replicate "a" 8 16).eval (shiftEnv 1) = some (bits 16 32896)
#guard (Op.icmp .slt "a" "b" 8).eval (shiftEnv 1) = some (bits 1 1)
#guard (Op.icmp .ult "a" "b" 8).eval (shiftEnv 1) = some (bits 1 0)
#guard (Op.concat "a" "b" 8 8).eval (shiftEnv 1) = some (bits 16 32769)
#guard (Op.extract "a" 7 8 1).eval (shiftEnv 1) = some (bits 1 1)

example : counterBody.WellFormed counterDesign := by
  simp [Module.WellFormed, Module.definitions, counterBody, Module.inputPorts,
    Module.outputPorts, Op.resultTypes, Op.operands, Op.Valid, List.lookup, or_imp,
    forall_and]

private def invalid (body : List (List String × Mlir.Op)) : Mlir.Module :=
  ⟨"invalid", [], body, []⟩

example : ¬ (invalid [(["x"], .constant 1 2)]).WellFormed ⟨[]⟩ := by
  simp [Module.WellFormed, Module.definitions, invalid, Module.inputPorts,
    Op.resultTypes, Op.Valid]

example : ¬ (invalid [(["x"], .constant 1 0), (["x"], .constant 1 1)]).WellFormed ⟨[]⟩ := by
  simp [Module.WellFormed, Module.definitions, invalid, Module.inputPorts, Op.resultTypes]

example : ¬ (invalid [(["x"], .comb .add "missing" "missing" 8)]).WellFormed ⟨[]⟩ := by
  simp [Module.WellFormed, Module.definitions, invalid, Module.inputPorts,
    Op.resultTypes, Op.Valid, Op.operands, List.lookup]

#guard ([1, 12, 16].all fun depth =>
  let c : MemConfig := ⟨depth, 8, 1, 2⟩
  (Mlir.Design.withModels [c] ⟨[.extern c.moduleName c.ports]⟩).items = [.module (memModel c)])
#guard (Mlir.Design.withModels [⟨12, 8, 1, 2⟩] ⟨[.extern "blackbox" []]⟩).items =
  [.extern "blackbox" []]
#guard (Mlir.Design.withModels [⟨12, 8, 1, 2⟩] ⟨[.extern "silicon_mem_12x8_r1w2" []]⟩).items =
  [.extern "silicon_mem_12x8_r1w2" []]

private def child : Mlir.Module :=
  ⟨"child", [⟨.input, "clk", .clock⟩, ⟨.input, "x", .int 8⟩,
    ⟨.output, "q", .int 8⟩],
    [(["r"], .compreg "x" "clk" none (.int 8))], ["r"]⟩

private def siblings : Mlir.Module :=
  ⟨"siblings", [⟨.input, "clk", .clock⟩, ⟨.output, "q", .int 8⟩],
    [(["u.q"], .instance "u" "child"
      [("clk", "clk", .clock), ("x", "v.q", .int 8)] [("q", .int 8)]),
     (["v.q"], .instance "v" "child"
      [("clk", "clk", .clock), ("x", "u.q", .int 8)] [("q", .int 8)])], ["u.q"]⟩

private def hierarchy : Mlir.Design := ⟨[.module child, .module siblings]⟩
private def siblingState : ModuleState := ⟨fun path name =>
  if name == "r" then match path with
    | ["u"] => some (bits 8 3)
    | ["v"] => some (bits 8 7)
    | _ => none
  else none⟩

private def siblingValues : Valuation := fun path name =>
  if name == "clk" then some .clock else
  match path, name with
  | [], "u.q" | ["u"], "r" | ["v"], "x" => some (bits 8 3)
  | [], "v.q" | ["v"], "r" | ["u"], "x" => some (bits 8 7)
  | _, _ => none

#guard ((nextHierarchyState hierarchy siblings siblingState siblingValues).instance "u").regs "r" =
  some (bits 8 7)
#guard ((nextHierarchyState hierarchy siblings siblingState siblingValues).instance "v").regs "r" =
  some (bits 8 3)

example : LocalSolution hierarchy siblings siblingState.regs (inputs 0)
    (siblingValues []) (fun name => siblingValues [name]) := by
  simp [LocalSolution, hierarchy, siblings, child, Design.findModule, Module.inputPorts,
    Module.outputPorts, siblingValues, inputs, instanceInputs, Env.typed, Value.ty, bits]

example : LocalSolution hierarchy child (siblingState.instance "u").regs
    (instanceInputs [("clk", "clk", .clock), ("x", "v.q", .int 8)] (siblingValues []))
    (siblingValues ["u"]) (fun name => siblingValues ["u", name]) := by
  simp [LocalSolution, child, Module.inputPorts, Module.outputPorts, siblingState,
    ModuleState.instance, ModuleState.regs, siblingValues, instanceInputs, Env.typed,
    Value.ty, bits]

example : LocalSolution hierarchy child (siblingState.instance "v").regs
    (instanceInputs [("clk", "clk", .clock), ("x", "u.q", .int 8)] (siblingValues []))
    (siblingValues ["v"]) (fun name => siblingValues ["v", name]) := by
  simp [LocalSolution, child, Module.inputPorts, Module.outputPorts, siblingState,
    ModuleState.instance, ModuleState.regs, siblingValues, instanceInputs, Env.typed,
    Value.ty, bits]

end Silicon.Core.Test.MlirSemantics
