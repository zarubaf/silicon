-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.HierarchyCorrect

/-!
The reference lowering is correct for the top module of a checked design without externs.
The lowered design uses the model of its configuration for each memory extern.
-/
namespace Silicon.Core.LowerProof

open Semantics

theorem solution_hierarchy (d : Mlir.Design) (m : Mlir.Module) (σ : Mlir.ModuleState)
    (inputs vals : Mlir.Env) (h : Mlir.IsSolution d m σ inputs vals) :
    Mlir.IsHierarchySolution d m σ inputs (Mlir.solutionValues d m σ vals) := by
  have self := Mlir.solutionValues_spec h
  obtain ⟨all, root, valid⟩ := h
  refine ⟨localSolution_inputs (fun p hp => ?_) self.1, self.2⟩
  obtain ⟨v, hi, _, hv⟩ := valid.1.1 p hp
  rw [← root, hv, hi]

end Silicon.Core.LowerProof

namespace Silicon.Core

open Semantics LowerProof

/-- The lowered module `(Lower.module m).1` pairs each output operand with an output port.
At the operand for the lowering of each core output port `p`, `vals` holds the output of `p`. -/
def LoweredOutputsAgree (m : Typed.Module) (output : Output m) (vals : Mlir.Env) : Prop :=
  ∀ (p : PortRef m.ports .output) (operand : String),
    (operand, Lower.port p.val) ∈ (Lower.module m).1.outputs.zip (Lower.module m).1.outputPorts →
      vals operand = some (coreValue p.val.ty (output p))

theorem LowerProof.zip_self_mem {α : Type} {a b : α} :
    ∀ {l : List α}, (a, b) ∈ l.zip l → a = b
  | [], member => by cases member
  | x :: xs, member => by
    rcases List.mem_cons.mp member with same | member
    · cases same
      rfl
    · exact zip_self_mem member

theorem LowerProof.lowered_outputs (m : Typed.Module) (output : Output m) (vals : Mlir.Env)
    (agree : OutputsAgree m output vals) : LoweredOutputsAgree m output vals := by
  intro p operand member
  rw [outputs_filter, Mlir.Module.outputPorts, module_ports, ports_output_filter, List.zip_map,
    List.mem_map] at member
  obtain ⟨⟨a, b⟩, pair, same⟩ := member
  cases zip_self_mem pair
  simp only [Prod.map, Prod.mk.injEq] at same
  obtain ⟨rfl, port⟩ := same
  have named : a.name = p.val.name := congrArg Mlir.Port.name port
  rw [named]
  exact agree p

/-- `lower_correct raw t h noExterns env top found` is the correctness of the reference lowering.
Let `d` be the lowered design that uses the model of each memory extern. The top module of
`d` is the lowering of the core top module. Take a core state `s` and an MLIR state `σ` that
correspond, and a core input with matching MLIR inputs. Then (a) an MLIR solution exists.
(b) Every MLIR solution has the core output of each output port at the output operand of that
port. (c) The MLIR next state of that solution corresponds to the core next state. -/
theorem lower_correct (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (noExterns : t.externs = []) (env : Env (CertifiedDesign.ofCheck raw t h).design)
    (top : Typed.Module) (found : t.bodies.find? (·.name == t.top) = some top) :
    let core := CertifiedDesign.ofCheck raw t h
    let hm := List.mem_of_find?_eq_some found
    let d := (lower t).withModels (memoryConfigs t)
    d.findModule t.top = some (Lower.module top).1 ∧
    ∀ (s : State core env top hm) (σ : Mlir.ModuleState),
      Corresponds core env noExterns top hm s σ →
      ∀ (input : Input top) (inputs : Mlir.Env), InputsAgree top.ports input inputs →
        (∃ vals, Mlir.IsSolution d (Lower.module top).1 σ inputs vals) ∧
        ∀ vals, Mlir.IsSolution d (Lower.module top).1 σ inputs vals →
          LoweredOutputsAgree top (step core env top hm s input).2 vals ∧
          Corresponds core env noExterns top hm (step core env top hm s input).1
            (Mlir.nextState d (Lower.module top).1 σ vals) := by
  intro core hm d
  refine ⟨?_, fun s σ corr input inputs agree => ?_⟩
  · have name : (Lower.module top).1.name = t.top := by
      rw [module_name]
      simpa using List.find?_some found
    rw [← name]
    exact findModule_mem _ (design_names raw t h noExterns) _ (body_in_design t noExterns top hm)
  have correct := modules_correct raw t h noExterns env top hm s σ corr input inputs agree
  refine ⟨?_, fun vals solved => ?_⟩
  · obtain ⟨all, valid, _⟩ := correct.1
    exact ⟨all [], all, rfl, valid⟩
  · have every := correct.2 _ (solution_hierarchy d _ σ inputs vals solved)
    exact ⟨lowered_outputs top _ vals every.1, every.2⟩

end Silicon.Core
