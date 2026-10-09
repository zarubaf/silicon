import Silicon.Core.Proof.Lower.HierarchyCorrect

/-!
The reference lowering is correct for the top module of a checked design without externs.
The lowered design uses the model of its configuration for each memory extern.
-/
namespace Silicon.Core.LowerProof

open Semantics

theorem solutionValues_root (d : Mlir.Design) (m : Mlir.Module) (σ : Mlir.ModuleState)
    (vals : Mlir.Env) : Mlir.solutionValues d m σ vals [] = vals := rfl

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

/-- `lower_correct raw t h noExterns env top found` is the correctness of the reference lowering.
Let `d` be the lowered design that uses the model of each memory extern. The top module of
`d` is the lowering of the core top module. Take a core state `s` and an MLIR state `σ` that
correspond, and a core input with matching MLIR inputs. Then (a) an MLIR solution exists.
(b) Every MLIR solution gives the outputs of the core step. (c) The MLIR next state of that
solution corresponds to the core next state. -/
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
          OutputsAgree top (step core env top hm s input).2 vals ∧
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
  · exact correct.2 _ (solution_hierarchy d _ σ inputs vals solved)

end Silicon.Core
