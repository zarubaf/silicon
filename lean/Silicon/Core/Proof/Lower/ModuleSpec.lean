import Silicon.Core.Proof.Lower.SoundStatement
import Silicon.Core.Proof.Lower.LetResults
import Silicon.Core.Proof.Lower.ResultNames
import Silicon.Core.Proof.Lower.SolutionFacts
import Silicon.Core.Proof.Lower.WellFormed
import Silicon.Core.Proof.Lower.Memory
import Silicon.Core.Proof.Lower.Module

/-!
Port agreement relates core port values to MLIR values at the port names.
An output port of the lowered module carries the renamed name of its assignment.
-/
namespace Silicon.Core.LowerProof

open Semantics

def InputsAgree (ports : List Port) (input : PortValues ports .input) (inputs : Mlir.Env) :
    Prop :=
  ∀ p : PortRef ports .input, inputs p.val.name = some (coreValue p.val.ty (input p))

def OutputsAgree (m : Typed.Module) (output : Output m) (vals : Mlir.Env) : Prop :=
  ∀ p : PortRef m.ports .output, vals (rename m p.val.name) = some (coreValue p.val.ty (output p))

abbrev certified (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t) :
    CertifiedDesign :=
  CertifiedDesign.ofCheck raw t h

/-- `ModuleCorrect raw t h noExterns env c hc` is the per-module result. Take a core state
`s` of `c` and an MLIR state `σ` that correspond, and a core input with matching MLIR inputs.
Then the lowered module `(Lower.module c).1` has a hierarchy solution in
`(lower t).withModels (memoryConfigs t)` with the core outputs. Every hierarchy solution has
the core outputs and a next state that corresponds to the core next state. A parent instance
supplies its own connection values as the inputs. So the hierarchy step proves this predicate
by strong induction on the module order and uses it at each child instance. -/
def ModuleCorrect (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (noExterns : t.externs = []) (env : Env (certified raw t h).design) (c : Typed.Module)
    (hc : c ∈ t.bodies) : Prop :=
  ∀ (s : State (certified raw t h) env c hc) (σ : Mlir.ModuleState),
    Corresponds (certified raw t h) env noExterns c hc s σ →
    ∀ (input : Input c) (inputs : Mlir.Env), InputsAgree c.ports input inputs →
      (∃ vals, Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module c).1
        σ inputs vals ∧
        OutputsAgree c (step (certified raw t h) env c hc s input).2 (vals [])) ∧
      ∀ vals, Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t))
        (Lower.module c).1 σ inputs vals →
        OutputsAgree c (step (certified raw t h) env c hc s input).2 (vals []) ∧
        Corresponds (certified raw t h) env noExterns c hc
          (step (certified raw t h) env c hc s input).1
          (Mlir.nextHierarchyState ((lower t).withModels (memoryConfigs t)) (Lower.module c).1
            vals)

end Silicon.Core.LowerProof
