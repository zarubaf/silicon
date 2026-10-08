import Silicon.Core.Semantics.Component
import Silicon.Core.Semantics.Hierarchy

/-!
A cycle uses the unique equation solution for the selected module in its design.
Each child component comes from its module equations or the supplied extern environment.
-/
namespace Silicon.Core.Semantics

noncomputable def designChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) : Children m :=
  assembleChildren d.design d.wellFormed env
    (fun module member children => localComponent d module member children) m hm

abbrev State (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :=
  LocalState m (designChildren d env m hm)

noncomputable def solution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : Valuation m.ctx :=
  localSolution d m hm (designChildren d env m hm) state input

def IsSolution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : Valuation m.ctx) : Prop :=
  IsLocalSolution d m hm (designChildren d env m hm) state input values

/-! Outputs use current state. Every state cell then receives its next value together. -/
noncomputable def step (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : State d env m hm × Output m :=
  let children := designChildren d env m hm
  let values := solution d env m hm state input
  let memories := stateMemories m children state
  (nextLocalState m children state values memories (connectionValues d m hm values memories),
    outputValues d m hm values)

theorem solution_unique (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) :
    ∃ values, IsSolution d env m hm state input values ∧
      ∀ other, IsSolution d env m hm state input other → other = values :=
  local_solution_unique d m hm (designChildren d env m hm) state input

/-! Inferred dependencies bound which current inputs can affect each output. -/
theorem deps_sound (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (a b : Input m) (output : PortRef m.ports .output)
    (agree : ∀ input : PortRef m.ports .input,
      input.val.name ∈ ((Deps.infer m.erase m.children).lookup output.val.name).getD [] →
        a input = b input) :
    (step d env m hm state a).2 output = (step d env m hm state b).2 output :=
  (localComponent d m hm (designChildren d env m hm)).out_respects state a b output agree

end Silicon.Core.Semantics
