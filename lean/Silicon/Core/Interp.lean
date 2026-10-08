import Silicon.Core.Semantics.Step
import Silicon.Core.Interp.Hierarchy

/-!
The interpreter uses the checker ranks and the finite driver search.
Outputs and state updates use the same equation solution.
-/
namespace Silicon.Core

open Semantics

namespace Interp

def solve (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : Valuation m.ctx :=
  let children := orderedChildren d env m hm
  let same := orderedChildren_eq d env m hm
  orderedSolution d m hm children (cast (congrArg (LocalState m) same.symm) state) input

theorem solve_eq_solution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : solve d env m hm state input =
      Semantics.solution d env m hm state input := by
  have transport (children : Children m) (same : children = designChildren d env m hm) :
      orderedSolution d m hm children (cast (congrArg (LocalState m) same.symm) state) input =
        Semantics.solution d env m hm state input := by
    cases same
    exact orderedSolution_eq d m hm _ state input
  exact transport _ (orderedChildren_eq d env m hm)

def step (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : State d env m hm × Output m :=
  let children := orderedChildren d env m hm
  let same := orderedChildren_eq d env m hm
  let result := orderedLocalStep d m hm children
    (cast (congrArg (LocalState m) same.symm) state) input
  (cast (congrArg (LocalState m) same) result.1, result.2)

theorem step_eq_values (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : step d env m hm state input =
      stepWithValues d env m hm state (solve d env m hm state input) := by
  rw [solve_eq_solution]
  have transport (children : Children m) (same : children = designChildren d env m hm) :
      let result := orderedLocalStep d m hm children
        (cast (congrArg (LocalState m) same.symm) state) input
      (cast (congrArg (LocalState m) same) result.1, result.2) =
        stepWithValues d env m hm state (Semantics.solution d env m hm state input) := by
    cases same
    dsimp only
    rw [orderedLocalStep_eq]
    rfl
  exact transport _ (orderedChildren_eq d env m hm)

/-! Designs without externs have a recursive all-zero start state. -/
def zeroState (d : CertifiedDesign) (env : Env d.design) (noExterns : d.design.externs = [])
    (m : Typed.Module) (hm : m ∈ d.design.bodies) : State d env m hm :=
  fun ⟨equation, member⟩ => by
    cases equation with
    | reg _ _ _ width _ _ _ _ _ _ => exact BitVec.ofNat width 0
    | mem => exact fun _ => 0
    | let_ | assign => exact ()
    | inst index pos inst child inputs =>
      have stmt := instance_member m index pos inst child inputs member
      have resolved := (d.wellFormed.2.1.2 m.erase (module_mem d.design m hm) _ stmt).1
      have existsItem : ∃ item ∈ d.design.erase.items, Typed.itemName item = child := by
        obtain ⟨item, found, _⟩ := resolved
        exact ⟨item, List.mem_of_find?_eq_some found, by
          simpa [Rules.findItem] using List.find?_some found⟩
      match found : d.design.bodies.find? (·.name == child) with
      | some c =>
        exact cast (State_inst_module d env m hm index pos inst child inputs member c found).symm
          (zeroState d env noExterns c (List.mem_of_find?_eq_some found))
      | none =>
        apply False.elim
        obtain ⟨e, he, _⟩ := external_exists d.design child existsItem found
        simp [noExterns] at he
termination_by moduleLevel d.design.erase d.wellFormed m.name
decreasing_by
  have childMem : child ∈ Typed.childNames m.erase :=
    List.mem_filterMap.mpr ⟨_, stmt, rfl⟩
  have name : c.name = child := by simpa using List.find?_some found
  simpa only [name, Typed.Module.erase] using
    moduleLevel_lower d.design.erase d.wellFormed m.erase (module_mem d.design m hm)
      child childMem

/-! A run records current outputs before it uses the next state. -/
def run (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    State d env m hm → List (Input m) → List (Output m)
  | _, [] => []
  | state, input :: rest =>
    let result := step d env m hm state input
    result.2 :: run d env m hm result.1 rest

end Interp

theorem interp_correct (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : IsSolution d env m hm state input
      (Interp.solve d env m hm state input) := by
  rw [Interp.solve_eq_solution]
  exact localSolution_isSolution d m hm (designChildren d env m hm) state input

theorem interp_step (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : Interp.step d env m hm state input =
      Semantics.step d env m hm state input := by
  rw [Interp.step_eq_values, Interp.solve_eq_solution]
  rfl

end Silicon.Core
