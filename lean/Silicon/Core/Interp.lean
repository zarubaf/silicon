-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Step
import Silicon.Core.Interp.Hierarchy

/-!
The interpreter uses the checker ranks and the finite driver search.
Outputs and state updates use the same equation solution.
-/
namespace Silicon.Core

open Semantics

namespace Interp

/-! One transport connects an interpreter child family to the semantic state type. -/
def withOrderedChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (Result : Children m → Type)
    (evaluate : (children : Children m) → Runners m children →
      LocalState m children → Result children)
    (state : State d env m hm) : Result (designChildren d env m hm) :=
  let plans := prepareModules d (moduleLevel d.design.erase d.wellFormed m.name)
  let children := orderedChildren d env m hm plans
  let same := orderedChildren_eq d env m hm plans
  cast (congrArg Result same)
    (evaluate children (orderedRunners d env m hm plans)
      (cast (congrArg (LocalState m) same.symm) state))

theorem withOrderedChildren_eq (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (Result : Children m → Type)
    (evaluate : (children : Children m) → Runners m children →
      LocalState m children → Result children)
    (state : State d env m hm) :
    withOrderedChildren d env m hm Result evaluate state =
      evaluate (designChildren d env m hm)
        (cast (congrArg (Runners m) (orderedChildren_eq d env m hm
          (prepareModules d (moduleLevel d.design.erase d.wellFormed m.name))))
          (orderedRunners d env m hm
            (prepareModules d (moduleLevel d.design.erase d.wellFormed m.name)))) state := by
  have transport (children : Children m) (same : children = designChildren d env m hm)
      (runners : Runners m children) :
      cast (congrArg Result same)
        (evaluate children runners (cast (congrArg (LocalState m) same.symm) state)) =
          evaluate (designChildren d env m hm) (cast (congrArg (Runners m) same) runners)
            state := by
    cases same
    rfl
  exact transport _ (orderedChildren_eq d env m hm _)
    (orderedRunners d env m hm _)

def solve (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : Valuation m.ctx :=
  withOrderedChildren d env m hm (fun _ => Valuation m.ctx)
    (fun children runners state => cachedSolution d m hm children runners state input) state

theorem solve_eq_solution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : solve d env m hm state input =
      Semantics.solution d env m hm state input := by
  rw [solve, withOrderedChildren_eq, cachedSolution_eq]
  rfl

def step (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : State d env m hm × Output m :=
  withOrderedChildren d env m hm (fun children => LocalState m children × Output m)
    (fun children runners state => cachedLocalStep d m hm children runners state input) state

theorem step_eq_values (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : step d env m hm state input =
      stepWithValues d env m hm state (solve d env m hm state input) := by
  rw [step, withOrderedChildren_eq, cachedLocalStep_eq, solve_eq_solution]
  rfl

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
      have existsItem : ∃ item ∈ d.design.erase.items, Item.name item = child := by
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
def runCycles {σ ι ο : Type} (tick : σ → ι → σ × ο) : σ → List ι → List ο
  | _, [] => []
  | state, input :: rest =>
    let result := tick state input
    result.2 :: runCycles tick result.1 rest

def run (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (inputs : List (Input m)) : List (Output m) :=
  let prepared := prepareValues d m hm (Deps.graph m.erase m.children) rfl
  withOrderedChildren d env m hm (fun _ => List (Output m))
    (fun children runners state =>
      runCycles (fun state input =>
        (finishCache d m hm children runners prepared state input
          (emptyCache d m hm children runners state input)).val) state inputs) state

theorem run_eq_cycles (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (inputs : List (Input m)) :
    run d env m hm state inputs = runCycles (step d env m hm) state inputs := by
  rw [run, withOrderedChildren_eq]
  apply congrArg (fun tick => runCycles tick state inputs)
  funext state input
  rw [(finishCache d m hm _ _ _ state input _).property]
  exact ((step_eq_values d env m hm state input).trans
    (congrArg (stepWithValues d env m hm state) (solve_eq_solution d env m hm state input))).symm

theorem run_nil (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm) :
    run d env m hm state [] = [] := by rw [run_eq_cycles]; rfl

theorem run_cons (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (rest : List (Input m)) :
    run d env m hm state (input :: rest) =
      (step d env m hm state input).2 :: run d env m hm (step d env m hm state input).1 rest := by
  simp only [run_eq_cycles, runCycles]

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
