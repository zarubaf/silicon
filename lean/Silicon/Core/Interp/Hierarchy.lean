import Silicon.Core.Interp.Values
import Silicon.Core.Semantics.Step

/-! Child modules use the stored equation values as well as the top module. -/
namespace Silicon.Core.Interp

open Semantics

/-! The pair keeps the cache outside the state and output functions. -/
def orderedLocalStep (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : LocalState m children × Output m :=
  let system := localSystem d m hm children state input
  let cache := orderedCache system (valueRefs m.ctx)
  localStepWithValues d m hm children state
    (curryValues (fun ref => cache.getD ref (system.initial ref)))

theorem orderedLocalStep_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : orderedLocalStep d m hm children state input =
      localStepWithValues d m hm children state (localSolution d m hm children state input) := by
  change localStepWithValues d m hm children state
    (orderedSolution d m hm children state input) = _
  rw [orderedSolution_eq]

def orderedComponent (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) :
    Component m.ports (Deps.infer m.erase m.children) where
  State := LocalState m children
  out := fun state input => (orderedLocalStep d m hm children state input).2
  next := fun state input => (orderedLocalStep d m hm children state input).1
  out_respects := by
    intro state a b output agree
    simp only [orderedLocalStep_eq]
    exact (localComponent d m hm children).out_respects state a b output agree

theorem orderedComponent_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) :
    orderedComponent d m hm children = localComponent d m hm children := by
  unfold orderedComponent localComponent
  congr 1 <;> funext state input <;> rw [orderedLocalStep_eq] <;> rfl

def orderedChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) : Children m :=
  assembleChildren d.design d.wellFormed env
    (fun module member children => orderedComponent d module member children) m hm

theorem orderedChildren_eq (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    orderedChildren d env m hm = designChildren d env m hm := by
  unfold orderedChildren designChildren
  have builders : (fun module member children => orderedComponent d module member children) =
      (fun module member children => localComponent d module member children) := by
    funext module member children
    exact orderedComponent_eq d module member children
  rw [builders]

end Silicon.Core.Interp
