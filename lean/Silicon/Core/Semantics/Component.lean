import Silicon.Core.Semantics.Output
import Silicon.Core.Semantics.Noninterference

/-!
A module solves its equations before it updates state.
Its output contract follows from the inferred dependency graph.
-/
namespace Silicon.Core.Semantics

noncomputable def localComponent (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) :
    Component m.ports (Deps.infer m.erase m.children) where
  State := LocalState m children
  out := fun state input => outputValues d m hm (localSolution d m hm children state input)
  next := fun state input =>
    let values := localSolution d m hm children state input
    let memories := stateMemories m children state
    nextLocalState m children state values memories (connectionValues d m hm values memories)
  out_respects := by
    intro state a b output agree
    rcases output with ⟨⟨pos, dir, name, ty⟩, member, direction⟩
    cases ty with
    | clock => rfl
    | bits width =>
      exact local_deps_sound d m hm children state a b
        ⟨⟨pos, dir, name, .bits width⟩, member, direction⟩ width
        (port_found d.design d.wellFormed m hm _ member rfl) agree

end Silicon.Core.Semantics
