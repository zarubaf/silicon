import Silicon.Core.Interp.Programs

/-! Compiled children expose paired cycles and retain their semantic state types. -/
namespace Silicon.Core.Interp

open Semantics

def orderedChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) : Children m :=
  programModels m (compileChildren d env m hm)

def orderedRunners (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    Runners m (orderedChildren d env m hm) :=
  programRunners m (compileChildren d env m hm)

theorem orderedChildren_eq (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    orderedChildren d env m hm = designChildren d env m hm :=
  compileChildren_models d env m hm

def cachedSolution (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : Valuation m.ctx :=
  let cache := cycleCache d m hm children runners state input
  curryValues (fun ref => cache.1.getD ref 0)

theorem cachedSolution_eq (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : cachedSolution d m hm children runners state input =
      localSolution d m hm children state input := by
  dsimp only [cachedSolution]
  rw [cycleCache_values]
  exact orderedSolution_eq d m hm children state input

end Silicon.Core.Interp
