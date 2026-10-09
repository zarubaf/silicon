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
  let filled := fillCache d m hm children runners state input (allSelection m input)
    (prepare d m hm) (emptyCache d m hm children runners state input)
  curryValues (fun ref => filled.val.values.getD ref 0)

theorem cachedSolution_eq (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : cachedSolution d m hm children runners state input =
      localSolution d m hm children state input := by
  funext node width found
  exact (Std.DHashMap.getD_eq_getD_get?).trans
    (congrArg (fun x => x.getD 0)
      ((fillCache d m hm children runners state input (allSelection m input)
        (prepare d m hm) (emptyCache d m hm children runners state input)).property
          ⟨node, width, found⟩ rfl))

end Silicon.Core.Interp
