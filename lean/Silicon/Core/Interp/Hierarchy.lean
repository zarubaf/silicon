-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Interp.Programs

/-! Compiled children expose paired cycles and retain their semantic state types. -/
namespace Silicon.Core.Interp

open Semantics

def orderedChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (plans : ModulePreparations d (moduleLevel d.design.erase d.wellFormed m.name)) : Children m :=
  programModels m (compileChildren d env m hm plans)

def orderedRunners (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (plans : ModulePreparations d (moduleLevel d.design.erase d.wellFormed m.name)) :
    Runners m (orderedChildren d env m hm plans) :=
  programRunners m (compileChildren d env m hm plans)

theorem orderedChildren_eq (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (plans : ModulePreparations d (moduleLevel d.design.erase d.wellFormed m.name)) :
    orderedChildren d env m hm plans = designChildren d env m hm :=
  compileChildren_models d env m hm plans

def cachedSolution (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : Valuation m.ctx :=
  (completeCache d m hm children runners
    (prepareValues d m hm (Deps.graph m.erase m.children) rfl) state input
    (emptyCache d m hm children runners state input)).val.1

theorem cachedSolution_eq (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : cachedSolution d m hm children runners state input =
      localSolution d m hm children state input :=
  (completeCache d m hm children runners
    (prepareValues d m hm (Deps.graph m.erase m.children) rfl) state input
    (emptyCache d m hm children runners state input)).property

end Silicon.Core.Interp
