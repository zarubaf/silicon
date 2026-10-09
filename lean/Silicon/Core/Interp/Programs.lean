import Silicon.Core.Interp.Finish
import Silicon.Core.Interp.Plans

/-! The hierarchy carries executable cycles beside their semantic components. -/
namespace Silicon.Core.Interp

open Semantics Typed

def ChildProgram (m : Typed.Module) : Typed.Equation m.ctx m.interfaces → Type 1
  | .inst _ _ _ child _ => Program (m.interfaces child) ((m.children child).getD [])
  | _ => PUnit

abbrev Programs (m : Typed.Module) := (e : EquationRef m) → ChildProgram m e.val

def programModels (m : Typed.Module) (programs : Programs m) : Children m
  | ⟨.inst i p n c xs, h⟩ => (programs ⟨.inst i p n c xs, h⟩).model
  | ⟨.let_ .., _⟩ | ⟨.reg .., _⟩ | ⟨.mem .., _⟩ | ⟨.assign .., _⟩ => PUnit.unit

def programRunners (m : Typed.Module) (programs : Programs m) :
    Runners m (programModels m programs)
  | ⟨.inst i p n c xs, h⟩ => (programs ⟨.inst i p n c xs, h⟩).evaluator
  | ⟨.let_ .., _⟩ | ⟨.reg .., _⟩ | ⟨.mem .., _⟩ | ⟨.assign .., _⟩ => PUnit.unit

def localProgram (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (prepared : Prepared d m hm) (programs : Programs m) :
    Program m.ports (Deps.infer m.erase m.children) where
  model := localComponent d m hm (programModels m programs)
  evaluator := localEvaluator d m hm (programModels m programs) (programRunners m programs) prepared

def transportProgram {ports other : List Port} {deps otherDeps : Deps}
    (hp : ports = other) (hd : deps = otherDeps) (program : Program ports deps) :
    Program other otherDeps := hp ▸ hd ▸ program

theorem transportProgram_model {ports other : List Port} {deps otherDeps : Deps}
    (hp : ports = other) (hd : deps = otherDeps) (program : Program ports deps) :
    (transportProgram hp hd program).model = transportComponent hp hd program.model := by
  cases hp
  cases hd
  rfl

def moduleProgram (d : CertifiedDesign) (m c : Typed.Module)
    (hm : m ∈ d.design.bodies) (hc : c ∈ d.design.bodies)
    (child : String) (name : c.name = child)
    (program : Program c.ports (Deps.infer c.erase c.children)) :
    Program (m.interfaces child) ((m.children child).getD []) :=
  transportProgram (by
    rw [(d.design.environments m hm).1, ← name]
    exact (portsOf_item d.design.erase d.wellFormed.1.1.1 (.module c.erase)
      (d.design.environments c hc).2.2).symm) (by
    rw [(d.design.environments m hm).2.1, ← name]
    change Deps.infer c.erase c.children =
      ((designDeps d.design.erase d.design.erase.depsFuel c.name).getD [])
    rw [d.design.dependencies d.wellFormed c hc]
    rfl) program

theorem moduleProgram_model (d : CertifiedDesign) (m c : Typed.Module)
    (hm : m ∈ d.design.bodies) (hc : c ∈ d.design.bodies)
    (child : String) (name : c.name = child)
    (program : Program c.ports (Deps.infer c.erase c.children)) :
    (moduleProgram d m c hm hc child name program).model =
      moduleChild d.design d.wellFormed m c hm hc child name program.model :=
  transportProgram_model _ _ _

def externProgram (model : Component ports deps) : Program ports deps where
  model := model
  evaluator := {
    Cache := fun _ _ => Unit
    empty := fun _ _ => ()
    output := fun state {_target} input port agree cache =>
      ⟨(model.out state input port, cache), model.out_respects state _ _ port agree⟩
    finish := fun state input _ => ⟨(model.next state input, model.out state input), rfl⟩ }

def compileChildrenWith (d : CertifiedDesign) (env : Env d.design)
    (limit : Nat) (plans : ModulePreparations d limit)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (bound : moduleLevel d.design.erase d.wellFormed m.name ≤ limit) : Programs m :=
  fun ⟨equation, member⟩ => by
    cases equation with
    | inst index pos inst child inputs =>
      have stmt := instance_member m index pos inst child inputs member
      have resolved := (d.wellFormed.2.1.2 m.erase (module_mem d.design m hm) _ stmt).1
      have existsItem : ∃ item ∈ d.design.erase.items, Item.name item = child := by
        obtain ⟨item, found, _⟩ := resolved
        exact ⟨item, List.mem_of_find?_eq_some found, by
          simpa [Rules.findItem] using List.find?_some found⟩
      exact match found : d.design.bodies.find? (·.name == child) with
      | some c => by
        have hc := List.mem_of_find?_eq_some found
        have name : c.name = child := by simpa using List.find?_some found
        have lower : moduleLevel d.design.erase d.wellFormed child <
            moduleLevel d.design.erase d.wellFormed m.name := by
          exact moduleLevel_lower d.design.erase d.wellFormed m.erase
            (module_mem d.design m hm) child (List.mem_filterMap.mpr ⟨_, stmt, rfl⟩)
        exact moduleProgram d m c hm hc child name
          (localProgram d c hc
            (modulePrepared d limit plans child c found (Nat.lt_of_lt_of_le lower bound))
            (compileChildrenWith d env limit plans c hc (by rw [name]; omega)))
      | none => by
        have existsExtern := external_exists d.design child existsItem found
        let e := (d.design.externs.find? (·.name == child)).get (by
          obtain ⟨e, he, _⟩ := existsExtern; simp [he])
        have selected : d.design.externs.find? (·.name == child) = some e :=
          (Option.some_get _).symm
        have he : Item.extern e ∈ d.design.erase.items := by
          obtain ⟨other, selectedOther, member⟩ := existsExtern
          rw [selected] at selectedOther
          exact Option.some.inj selectedOther ▸ member
        exact externProgram (externChild d.design d.wellFormed m hm e he child
          (by simpa using List.find?_some selected)
          (env e (List.mem_of_find?_eq_some selected)))
    | _ => exact PUnit.unit
termination_by moduleLevel d.design.erase d.wellFormed m.name
decreasing_by
  have childMem : child ∈ Typed.childNames m.erase :=
    List.mem_filterMap.mpr ⟨_, stmt, rfl⟩
  simpa only [name, Typed.Module.erase] using
    moduleLevel_lower d.design.erase d.wellFormed m.erase (module_mem d.design m hm)
      child childMem

theorem compileChildrenWith_models (d : CertifiedDesign) (env : Env d.design)
    (limit : Nat) (plans : ModulePreparations d limit)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (bound : moduleLevel d.design.erase d.wellFormed m.name ≤ limit) :
    programModels m (compileChildrenWith d env limit plans m hm bound) =
      designChildren d env m hm := by
  funext e
  obtain ⟨equation, member⟩ := e
  cases equation with
  | inst i p n child inputs =>
    dsimp only [programModels]
    rw [compileChildrenWith]
    dsimp only
    split
    next c found =>
      rw [moduleProgram_model, designChildren_inst_module d env m hm i p n child inputs
        member c found]
      change moduleChild _ _ _ _ _ _ _ _
        (localComponent d c _ (programModels c (compileChildrenWith d env limit plans c _ _))) = _
      rw [compileChildrenWith_models d env limit plans c (List.mem_of_find?_eq_some found)]
    next absent =>
      unfold designChildren
      rw [assembleChildren]
      dsimp only
      split
      next c found => rw [absent] at found; contradiction
      next => rfl
  | _ =>
    unfold designChildren
    rw [assembleChildren]
    rfl
termination_by moduleLevel d.design.erase d.wellFormed m.name
decreasing_by
  rename_i c found _ _
  have stmt := instance_member m i p n child inputs member
  have childMem : child ∈ Typed.childNames m.erase :=
    List.mem_filterMap.mpr ⟨_, stmt, rfl⟩
  have name : c.name = child := by simpa using List.find?_some found
  simpa only [name, Typed.Module.erase] using
    moduleLevel_lower d.design.erase d.wellFormed m.erase (module_mem d.design m hm)
      child childMem

def compileChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (plans : ModulePreparations d (moduleLevel d.design.erase d.wellFormed m.name)) : Programs m :=
  compileChildrenWith d env _ plans m hm (Nat.le_refl _)

theorem compileChildren_models (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (plans : ModulePreparations d (moduleLevel d.design.erase d.wellFormed m.name)) :
    programModels m (compileChildren d env m hm plans) = designChildren d env m hm :=
  compileChildrenWith_models d env _ _ m hm _

end Silicon.Core.Interp
