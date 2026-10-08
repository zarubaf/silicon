import Silicon.Core.Semantics.Component
import Silicon.Core.Semantics.Hierarchy

/-!
A cycle uses the unique equation solution for the selected module in its design.
Each child component comes from its module equations or the supplied extern environment.
-/
namespace Silicon.Core.Semantics

def designChildren (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) : Children m :=
  assembleChildren d.design d.wellFormed env
    (fun module member children => localComponent d module member children) m hm

theorem designChildren_inst_module (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body)
    (c : Typed.Module) (found : d.design.bodies.find? (·.name == child) = some c) :
    designChildren d env m hm ⟨.inst index pos inst child inputs, member⟩ =
      moduleChild d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found) child
        (by simpa using List.find?_some found)
        (localComponent d c (List.mem_of_find?_eq_some found)
          (designChildren d env c (List.mem_of_find?_eq_some found))) :=
  assembleChildren_inst_module d.design d.wellFormed env _ m hm
    index pos inst child inputs member c found

theorem designChildren_inst_extern (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body)
    (absent : d.design.bodies.find? (·.name == child) = none)
    (e : Extern) (found : d.design.externs.find? (·.name == child) = some e)
    (he : Item.extern e ∈ d.design.erase.items) :
    designChildren d env m hm ⟨.inst index pos inst child inputs, member⟩ =
      externChild d.design d.wellFormed m hm e he child (by simpa using List.find?_some found)
        (env e (List.mem_of_find?_eq_some found)) :=
  assembleChildren_inst_extern d.design d.wellFormed env _ m hm
    index pos inst child inputs member absent e found he

abbrev State (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :=
  LocalState m (designChildren d env m hm)

@[simp] theorem State_inst_module (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body)
    (c : Typed.Module) (found : d.design.bodies.find? (·.name == child) = some c) :
    CellState m (.inst index pos inst child inputs)
      (designChildren d env m hm ⟨.inst index pos inst child inputs, member⟩) =
        State d env c (List.mem_of_find?_eq_some found) := by
  rw [designChildren_inst_module d env m hm index pos inst child inputs member c found]
  exact moduleChild_state _ _ _ _ _ _ _ _ _

@[simp] theorem State_inst_extern (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body)
    (absent : d.design.bodies.find? (·.name == child) = none)
    (e : Extern) (found : d.design.externs.find? (·.name == child) = some e)
    (he : Item.extern e ∈ d.design.erase.items) :
    CellState m (.inst index pos inst child inputs)
      (designChildren d env m hm ⟨.inst index pos inst child inputs, member⟩) =
        (env e (List.mem_of_find?_eq_some found)).State := by
  rw [designChildren_inst_extern d env m hm index pos inst child inputs member absent e found he]
  exact externChild_state _ _ _ _ _ _ _ _ _

def solution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : Valuation m.ctx :=
  localSolution d m hm (designChildren d env m hm) state input

def IsSolution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : Valuation m.ctx) : Prop :=
  IsLocalSolution d m hm (designChildren d env m hm) state input values

/-! Outputs and updates share one valuation of the current cycle. -/
def localStepWithValues (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (values : Valuation m.ctx) : LocalState m children × Output m :=
  let memories := stateMemories m children state
  (nextLocalState m children state values memories (connectionValues d m hm values memories),
    outputValues d m hm values)

def stepWithValues (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (values : Valuation m.ctx) : State d env m hm × Output m :=
  localStepWithValues d m hm (designChildren d env m hm) state values

def step (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) : State d env m hm × Output m :=
  stepWithValues d env m hm state (solution d env m hm state input)

theorem solution_unique (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) :
    ∃ values, IsSolution d env m hm state input values ∧
      ∀ other, IsSolution d env m hm state input other → other = values :=
  local_solution_unique d m hm (designChildren d env m hm) state input

/-! The design dependency table bounds which current inputs can affect each output. -/
theorem deps_sound (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (a b : Input m) (output : PortRef m.ports .output)
    (agree : ∀ input : PortRef m.ports .input,
      input.val.name ∈ (((Typed.designDeps d.design.erase (d.design.erase.items.length + 1)
        m.name).getD []).lookup output.val.name).getD [] →
        a input = b input) :
    (step d env m hm state a).2 output = (step d env m hm state b).2 output := by
  apply (localComponent d m hm (designChildren d env m hm)).out_respects state a b output
  rw [d.design.dependencies d.wellFormed m hm] at agree
  exact agree

end Silicon.Core.Semantics
