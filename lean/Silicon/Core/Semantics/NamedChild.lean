import Silicon.Core.Semantics.NamedLocal

/-! Child component transport preserves the child's step and its port values. -/
namespace Silicon.Core.Semantics

private theorem Component.out_heq_of_eq {ports : List Port} {deps : Deps}
    (a b : Component ports deps) (models : a = b) (state : a.State) (state' : b.State)
    (states : HEq state state') (input : PortValues ports .input) :
    HEq (a.out state input) (b.out state' input) := by
  cases models
  cases states
  rfl

private theorem Component.next_heq_of_eq {ports : List Port} {deps : Deps}
    (a b : Component ports deps) (models : a = b) (state : a.State) (state' : b.State)
    (states : HEq state state') (input : PortValues ports .input) :
    HEq (a.next state input) (b.next state' input) := by
  cases models
  cases states
  rfl

theorem child_ports (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (c : Typed.Module) (child : String)
    (found : d.design.bodies.find? (·.name == child) = some c) :
    m.interfaces child = c.ports := by
  have name : c.name = child := by simpa using List.find?_some found
  rw [(d.design.environments m hm).1, ← name]
  exact portsOf_item d.design.erase d.wellFormed.1.1.1 (.module c.erase)
    (d.design.environments c (List.mem_of_find?_eq_some found)).2.2

theorem designChildren_instance_out (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (found : d.design.bodies.find? (·.name == child) = some c)
    (state : State d env m hm) (childState : State d env c (List.mem_of_find?_eq_some found))
    (states : HEq (state ⟨.inst i p name child inputs, member⟩) childState)
    (input : PortValues (m.interfaces child) .input) (childInput : Input c)
    (sameInput : HEq input childInput) :
    HEq ((designChildren d env m hm ⟨.inst i p name child inputs, member⟩).out
      (state ⟨.inst i p name child inputs, member⟩) input)
      (Interp.step d env c (List.mem_of_find?_eq_some found) childState childInput).2 := by
  let eq := designChildren_inst_module d env m hm i p name child inputs member c found
  let model := localComponent d c (List.mem_of_find?_eq_some found)
    (designChildren d env c (List.mem_of_find?_eq_some found))
  let transported := moduleChild d.design d.wellFormed m c hm
    (List.mem_of_find?_eq_some found) child (by simpa using List.find?_some found) model
  let intermediate : transported.State := cast (congrArg Component.State eq)
    (state ⟨.inst i p name child inputs, member⟩)
  have middle : HEq intermediate childState := (cast_heq _ _).trans states
  exact (Component.out_heq_of_eq _ _ eq _ intermediate (cast_heq _ _).symm input).trans
    (moduleChild_out d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found) child
      (by simpa using List.find?_some found) model intermediate childState input childInput
      middle sameInput)

theorem designChildren_instance_next (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (found : d.design.bodies.find? (·.name == child) = some c)
    (state : State d env m hm) (childState : State d env c (List.mem_of_find?_eq_some found))
    (states : HEq (state ⟨.inst i p name child inputs, member⟩) childState)
    (input : PortValues (m.interfaces child) .input) (childInput : Input c)
    (sameInput : HEq input childInput) :
    HEq ((designChildren d env m hm ⟨.inst i p name child inputs, member⟩).next
      (state ⟨.inst i p name child inputs, member⟩) input)
      (Interp.step d env c (List.mem_of_find?_eq_some found) childState childInput).1 := by
  let eq := designChildren_inst_module d env m hm i p name child inputs member c found
  let model := localComponent d c (List.mem_of_find?_eq_some found)
    (designChildren d env c (List.mem_of_find?_eq_some found))
  let transported := moduleChild d.design d.wellFormed m c hm
    (List.mem_of_find?_eq_some found) child (by simpa using List.find?_some found) model
  let intermediate : transported.State := cast (congrArg Component.State eq)
    (state ⟨.inst i p name child inputs, member⟩)
  have middle : HEq intermediate childState := (cast_heq _ _).trans states
  exact (Component.next_heq_of_eq _ _ eq _ intermediate (cast_heq _ _).symm input).trans
    (moduleChild_next d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found) child
      (by simpa using List.find?_some found) model intermediate childState input childInput
      middle sameInput)

end Silicon.Core.Semantics
