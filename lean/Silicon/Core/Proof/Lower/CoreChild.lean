import Silicon.Core.Semantics.Step

/-!
A child component of a checked module is the step function of the child module.
Its port values and state cells only change type along the interface equality.
-/
namespace Silicon.Core.LowerProof

open Semantics

def transportInput {a b : List Port} (same : a = b) (input : PortValues a .input) :
    PortValues b .input :=
  fun q => input ⟨q.val, same ▸ q.property.1, q.property.2⟩

theorem transportInput_heq {a b : List Port} (same : a = b) (input : PortValues a .input) :
    HEq input (transportInput same input) := by
  subst same
  rfl

theorem heq_apply {a b : List Port} (same : a = b) {f : PortValues a dir} {g : PortValues b dir}
    (e : HEq f g) (p : Port) (h₁ : p ∈ a) (h₂ : p ∈ b) (hd : p.dir = dir) :
    f ⟨p, h₁, hd⟩ = g ⟨p, h₂, hd⟩ := by
  subst same
  cases e
  rfl

theorem cast_eq_cast {α β : Type} (h₁ h₂ : α = β) (x : α) : cast h₁ x = cast h₂ x := rfl

section
variable (d : CertifiedDesign) (env : Env d.design) (m : Typed.Module) (hm : m ∈ d.design.bodies)
  (i : Nat) (p : Pos) (n child : String)
  (inputs : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
  (member : Typed.Equation.inst i p n child inputs ∈ m.body) (c : Typed.Module)
  (found : d.design.bodies.find? (·.name == child) = some c)

include hm found in
theorem child_ports : m.interfaces child = c.ports := by
  have hc := List.mem_of_find?_eq_some found
  have name : c.name = child := by simpa using List.find?_some found
  rw [(d.design.environments m hm).1, ← name]
  exact portsOf_item d.design.erase d.wellFormed.1.1.1 (.module c.erase)
    (d.design.environments c hc).2.2

private theorem component_out
    (C : Component (m.interfaces child) ((m.children child).getD []))
    (hC : C = moduleChild d.design d.wellFormed m c hm
      (List.mem_of_find?_eq_some found) child (by simpa using List.find?_some found)
      (localComponent d c (List.mem_of_find?_eq_some found)
        (designChildren d env c (List.mem_of_find?_eq_some found))))
    (state : C.State) (state' : State d env c (List.mem_of_find?_eq_some found))
    (hs : HEq state state') (conn : PortValues (m.interfaces child) .input) (port : Port)
    (h₁ : port ∈ m.interfaces child)
    (h₂ : port ∈ c.ports) (dir : port.dir = .output) :
    C.out state conn ⟨port, h₁, dir⟩ =
      (step d env c (List.mem_of_find?_eq_some found) state'
        (transportInput (child_ports d m hm child c found) conn)).2
        ⟨port, h₂, dir⟩ := by
  subst hC
  have out := moduleChild_out d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found)
    child (by simpa using List.find?_some found) _ state state' conn
    (transportInput (child_ports d m hm child c found) conn) hs (transportInput_heq _ conn)
  exact heq_apply (child_ports d m hm child c found) out port h₁ h₂ dir

private theorem component_next
    (C : Component (m.interfaces child) ((m.children child).getD []))
    (hC : C = moduleChild d.design d.wellFormed m c hm
      (List.mem_of_find?_eq_some found) child (by simpa using List.find?_some found)
      (localComponent d c (List.mem_of_find?_eq_some found)
        (designChildren d env c (List.mem_of_find?_eq_some found))))
    (state : C.State) (state' : State d env c (List.mem_of_find?_eq_some found))
    (hs : HEq state state') (conn : PortValues (m.interfaces child) .input) :
    HEq (C.next state conn)
      (step d env c (List.mem_of_find?_eq_some found) state'
        (transportInput (child_ports d m hm child c found) conn)).1 := by
  subst hC
  exact moduleChild_next d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found)
    child (by simpa using List.find?_some found) _ state state' conn
    (transportInput (child_ports d m hm child c found) conn) hs (transportInput_heq _ conn)

/-- The output of a module child is the step output of the child module. -/
theorem child_out (state : CellState m (.inst i p n child inputs)
      (designChildren d env m hm ⟨.inst i p n child inputs, member⟩))
    (conn : PortValues (m.interfaces child) .input) (port : Port)
    (h₁ : port ∈ m.interfaces child) (h₂ : port ∈ c.ports) (dir : port.dir = .output) :
    (designChildren d env m hm ⟨.inst i p n child inputs, member⟩).out state conn
      ⟨port, h₁, dir⟩ =
      (step d env c (List.mem_of_find?_eq_some found)
        (cast (State_inst_module d env m hm i p n child inputs member c found) state)
        (transportInput (child_ports d m hm child c found) conn)).2 ⟨port, h₂, dir⟩ :=
  component_out d env m hm child c found _
    (designChildren_inst_module d env m hm i p n child inputs member c found) state _
    (cast_heq _ _).symm conn port h₁ h₂ dir

/-- The next state of a module child is the step state of the child module. -/
theorem child_next (state : CellState m (.inst i p n child inputs)
      (designChildren d env m hm ⟨.inst i p n child inputs, member⟩))
    (conn : PortValues (m.interfaces child) .input) :
    cast (State_inst_module d env m hm i p n child inputs member c found)
      ((designChildren d env m hm ⟨.inst i p n child inputs, member⟩).next state conn) =
      (step d env c (List.mem_of_find?_eq_some found)
        (cast (State_inst_module d env m hm i p n child inputs member c found) state)
        (transportInput (child_ports d m hm child c found) conn)).1 := by
  apply eq_of_heq
  exact (cast_heq _ _).trans (component_next d env m hm child c found _
    (designChildren_inst_module d env m hm i p n child inputs member c found) state _
    (cast_heq _ _).symm conn)

end

end Silicon.Core.LowerProof
