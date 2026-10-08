import Silicon.Core.Semantics.Interface

/-!
Each register, memory, and child instance has its own state cell.
Combinational equations carry no state.
-/
namespace Silicon.Core.Semantics

abbrev EquationRef (m : Typed.Module) := {equation // equation ∈ m.body}

def ChildModel (m : Typed.Module) : Typed.Equation m.ctx m.interfaces → Type 1
  | .inst _ _ _ child _ => Component (m.interfaces child) ((m.children child).getD [])
  | _ => PUnit

abbrev Children (m : Typed.Module) := (equation : EquationRef m) → ChildModel m equation.val

def CellState (m : Typed.Module) :
    (equation : Typed.Equation m.ctx m.interfaces) → ChildModel m equation → Type
  | .reg _ _ _ width .., _ => Value width
  | .mem _ _ _ width depth .., _ => Fin depth → Value width
  | .inst .., child => child.State
  | _, _ => Unit

abbrev LocalState (m : Typed.Module) (children : Children m) :=
  (equation : EquationRef m) → CellState m equation.val (children equation)

/-! Child inputs use values from the parent's current-cycle solution. -/
def ConnectionType (m : Typed.Module) : Typed.Equation m.ctx m.interfaces → Type
  | .inst _ _ _ child _ => PortValues (m.interfaces child) .input
  | _ => Unit

abbrev ConnectionValues (m : Typed.Module) :=
  (equation : EquationRef m) → ConnectionType m equation.val

/-! All state cells update together after the equations yield their current-cycle values. -/
def nextLocalState (m : Typed.Module) (children : Children m)
    (state : LocalState m children) (values : Valuation m.ctx) (memories : Memories m.ctx)
    (connections : ConnectionValues m) : LocalState m children
  | ⟨.reg _ _ _ _ _ _ reset _ _ next, _⟩ =>
    nextRegister values memories reset next
  | ⟨.mem i p name width depth clock target writes, member⟩ =>
    nextMemory values memories
      (state ⟨.mem i p name width depth clock target writes, member⟩) writes
  | ⟨.inst i p name child inputs, member⟩ =>
    let e : EquationRef m := ⟨.inst i p name child inputs, member⟩
    (children e).next (state e) (connections e)
  | ⟨.let_ .., _⟩ | ⟨.assign .., _⟩ => ()

end Silicon.Core.Semantics
