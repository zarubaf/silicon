-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Expression
import Silicon.Core.Check

/-!
Port values retain their interface types. Extern contracts constrain current outputs,
while each extern defines its own state and next-state function.
-/
namespace Silicon.Core.Semantics

abbrev PortRef (ports : List Port) (dir : PortDir) :=
  {port : Port // port ∈ ports ∧ port.dir = dir}

abbrev PortValues (ports : List Port) (dir : PortDir) :=
  (port : PortRef ports dir) → TyValue port.val.ty

abbrev Input (m : Typed.Module) := PortValues m.ports .input
abbrev Output (m : Typed.Module) := PortValues m.ports .output

/-! An output contract refers to input names in the declared port interface. -/
structure Component (ports : List Port) (deps : Deps) where
  State : Type
  out : State → PortValues ports .input → PortValues ports .output
  next : State → PortValues ports .input → State
  out_respects : ∀ s a b (output : PortRef ports .output),
    (∀ input : PortRef ports .input,
      input.val.name ∈ (deps.lookup output.val.name).getD [] → a input = b input) →
    out s a output = out s b output

abbrev ExternSem (extern : Extern) := Component extern.ports (Typed.externDeps extern)

abbrev Env (d : Typed.Design) :=
  (extern : Extern) → extern ∈ d.externs → ExternSem extern

/-! Typed elaboration alone does not certify unique names or complete connections. -/
structure CertifiedDesign where
  design : Typed.Design
  wellFormed : WellFormed design.erase

def CertifiedDesign.ofCheck (raw : Core.Design) (typed : Typed.Design)
    (accepted : check raw = .ok typed) : CertifiedDesign :=
  ⟨typed, by rw [check_sound_erase raw typed accepted]; exact (check_sound raw typed accepted).1⟩

end Silicon.Core.Semantics
