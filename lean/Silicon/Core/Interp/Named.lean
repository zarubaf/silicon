import Silicon.Core.Interp

/-!
A named run reads inputs by port name and records outputs in port order.
It starts with zero state and requires a design without externs.
-/
namespace Silicon.Core

open Semantics

namespace NamedRun

def inputValues (m : Typed.Module) (values : List (String × Nat)) : Input m :=
  fun p => match p.val.ty with
  | .clock => ()
  | .bits w => BitVec.ofNat w ((values.lookup p.val.name).getD 0)

def encodeOutputs (ports : List Port) (values : PortValues ports .output) :
    List (String × Nat) :=
  ports.attach.filterMap fun p =>
    if h : p.val.dir = .output then
      match ht : p.val.ty with
      | .clock => none
      | .bits _ => some (p.val.name,
          (cast (congrArg TyValue ht) (values ⟨p.val, p.property, h⟩)).toNat)
    else none

def outputValues (m : Typed.Module) (values : Output m) : List (String × Nat) :=
  encodeOutputs m.ports values

def emptyEnv (t : CertifiedDesign) (noExterns : t.design.externs = []) : Env t.design :=
  fun _ member => False.elim (by simp [noExterns] at member)

theorem top_exists (t : CertifiedDesign) (noExterns : t.design.externs = []) :
    ∃ m, t.design.bodies.find? (·.name == t.design.top) = some m := by
  cases found : t.design.bodies.find? (·.name == t.design.top) with
  | some m => exact ⟨m, rfl⟩
  | none =>
    have resolved := t.wellFormed.2.1.1
    have item : ∃ i ∈ t.design.erase.items, Typed.itemName i = t.design.top := by
      cases hi : Rules.findItem t.design.erase t.design.erase.top with
      | none => simp [hi] at resolved
      | some i =>
        exact ⟨i, List.mem_of_find?_eq_some hi, by
          simpa [Rules.findItem, Typed.Design.erase, Typed.assembleDesign] using
            List.find?_some hi⟩
    obtain ⟨e, he, _⟩ := external_exists t.design t.design.top item found
    simp [noExterns] at he

def top (t : CertifiedDesign) (noExterns : t.design.externs = []) :
    {m : Typed.Module // m ∈ t.design.bodies} :=
  match found : t.design.bodies.find? (·.name == t.design.top) with
  | some m => ⟨m, List.mem_of_find?_eq_some found⟩
  | none => False.elim (by
      obtain ⟨m, hm⟩ := top_exists t noExterns
      rw [found] at hm
      contradiction)

end NamedRun

def namedRun (t : CertifiedDesign) (inputs : List (List (String × Nat)))
    (noExterns : t.design.externs = []) : List (List (String × Nat)) :=
  let env := NamedRun.emptyEnv t noExterns
  let m := NamedRun.top t noExterns
  (Interp.run t env m.val m.property (Interp.zeroState t env noExterns m.val m.property)
    (inputs.map (NamedRun.inputValues m.val))).map (NamedRun.outputValues m.val)

end Silicon.Core

