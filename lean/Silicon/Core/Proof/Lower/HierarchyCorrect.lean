-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleCorrect

/-!
Every lowered module of a checked design without externs is correct. A child has a lower
module level than its parent, so the proof of a parent may use the proofs of its children.
-/
namespace Silicon.Core.LowerProof

open Semantics

theorem modules_correct (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (noExterns : t.externs = []) (env : Env (certified raw t h).design) (m : Typed.Module)
    (hm : m ∈ t.bodies) : ModuleCorrect raw t h noExterns env m hm :=
  module_correct raw t h noExterns m hm env fun i p n child inputs _member c found =>
    modules_correct raw t h noExterns env c (List.mem_of_find?_eq_some found)
termination_by moduleLevel (certified raw t h).design.erase (certified raw t h).wellFormed m.name
decreasing_by
  have stmt := instance_member m i p n child inputs _member
  have childMem : child ∈ Typed.childNames m.erase := List.mem_filterMap.mpr ⟨_, stmt, rfl⟩
  have named : c.name = child := by simpa using List.find?_some found
  simpa only [named, Typed.Module.erase] using
    moduleLevel_lower (certified raw t h).design.erase (certified raw t h).wellFormed m.erase
      (module_mem (certified raw t h).design m hm) child childMem

end Silicon.Core.LowerProof
