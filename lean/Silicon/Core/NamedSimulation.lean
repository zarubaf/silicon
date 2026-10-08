import Silicon.Core.NamedRun

/-! A step simulation gives equal named traces for every finite input sequence. -/
namespace Silicon.Core

open Semantics

namespace NamedRun

theorem run_eq_of_named_step (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (simulate : ∀ (a : State d env m hm) (b : State d' env' m' hm'),
      namedState d env noExterns m hm a = namedState d' env' noExterns' m' hm' b →
      ∀ vector : List (String × Nat),
      let left := Interp.step d env m hm a (inputValues m vector)
      let right := Interp.step d' env' m' hm' b (inputValues m' vector)
      outputValues m left.2 = outputValues m' right.2 ∧
        namedState d env noExterns m hm left.1 =
          namedState d' env' noExterns' m' hm' right.1)
    (a : State d env m hm) (b : State d' env' m' hm')
    (same : namedState d env noExterns m hm a = namedState d' env' noExterns' m' hm' b)
    (inputs : List (List (String × Nat))) :
    (Interp.run d env m hm a (inputs.map (inputValues m))).map (outputValues m) =
      (Interp.run d' env' m' hm' b (inputs.map (inputValues m'))).map (outputValues m') := by
  induction inputs generalizing a b with
  | nil => rfl
  | cons vector rest ih =>
    obtain ⟨outputs, states⟩ := simulate a b same vector
    simp only [List.map_cons, Interp.run]
    rw [outputs, ih _ _ states]

end NamedRun

end Silicon.Core
