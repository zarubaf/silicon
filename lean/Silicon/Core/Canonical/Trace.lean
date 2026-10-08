import Silicon.Core.Canonical.Step

/-! Canonical order preserves named traces from the all-zero initial state. -/
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

namespace Silicon.Core

open Semantics

namespace NamedRun

theorem inputValues_heq (m m' : Typed.Module) (ports : m.ports = m'.ports)
    (vector : List (String × Nat)) : HEq (inputValues m vector) (inputValues m' vector) := by
  apply portValues_heq ports
  intro port hp hp' dir
  rfl

theorem outputValues_eq (m m' : Typed.Module) (ports : m.ports = m'.ports)
    (values : Output m) (values' : Output m') (same : HEq values values') :
    outputValues m values = outputValues m' values' := by
  have congr (ps qs : List Port) (h : ps = qs) (a : PortValues ps .output)
      (b : PortValues qs .output) (he : HEq a b) : encodeOutputs ps a = encodeOutputs qs b := by
    cases h
    cases he
    rfl
  exact congr m.ports m'.ports ports values values' same

end NamedRun

theorem namedRun_reorder (d d' : CertifiedDesign) (order : Reorder d.design.erase d'.design.erase)
    (noExterns : d.design.externs = []) (noExterns' : d'.design.externs = [])
    (inputs : List (List (String × Nat))) : namedRun d inputs noExterns =
      namedRun d' inputs noExterns' := by
  let m := NamedRun.top d noExterns
  let m' := NamedRun.top d' noExterns'
  have related := NamedRun.top_reorder d d' noExterns noExterns' order
  have ports : m.val.ports = m'.val.ports := related.ports
  have step := namedStep_reorder d d' (NamedRun.emptyEnv d noExterns)
    (NamedRun.emptyEnv d' noExterns') noExterns noExterns' order m.val m'.val
    m.property m'.property related
  apply NamedRun.run_eq_of_named_step d d' _ _ noExterns noExterns' m.val m'.val
    m.property m'.property
  · intro a b same vector
    have result := step a b same (NamedRun.inputValues m.val vector)
      (NamedRun.inputValues m'.val vector) (NamedRun.inputValues_heq m.val m'.val ports vector)
    exact ⟨NamedRun.outputValues_eq m.val m'.val ports _ _ result.1, result.2⟩
  · exact NamedRun.zero_top_reorder d d' noExterns noExterns' order

private theorem check_externs (d : Design) (t : Typed.Design) (h : check d = .ok t) :
    t.externs = d.items.filterMap (fun i => match i with
      | .extern e => some e | _ => none) := by
  have elaborate : Typed.elaborateDesign d = some t := by
    unfold check at h
    split at h
    · contradiction
    next he =>
      split at h
      next typed accepted => cases h; exact accepted
      next failure =>
        obtain ⟨typed, accepted⟩ := Check.elaborate_complete d ((Check.no_errors d).mp he)
        rw [failure] at accepted
        contradiction
  simp only [Typed.elaborateDesign, bind, Option.bind_eq_some_iff] at elaborate
  obtain ⟨sorted, _, elaborate⟩ := elaborate
  split at elaborate <;> try contradiction
  split at elaborate <;> try contradiction
  split at elaborate <;> try contradiction
  split at elaborate <;> try contradiction
  cases elaborate
  rfl

theorem canonicalize_noExterns (d : Design) (t t' : Typed.Design)
    (h : check d = .ok t) (h' : check (canonicalize d) = .ok t')
    (noExterns : t.externs = []) : t'.externs = [] := by
  rw [check_externs _ _ h] at noExterns
  rw [check_externs _ _ h']
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e member
  obtain ⟨item, hi, he⟩ := List.mem_filterMap.mp member
  obtain ⟨old, ho, related⟩ := (canonicalize_reorder d).items.right hi
  cases related with
  | module => cases he
  | extern old new _ _ _ _ =>
    have member : old ∈ d.items.filterMap (fun i => match i with
        | .extern e => some e | _ => none) := List.mem_filterMap.mpr ⟨_, ho, rfl⟩
    simp [noExterns] at member

theorem canonicalize_sem (d : Design) (t t' : Typed.Design)
    (h : check d = .ok t) (h' : check (canonicalize d) = .ok t')
    (noExterns : t.externs = [])
    (inputs : List (List (String × Nat))) :
    namedRun (Semantics.CertifiedDesign.ofCheck d t h) inputs noExterns =
      namedRun (Semantics.CertifiedDesign.ofCheck (canonicalize d) t' h') inputs
        (canonicalize_noExterns d t t' h h' noExterns) := by
  apply namedRun_reorder _ _ _ noExterns _ inputs
  change Reorder t.erase t'.erase
  rw [check_sound_erase d t h, check_sound_erase (canonicalize d) t' h']
  exact canonicalize_reorder d

end Silicon.Core
