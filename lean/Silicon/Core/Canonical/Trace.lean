import Silicon.Core.Canonical.Step

/-! A step simulation preserves named traces from the all-zero initial state. -/
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
  | nil => simp only [List.map_nil, Interp.run_nil]
  | cons vector rest ih =>
    obtain ⟨outputs, states⟩ := simulate a b same vector
    simp only [List.map_cons, Interp.run_cons]
    rw [outputs, ih _ _ states]

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

/-! Canonical order preserves each step from any pair of equal named states. -/
open NamedRun in
theorem canonicalize_step (d : Design) (t t' : Typed.Design)
    (h : check d = .ok t) (h' : check (canonicalize d) = .ok t')
    (noExterns : t.externs = []) :
    let c := CertifiedDesign.ofCheck d t h
    let c' := CertifiedDesign.ofCheck (canonicalize d) t' h'
    let ne := canonicalize_noExterns d t t' h h' noExterns
    let m := top c noExterns
    let m' := top c' ne
    ∀ (a : State c (emptyEnv c noExterns) m.val m.property)
      (b : State c' (emptyEnv c' ne) m'.val m'.property),
      namedState c (emptyEnv c noExterns) noExterns m.val m.property a =
        namedState c' (emptyEnv c' ne) ne m'.val m'.property b →
      ∀ vector : List (String × Nat),
      let left := Interp.step c (emptyEnv c noExterns) m.val m.property a
        (inputValues m.val vector)
      let right := Interp.step c' (emptyEnv c' ne) m'.val m'.property b
        (inputValues m'.val vector)
      outputValues m.val left.2 = outputValues m'.val right.2 ∧
        namedState c (emptyEnv c noExterns) noExterns m.val m.property left.1 =
          namedState c' (emptyEnv c' ne) ne m'.val m'.property right.1 := by
  intro c c' ne m m' a b same vector
  have order : Reorder c.design.erase c'.design.erase := by
    change Reorder t.erase t'.erase
    rw [check_sound_erase d t h, check_sound_erase (canonicalize d) t' h']
    exact canonicalize_reorder d
  have related := top_reorder c c' noExterns ne order
  have result := namedStep_reorder c c' (emptyEnv c noExterns) (emptyEnv c' ne)
    noExterns ne order m.val m'.val m.property m'.property related a b same
    (inputValues m.val vector) (inputValues m'.val vector)
    (inputValues_heq m.val m'.val related.ports vector)
  exact ⟨outputValues_eq m.val m'.val related.ports _ _ result.1, result.2⟩

theorem canonicalize_sem (d : Design) (t t' : Typed.Design)
    (h : check d = .ok t) (h' : check (canonicalize d) = .ok t')
    (noExterns : t.externs = [])
    (inputs : List (List (String × Nat))) :
    namedRun (Semantics.CertifiedDesign.ofCheck d t h) inputs noExterns =
      namedRun (Semantics.CertifiedDesign.ofCheck (canonicalize d) t' h') inputs
        (canonicalize_noExterns d t t' h h' noExterns) := by
  apply NamedRun.run_eq_of_named_step
  · exact canonicalize_step d t t' h h' noExterns
  · apply NamedRun.zero_top_reorder
    change Reorder t.erase t'.erase
    rw [check_sound_erase d t h, check_sound_erase (canonicalize d) t' h']
    exact canonicalize_reorder d

end Silicon.Core
