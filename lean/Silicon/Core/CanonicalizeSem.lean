import Silicon.Core.NamedStep

/-! Canonical order preserves named traces from the all-zero initial state. -/
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
  let encode (ps : List Port) (values : PortValues ps .output) : List (String × Nat) :=
    ps.attach.filterMap fun p =>
      if h : p.val.dir = .output then
        match ht : p.val.ty with
        | .clock => none
        | .bits _ => some (p.val.name,
            (cast (congrArg TyValue ht) (values ⟨p.val, p.property, h⟩)).toNat)
      else none
  have congr (ps qs : List Port) (h : ps = qs) (a : PortValues ps .output)
      (b : PortValues qs .output) (he : HEq a b) : encode ps a = encode qs b := by
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

theorem canonicalize_sem (d : Design) (t t' : Typed.Design)
    (h : check d = .ok t) (h' : check (canonicalize d) = .ok t')
    (noExterns : t.externs = []) (noExterns' : t'.externs = [])
    (inputs : List (List (String × Nat))) :
    namedRun (Semantics.CertifiedDesign.ofCheck d t h) inputs noExterns =
      namedRun (Semantics.CertifiedDesign.ofCheck (canonicalize d) t' h') inputs noExterns' := by
  apply namedRun_reorder _ _ _ noExterns noExterns' inputs
  change Reorder t.erase t'.erase
  rw [check_sound_erase d t h, check_sound_erase (canonicalize d) t' h']
  exact canonicalize_reorder d

end Silicon.Core
