import Silicon.Core.Canonical.Zero

/-! Reordered erased modules retain their named interfaces and context lookups. -/
namespace Silicon.Core

open Semantics

namespace NamedRun

theorem top_found (d : CertifiedDesign) (noExterns : d.design.externs = []) :
    d.design.bodies.find? (·.name == d.design.top) = some (top d noExterns).val := by
  unfold top
  split
  · assumption
  · rename_i absent
    obtain ⟨m, found⟩ := top_exists d noExterns
    rw [absent] at found
    contradiction

theorem top_reorder (d d' : CertifiedDesign) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase) :
    ItemReorder d.design.erase.items (.module (top d noExterns).val.erase)
      (.module (top d' noExterns').val.erase) := by
  obtain ⟨m', found, related⟩ := order.typed_module (top d noExterns).val
    (top d noExterns).property
  have named : (top d noExterns).val.name = d.design.top := by
    simpa using List.find?_some (top_found d noExterns)
  have tops : d'.design.top = d.design.top := order.1
  rw [named, ← tops, top_found d' noExterns'] at found
  cases found
  exact related

theorem zero_top_reorder (d d' : CertifiedDesign) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase) :
    let m := top d noExterns
    let m' := top d' noExterns'
    namedState d (emptyEnv d noExterns) noExterns m.val m.property
      (Interp.zeroState d (emptyEnv d noExterns) noExterns m.val m.property) =
    namedState d' (emptyEnv d' noExterns') noExterns' m'.val m'.property
      (Interp.zeroState d' (emptyEnv d' noExterns') noExterns' m'.val m'.property) := by
  obtain related := top_reorder d d' noExterns noExterns' order
  cases related with
  | module _ _ _ _ _ body =>
    exact namedState_zero_reorder d d' _ _ noExterns noExterns' order _ _ _ _ body

end NamedRun

end Silicon.Core
