import Silicon.Core.Semantics.NamedZero
import Silicon.Core.NamedSimulation

/-! Reordered erased modules retain their named interfaces and context lookups. -/
namespace Silicon.Core

open Semantics

namespace Reorder

theorem typed_module {d d' : CertifiedDesign} (order : Reorder d.design.erase d'.design.erase)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    ∃ m', d'.design.bodies.find? (·.name == m.name) = some m' ∧
      ItemReorder (.module m.erase) (.module m'.erase) := by
  obtain ⟨item, member, related⟩ := order.2.left (d.design.environments m hm).2.2
  cases related with
  | module raw raw' pos name ports body =>
    obtain ⟨m', found, erased⟩ := erased_module_found d'.design raw' member
    refine ⟨m', ?_, ?_⟩
    · simpa only [name, Typed.Module.erase] using found
    · rw [erased]
      exact .module _ _ pos name ports body

theorem typed_context {d d' : CertifiedDesign} (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder (.module m.erase) (.module m'.erase)) (node : Deps.Node) :
    m.ctx.lookup node = m'.ctx.lookup node := by
  rw [d.design.module_context m hm, d'.design.module_context m' hm']
  cases related with
  | module _ _ _ _ ports body =>
    exact order.context_lookup d.wellFormed.1 (module_mem d.design m hm) ports body node

theorem typed_interfaces {d d' : CertifiedDesign}
    (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies) :
    m.interfaces = m'.interfaces := by
  rw [(d.design.environments m hm).1, (d'.design.environments m' hm').1]
  exact order.portsOf d.wellFormed.1

end Reorder

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
    ItemReorder (.module (top d noExterns).val.erase)
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
