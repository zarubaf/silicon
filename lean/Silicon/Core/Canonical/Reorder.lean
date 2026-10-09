import Silicon.Core.Canonical.WellFormed
import Silicon.Core.Semantics.Step

/-! Reordered modules retain their typed interfaces and context lookups. -/
namespace Silicon.Core

open Semantics

namespace Reorder

theorem typed_module {d d' : CertifiedDesign} (order : Reorder d.design.erase d'.design.erase)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    ∃ m', d'.design.bodies.find? (·.name == m.name) = some m' ∧
      ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase) := by
  obtain ⟨item, member, related⟩ := order.items.left (d.design.environments m hm).2.2
  cases related with
  | module raw raw' pos name ports body =>
    obtain ⟨m', found, erased⟩ := erased_module_found d'.design raw' member
    refine ⟨m', ?_, ?_⟩
    · simpa only [name, Typed.Module.erase] using found
    · rw [erased]
      exact .module _ _ pos name ports body

theorem typed_context {d d' : CertifiedDesign} (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (node : Deps.Node) :
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

end Silicon.Core
