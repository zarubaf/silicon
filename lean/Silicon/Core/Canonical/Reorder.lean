import Silicon.Core.Canonical.WellFormed
import Silicon.Core.Semantics.Step

/-! Reordered modules retain their typed interfaces and context lookups. -/
namespace Silicon.Core

open Semantics

namespace Semantics

theorem erased_module_found (d : Typed.Design) (c : Core.Module)
    (member : Core.Item.module c ∈ d.erase.items) :
    ∃ m, d.bodies.find? (·.name == c.name) = some m ∧ m.erase = c := by
  obtain ⟨key, _, he⟩ := List.mem_filterMap.mp member
  change (match d.bodies.find? (·.name == key) with
    | some m => some (.module m.erase)
    | none => (d.externs.find? (·.name == key)).map Item.extern) = some (.module c) at he
  cases found : d.bodies.find? (·.name == key) with
  | some m =>
    simp only [found] at he
    have erased := Core.Item.module.inj (Option.some.inj he)
    have named : m.name = key := by simpa using List.find?_some found
    exact ⟨m, by simpa only [← erased, Typed.Module.erase, named] using found, erased⟩
  | none =>
    simp only [found] at he
    obtain ⟨e, _, impossible⟩ := Option.map_eq_some_iff.mp he
    cases impossible

end Semantics

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
