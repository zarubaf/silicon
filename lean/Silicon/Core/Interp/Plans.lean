import Silicon.Core.Interp.Prepared

namespace Silicon.Core.Interp

open Semantics

/-! A run shares preparations for all modules in the design. -/
abbrev ModuleKey (d : CertifiedDesign) (_limit : Nat) :=
  {name : String // (d.design.bodies.find? (·.name == name)).isSome}

def selectedModule (d : CertifiedDesign) (limit : Nat) (key : ModuleKey d limit) :
    {m : Typed.Module // m ∈ d.design.bodies} :=
  let found := d.design.bodies.find? (·.name == key.val)
  let m := found.get key.property
  ⟨m, List.mem_of_find?_eq_some (Option.some_get key.property).symm⟩

/-! Store the table as data so a key lookup cannot rebuild its entries. -/
abbrev ModulePreparations (d : CertifiedDesign) (limit : Nat) :=
  Table (fun key : ModuleKey d limit =>
    prepare d (selectedModule d limit key).val (selectedModule d limit key).property)

def prepareModules (d : CertifiedDesign) (limit : Nat) : ModulePreparations d limit := by
  let keys : List (ModuleKey d limit) := (d.design.bodies.map (·.name)).filterMap fun name =>
    if h : (d.design.bodies.find? (·.name == name)).isSome then some ⟨name, h⟩ else none
  let table := indexed (fun key : ModuleKey d limit =>
    prepare d (selectedModule d limit key).val (selectedModule d limit key).property) keys (by
      intro key
      obtain ⟨m, found⟩ := Option.isSome_iff_exists.mp key.property
      have name : m.name = key.val := by simpa using List.find?_some found
      apply List.mem_filterMap.mpr
      exact ⟨key.val, List.mem_map.mpr ⟨m, List.mem_of_find?_eq_some found, name⟩,
        by simp [key.property]⟩)
  exact table

def modulePrepared (d : CertifiedDesign) (limit : Nat) (plans : ModulePreparations d limit)
    (name : String) (m : Typed.Module) (found : d.design.bodies.find? (·.name == name) = some m)
    (_lower : moduleLevel d.design.erase d.wellFormed name < limit) :
    Prepared d m (List.mem_of_find?_eq_some found) := by
  let key : ModuleKey d limit := ⟨name, by simp [found]⟩
  have same : (selectedModule d limit key).val = m := by
    simp [selectedModule, key, found]
  exact cast (congrArg (fun m : {m : Typed.Module // m ∈ d.design.bodies} =>
    Prepared d m.val m.property) (show selectedModule d limit key =
      ⟨m, List.mem_of_find?_eq_some found⟩ from Subtype.ext same)) (plans.get key)

end Silicon.Core.Interp
