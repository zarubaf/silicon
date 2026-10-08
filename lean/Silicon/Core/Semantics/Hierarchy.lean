import Silicon.Core.Semantics.Decode
import Silicon.Core.DependencyTable

/-! Hierarchy ranks build each module from the components of its children. -/
namespace Silicon.Core.Semantics

open Typed

theorem erased_item_origin (d : Typed.Design) (item : Item) (hi : item ∈ d.erase.items) :
    (∃ m ∈ d.bodies, item = .module m.erase) ∨
      ∃ e ∈ d.externs, item = .extern e := by
  obtain ⟨name, _, he⟩ := List.mem_filterMap.mp hi
  change (match d.bodies.find? (·.name == name) with
    | some m => some (.module m.erase)
    | none => (d.externs.find? (·.name == name)).map Item.extern) = some item at he
  cases hm : d.bodies.find? (·.name == name) with
  | some m =>
    simp only [hm] at he
    exact Or.inl ⟨m, List.mem_of_find?_eq_some hm, (Option.some.inj he).symm⟩
  | none =>
    simp only [hm] at he
    obtain ⟨e, he', he⟩ := Option.map_eq_some_iff.mp he
    exact Or.inr ⟨e, List.mem_of_find?_eq_some he', he.symm⟩

private theorem find_item_mem (items : List Item) (hn : (items.map itemName).Nodup)
    (item : Item) (hi : item ∈ items) :
    items.find? (fun i => itemName i == itemName item) = some item := by
  induction items with
  | nil => simp at hi
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · have ne : itemName first ≠ itemName item := by
        intro he
        exact hn.1 (he ▸ List.mem_map.mpr ⟨item, hi, rfl⟩)
      simpa [List.find?_cons, ne] using ih hn.2 hi

theorem portsOf_item (d : Core.Design) (hn : (d.items.map itemName).Nodup)
    (item : Item) (hi : item ∈ d.items) : portsOf d (itemName item) = itemPorts item := by
  simp [portsOf, find_item_mem d.items hn item hi]

abbrev NamedComponent (d : Typed.Design) (name : String) :=
  Component (portsOf d.erase name)
    ((designDeps d.erase (d.erase.items.length + 1) name).getD [])

abbrev LocalBuilder (d : Typed.Design) :=
  (m : Typed.Module) → m ∈ d.bodies → Children m →
    Component m.ports (Deps.infer m.erase m.children)

private noncomputable def namedComponent (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) (q : Deps.Node → Nat)
    (edges : ∀ row ∈ hierarchyGraph d.erase, ∀ dep ∈ row.2, q dep < q row.1)
    (rank : Nat) : ∀ name, q (.name name) = rank →
      ∀ item ∈ d.erase.items, itemName item = name → NamedComponent d name := by
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro name hq item hi hn
    classical
    by_cases origin : ∃ m ∈ d.bodies, item = .module m.erase
    · let m := origin.choose
      have hm : m ∈ d.bodies := origin.choose_spec.1
      have itemEq : item = .module m.erase := origin.choose_spec.2
      have itemHi : Item.module m.erase ∈ d.erase.items := itemEq ▸ hi
      have hname : m.name = name := by simpa [itemEq, itemName, Typed.Module.erase] using hn
      rw [← hname] at hq ⊢
      change q (.name m.name) = rank at hq
      let children : Children m := by
        intro ⟨equation, member⟩
        cases equation with
        | inst index pos inst child inputs =>
          let raw := inputs.map fun input => (input.1.val.name, input.2.erase)
          have stmt : Core.Stmt.inst pos inst child raw ∈ m.erase.body := by
            apply (Ownership.mem_equationsErase m.body _).mpr
            exact ⟨.inst index pos inst child inputs, member, index,
              .inst pos inst child inputs, by simp [Typed.Equation.parts], rfl⟩
          have resolved := (wf.2.1.2 m.erase (module_mem d m hm) _ stmt).1
          let childItem := resolved.choose
          have found := resolved.choose_spec.1
          have childMem := List.mem_of_find?_eq_some found
          have childName : itemName childItem = child := by
            simpa [childItem, Rules.findItem] using List.find?_some found
          have childNames : child ∈ Typed.childNames m.erase :=
            List.mem_filterMap.mpr ⟨.inst pos inst child raw, stmt, rfl⟩
          have lower := edges (.name m.name, (Typed.childNames m.erase).map Deps.Node.name)
            (List.mem_map.mpr ⟨m.erase, module_mem d m hm, rfl⟩) (.name child)
            (List.mem_map.mpr ⟨child, childNames, rfl⟩)
          change q (.name child) < q (.name m.name) at lower
          have model := ih (q (.name child)) (by omega) child rfl childItem childMem childName
          have interfaces : m.interfaces = portsOf d.erase := (d.environments m hm).1
          have dependencies : m.children = designDeps d.erase (d.erase.items.length + 1) :=
            (d.environments m hm).2.1
          simpa only [ChildModel, NamedComponent, interfaces, dependencies] using model
        | _ => exact PUnit.unit
      let result := build m hm children
      have ports := portsOf_item d.erase wf.1.1.1 (.module m.erase) itemHi
      have deps := d.dependencies wf m hm
      simpa only [NamedComponent, deps, Option.getD_some, itemName, itemPorts,
        Typed.Module.erase] using ports ▸ result
    · have external := (erased_item_origin d item hi).resolve_left origin
      let e := external.choose
      have he : e ∈ d.externs := external.choose_spec.1
      have itemEq : item = .extern e := external.choose_spec.2
      have itemHi : Item.extern e ∈ d.erase.items := itemEq ▸ hi
      have hname : e.name = name := by simpa [itemEq, itemName] using hn
      rw [← hname] at hq ⊢
      have ports := portsOf_item d.erase wf.1.1.1 (.extern e) itemHi
      have deps := designDeps_extern d.erase wf.1.1.1 e itemHi d.erase.items.length
      let result := env e he
      simpa only [NamedComponent, deps, Option.getD_some, itemName, itemPorts] using ports ▸ result

/-! The selected item owns its complete hierarchy state. -/
noncomputable def assembleComponent (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) (item : Item) (hi : item ∈ d.erase.items) :
    NamedComponent d (itemName item) := by
  let ranks := bounded_ranks (hierarchyGraph d.erase) wf.2.2.2.2.2.2.2.2.1
  let q := ranks.choose
  exact namedComponent d wf env build q ranks.choose_spec.2 (q (.name (itemName item)))
    (itemName item) rfl item hi rfl

/-! Expose the concrete child product for the module's equation and state interfaces. -/
noncomputable def assembleChildren (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) (m : Typed.Module) (hm : m ∈ d.bodies) :
    Children m := by
  intro ⟨equation, member⟩
  cases equation with
  | inst index pos inst child inputs =>
    let raw := inputs.map fun input => (input.1.val.name, input.2.erase)
    have stmt : Core.Stmt.inst pos inst child raw ∈ m.erase.body := by
      apply (Ownership.mem_equationsErase m.body _).mpr
      exact ⟨.inst index pos inst child inputs, member, index,
        .inst pos inst child inputs, by simp [Typed.Equation.parts], rfl⟩
    have resolved := (wf.2.1.2 m.erase (module_mem d m hm) _ stmt).1
    let item := resolved.choose
    have found := resolved.choose_spec.1
    have member := List.mem_of_find?_eq_some found
    have name : itemName item = child := by
      simpa [item, Rules.findItem] using List.find?_some found
    let model : NamedComponent d child := name ▸ assembleComponent d wf env build item member
    have interfaces : m.interfaces = portsOf d.erase := (d.environments m hm).1
    have dependencies : m.children = designDeps d.erase (d.erase.items.length + 1) :=
      (d.environments m hm).2.1
    simpa only [ChildModel, NamedComponent, interfaces, dependencies] using model
  | _ => exact PUnit.unit

theorem topItem_exists (d : Typed.Design) (wf : WellFormed d.erase) :
    ∃ item ∈ d.erase.items, itemName item = d.erase.top := by
  have resolved := wf.2.1.1
  cases found : Rules.findItem d.erase d.erase.top with
  | none => simp [found] at resolved
  | some item =>
    refine ⟨item, List.mem_of_find?_eq_some found, ?_⟩
    simpa [Rules.findItem] using List.find?_some found

noncomputable def assembleTop (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) : NamedComponent d d.erase.top := by
  let origin := topItem_exists d wf
  let item := origin.choose
  have hi : item ∈ d.erase.items := origin.choose_spec.1
  have hn : itemName item = d.erase.top := origin.choose_spec.2
  exact hn ▸ assembleComponent d wf env build item hi

end Silicon.Core.Semantics
