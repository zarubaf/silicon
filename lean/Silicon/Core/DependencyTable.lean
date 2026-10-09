import Silicon.Core.Check

/-! Hierarchy ranks bound the rounds needed to infer child dependencies. -/
namespace Silicon.Core.Typed

theorem infer_congr_children (m : Core.Module) (left right : String → Option Deps)
    (h : ∀ child ∈ childNames m, left child = right child) :
    Deps.infer m left = Deps.infer m right := by
  have each : ∀ s ∈ m.body, Deps.equations left s = Deps.equations right s := by
    intro s hs
    cases s <;> try rfl
    rename_i pos name child inputs
    simp only [Deps.equations, h child (List.mem_filterMap.mpr ⟨_, hs, rfl⟩)]
  have eqs : m.body.flatMap (Deps.equations left) = m.body.flatMap (Deps.equations right) := by
    generalize m.body = body at each ⊢
    induction body with
    | nil => rfl
    | cons s rest ih =>
      simp only [List.flatMap_cons, each s (by simp)]
      rw [ih (fun t ht => each t (by simp [ht]))]
  have graph : Deps.graph m left = Deps.graph m right := by
    simp only [Deps.graph, eqs]
  unfold Deps.infer
  rw [graph]

private theorem lookup_map_item (items : List Item) (values : Item → Deps)
    (hn : (items.map Item.name).Nodup) (item : Item) (hi : item ∈ items) :
    (items.map fun i => (Item.name i, values i)).lookup (Item.name item) = some (values item) := by
  induction items with
  | nil => simp at hi
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · have ne : Item.name item ≠ Item.name first := by
        intro he
        exact hn.1 (he ▸ List.mem_map.mpr ⟨item, hi, rfl⟩)
      simp only [List.map_cons, List.lookup_cons, beq_eq_false_iff_ne.mpr ne]
      exact ih hn.2 hi

private theorem lookup_map_absent (items : List Item) (values : Item → Deps)
    (name : String) (absent : ∀ i ∈ items, Item.name i ≠ name) :
    (items.map fun i => (Item.name i, values i)).lookup name = none := by
  rw [List.lookup_eq_none_iff]
  intro pair hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  simp [Ne.symm (absent i hi)]

theorem designDeps_extern (d : Core.Design) (hn : (d.items.map Item.name).Nodup)
    (e : Extern) (he : Item.extern e ∈ d.items) (fuel : Nat) :
    designDeps d (fuel + 1) e.name = some (externDeps e) := by
  exact lookup_map_item d.items _ hn (.extern e) he

theorem designDeps_module (d : Core.Design) (hn : (d.items.map Item.name).Nodup)
    (m : Core.Module) (hm : Item.module m ∈ d.items) (fuel : Nat) :
    designDeps d (fuel + 1) m.name = some (Deps.infer m (designDeps d fuel)) := by
  exact lookup_map_item d.items _ hn (.module m) hm

private theorem designDeps_absent (d : Core.Design) (name : String)
    (absent : ∀ i ∈ d.items, Item.name i ≠ name) (fuel : Nat) :
    designDeps d fuel name = none := by
  cases fuel with
  | zero => rfl
  | succ fuel => exact lookup_map_absent d.items _ name absent

theorem designDeps_stable (d : Core.Design) (hn : (d.items.map Item.name).Nodup)
    (q : Deps.Node → Nat)
    (edges : ∀ row ∈ hierarchyGraph d, ∀ dep ∈ row.2, q dep < q row.1)
    (fuel other : Nat) (name : String)
    (hf : q (.name name) < fuel) (ho : q (.name name) < other) :
    designDeps d fuel name = designDeps d other name := by
  induction fuel generalizing other name with
  | zero => omega
  | succ fuel ih =>
    cases other with
    | zero => omega
    | succ other =>
      by_cases existsItem : ∃ item ∈ d.items, Item.name item = name
      · obtain ⟨item, hi, rfl⟩ := existsItem
        cases item with
        | extern e =>
          simp only [Item.name]
          rw [designDeps_extern d hn e hi, designDeps_extern d hn e hi]
        | module m =>
          simp only [Item.name]
          rw [designDeps_module d hn m hi, designDeps_module d hn m hi]
          congr 1
          apply infer_congr_children
          intro child hc
          have hm : m ∈ modules d := List.mem_filterMap.mpr ⟨.module m, hi, rfl⟩
          have he := edges (.name m.name, (childNames m).map Deps.Node.name)
            (List.mem_map.mpr ⟨m, hm, rfl⟩) (.name child)
            (List.mem_map.mpr ⟨child, hc, rfl⟩)
          change q (.name child) < q (.name m.name) at he
          apply ih other child <;> simp only [Item.name] at hf ho <;> omega
      · have absent : ∀ item ∈ d.items, Item.name item ≠ name := by
          intro item hi he
          exact existsItem ⟨item, hi, he⟩
        rw [designDeps_absent d name absent, designDeps_absent d name absent]

theorem designDeps_saturated (d : Core.Design) (wf : WellFormed d)
    (m : Core.Module) (hm : Item.module m ∈ d.items) :
    designDeps d d.depsFuel m.name =
      some (Deps.infer m (designDeps d d.depsFuel)) := by
  obtain ⟨q, bound, edges⟩ := bounded_ranks (hierarchyGraph d) wf.2.2.2.2.2.2.2.2.1
  have lengthBound : (hierarchyGraph d).length ≤ d.items.length := by
    simp only [hierarchyGraph, List.length_map, modules]
    exact List.length_filterMap_le _ _
  have stable : designDeps d d.depsFuel m.name =
      designDeps d (d.items.length + 2) m.name :=
    designDeps_stable d wf.1.1.1 q edges _ _ _
      (by have := bound (.name m.name); unfold Core.Design.depsFuel; omega)
      (by have := bound (.name m.name); omega)
  rw [stable]
  exact designDeps_module d wf.1.1.1 m hm d.depsFuel

theorem Design.dependencies (d : Design) (wf : WellFormed d.erase)
    (m : Module) (hm : m ∈ d.bodies) :
    designDeps d.erase d.erase.depsFuel m.name =
      some (Deps.infer m.erase m.children) := by
  have env := d.environments m hm
  have result := designDeps_saturated d.erase wf m.erase env.2.2
  have children : m.children = designDeps d.erase d.erase.depsFuel := env.2.1
  simpa only [← children, Module.erase] using result

end Silicon.Core.Typed
