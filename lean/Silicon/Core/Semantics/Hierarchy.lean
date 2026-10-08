import Silicon.Core.Semantics.Decode
import Silicon.Core.DependencyTable
import Silicon.Core.Semantics.HierarchyOrder

/-! The checker order builds each module from the components of its children. -/
namespace Silicon.Core.Semantics

open Typed

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

abbrev LocalBuilder (d : Typed.Design) :=
  (m : Typed.Module) → m ∈ d.bodies → Children m →
    Component m.ports (Deps.infer m.erase m.children)

theorem instance_member (m : Typed.Module)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body) :
    Core.Stmt.inst pos inst child (inputs.map fun input => (input.1.val.name, input.2.erase)) ∈
      m.erase.body := by
  apply (Ownership.mem_equationsErase m.body _).mpr
  exact ⟨.inst index pos inst child inputs, member, index,
    .inst pos inst child inputs, by simp [Typed.Equation.parts], rfl⟩

theorem external_exists (d : Typed.Design) (name : String)
    (existsItem : ∃ item ∈ d.erase.items, itemName item = name)
    (absent : d.bodies.find? (·.name == name) = none) :
    ∃ e, d.externs.find? (·.name == name) = some e ∧ Item.extern e ∈ d.erase.items := by
  obtain ⟨item, hi, hn⟩ := existsItem
  obtain ⟨key, hk, he⟩ := List.mem_filterMap.mp hi
  change (match d.bodies.find? (·.name == key) with
    | some m => some (.module m.erase)
    | none => (d.externs.find? (·.name == key)).map Item.extern) = some item at he
  cases hm : d.bodies.find? (·.name == key) with
  | some m =>
    simp only [hm] at he
    cases he
    have hname : m.name = key := by simpa using List.find?_some hm
    change m.name = name at hn
    rw [← hname, hn, absent] at hm
    contradiction
  | none =>
    simp only [hm] at he
    obtain ⟨e, found, he⟩ := Option.map_eq_some_iff.mp he
    subst item
    have hname : e.name = key := by simpa using List.find?_some found
    change e.name = name at hn
    exact ⟨e, by simpa only [← hn, ← hname] using found, hi⟩

/-! Interface equalities transport components without changing their state cells. -/
private def transportComponent {ports other : List Port} {deps otherDeps : Deps}
    (hp : ports = other) (hd : deps = otherDeps) (model : Component ports deps) :
    Component other otherDeps where
  State := model.State
  out := hp ▸ model.out
  next := hp ▸ model.next
  out_respects := by
    cases hp
    cases hd
    exact model.out_respects

private theorem transportComponent_state {ports other : List Port} {deps otherDeps : Deps}
    (hp : ports = other) (hd : deps = otherDeps) (model : Component ports deps) :
    (transportComponent hp hd model).State = model.State := rfl

private theorem transportComponent_out {ports other : List Port} {deps otherDeps : Deps}
    (hp : ports = other) (hd : deps = otherDeps) (model : Component ports deps)
    (state : (transportComponent hp hd model).State) (state' : model.State)
    (input : PortValues other .input) (input' : PortValues ports .input)
    (states : HEq state state') (inputs : HEq input input') :
    HEq ((transportComponent hp hd model).out state input) (model.out state' input') := by
  cases hp
  cases hd
  cases states
  cases inputs
  rfl

private theorem transportComponent_next {ports other : List Port} {deps otherDeps : Deps}
    (hp : ports = other) (hd : deps = otherDeps) (model : Component ports deps)
    (state : (transportComponent hp hd model).State) (state' : model.State)
    (input : PortValues other .input) (input' : PortValues ports .input)
    (states : HEq state state') (inputs : HEq input input') :
    HEq ((transportComponent hp hd model).next state input) (model.next state' input') := by
  cases hp
  cases hd
  cases states
  cases inputs
  rfl

def moduleChild (d : Typed.Design) (wf : WellFormed d.erase)
    (m c : Typed.Module) (hm : m ∈ d.bodies) (hc : c ∈ d.bodies)
    (child : String) (name : c.name = child)
    (model : Component c.ports (Deps.infer c.erase c.children)) :
    Component (m.interfaces child) ((m.children child).getD []) :=
  transportComponent (by
    rw [(d.environments m hm).1, ← name]
    exact (portsOf_item d.erase wf.1.1.1 (.module c.erase)
      (d.environments c hc).2.2).symm) (by
    rw [(d.environments m hm).2.1, ← name]
    change Deps.infer c.erase c.children =
      ((designDeps d.erase (d.erase.items.length + 1) c.name).getD [])
    rw [d.dependencies wf c hc]
    rfl) model

@[simp] theorem moduleChild_state (d : Typed.Design) (wf : WellFormed d.erase)
    (m c : Typed.Module) (hm : m ∈ d.bodies) (hc : c ∈ d.bodies)
    (child : String) (name : c.name = child)
    (model : Component c.ports (Deps.infer c.erase c.children)) :
    (moduleChild d wf m c hm hc child name model).State = model.State :=
  transportComponent_state _ _ model

theorem moduleChild_out (d : Typed.Design) (wf : WellFormed d.erase)
    (m c : Typed.Module) (hm : m ∈ d.bodies) (hc : c ∈ d.bodies)
    (child : String) (name : c.name = child)
    (model : Component c.ports (Deps.infer c.erase c.children))
    (state : (moduleChild d wf m c hm hc child name model).State) (state' : model.State)
    (input : PortValues (m.interfaces child) .input) (input' : Input c)
    (states : HEq state state') (inputs : HEq input input') :
    HEq ((moduleChild d wf m c hm hc child name model).out state input)
      (model.out state' input') :=
  transportComponent_out _ _ model state state' input input' states inputs

theorem moduleChild_next (d : Typed.Design) (wf : WellFormed d.erase)
    (m c : Typed.Module) (hm : m ∈ d.bodies) (hc : c ∈ d.bodies)
    (child : String) (name : c.name = child)
    (model : Component c.ports (Deps.infer c.erase c.children))
    (state : (moduleChild d wf m c hm hc child name model).State) (state' : model.State)
    (input : PortValues (m.interfaces child) .input) (input' : Input c)
    (states : HEq state state') (inputs : HEq input input') :
    HEq ((moduleChild d wf m c hm hc child name model).next state input)
      (model.next state' input') :=
  transportComponent_next _ _ model state state' input input' states inputs

def externChild (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (e : Extern)
    (he : Item.extern e ∈ d.erase.items) (child : String) (name : e.name = child)
    (model : ExternSem e) :
    Component (m.interfaces child) ((m.children child).getD []) :=
  transportComponent (by
    rw [(d.environments m hm).1, ← name]
    exact (portsOf_item d.erase wf.1.1.1 (.extern e) he).symm) (by
    rw [(d.environments m hm).2.1, ← name]
    change externDeps e = ((designDeps d.erase (d.erase.items.length + 1) e.name).getD [])
    rw [designDeps_extern d.erase wf.1.1.1 e he d.erase.items.length]
    rfl) model

@[simp] theorem externChild_state (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (e : Extern)
    (he : Item.extern e ∈ d.erase.items) (child : String) (name : e.name = child)
    (model : ExternSem e) :
    (externChild d wf m hm e he child name model).State = model.State :=
  transportComponent_state _ _ model

/-! Recursion follows the computed module positions, with externs at the leaves. -/
def assembleChildren (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) (m : Typed.Module) (hm : m ∈ d.bodies) :
    Children m := fun ⟨equation, member⟩ => by
  cases equation with
  | inst index pos inst child inputs =>
    have stmt := instance_member m index pos inst child inputs member
    have resolved := (wf.2.1.2 m.erase (module_mem d m hm) _ stmt).1
    have existsItem : ∃ item ∈ d.erase.items, itemName item = child := by
      obtain ⟨item, found, _⟩ := resolved
      exact ⟨item, List.mem_of_find?_eq_some found, by
        simpa [Rules.findItem] using List.find?_some found⟩
    exact match found : d.bodies.find? (·.name == child) with
    | some c => by
      have hc := List.mem_of_find?_eq_some found
      have name : c.name = child := by simpa using List.find?_some found
      exact moduleChild d wf m c hm hc child name
        (build c hc (assembleChildren d wf env build c hc))
    | none => by
      have existsExtern := external_exists d child existsItem found
      let e := (d.externs.find? (·.name == child)).get (by
        obtain ⟨e, he, _⟩ := existsExtern; simp [he])
      have selected : d.externs.find? (·.name == child) = some e := (Option.some_get _).symm
      have he : Item.extern e ∈ d.erase.items := by
        obtain ⟨other, selectedOther, member⟩ := existsExtern
        rw [selected] at selectedOther
        exact Option.some.inj selectedOther ▸ member
      exact externChild d wf m hm e he child
        (by simpa using List.find?_some selected)
        (env e (List.mem_of_find?_eq_some selected))
  | _ => exact PUnit.unit
termination_by moduleLevel d.erase wf m.name
decreasing_by
  have childMem : child ∈ Typed.childNames m.erase :=
    List.mem_filterMap.mpr ⟨_, stmt, rfl⟩
  simpa only [name, Typed.Module.erase] using
    moduleLevel_lower d.erase wf m.erase (module_mem d m hm) child childMem

/-! These equations expose each child without the recursion proof. -/
theorem assembleChildren_inst_module (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) (m : Typed.Module) (hm : m ∈ d.bodies)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body)
    (c : Typed.Module) (found : d.bodies.find? (·.name == child) = some c) :
    assembleChildren d wf env build m hm ⟨.inst index pos inst child inputs, member⟩ =
      moduleChild d wf m c hm (List.mem_of_find?_eq_some found) child
        (by simpa using List.find?_some found)
        (build c (List.mem_of_find?_eq_some found)
          (assembleChildren d wf env build c (List.mem_of_find?_eq_some found))) := by
  rw [assembleChildren]
  dsimp only
  change @Eq (Component (m.interfaces child) ((m.children child).getD [])) _ _
  split
  · rename_i other selected
    have same := Option.some.inj (selected.symm.trans found)
    subst other
    rfl
  · rename_i selected
    rw [found] at selected
    contradiction

theorem assembleChildren_inst_extern (d : Typed.Design) (wf : WellFormed d.erase)
    (env : Env d) (build : LocalBuilder d) (m : Typed.Module) (hm : m ∈ d.bodies)
    (index : Nat) (pos : Pos) (inst child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos inst child inputs ∈ m.body)
    (absent : d.bodies.find? (·.name == child) = none)
    (e : Extern) (found : d.externs.find? (·.name == child) = some e)
    (he : Item.extern e ∈ d.erase.items) :
    assembleChildren d wf env build m hm ⟨.inst index pos inst child inputs, member⟩ =
      externChild d wf m hm e he child (by simpa using List.find?_some found)
        (env e (List.mem_of_find?_eq_some found)) := by
  rw [assembleChildren]
  dsimp only
  split
  · rename_i other selected
    rw [absent] at selected
    contradiction
  · have congruent (other : Extern) (ho : Item.extern other ∈ d.erase.items)
        (hn : other.name = child) (hm : other ∈ d.externs) (eq : other = e) :
        externChild d wf m ‹m ∈ d.bodies› other ho child hn (env other hm) =
          externChild d wf m ‹m ∈ d.bodies› e he child
            (by simpa using List.find?_some found)
            (env e (List.mem_of_find?_eq_some found)) := by
      subst other
      rfl
    exact congruent _ _ _ _ (by simp [found])

end Silicon.Core.Semantics
