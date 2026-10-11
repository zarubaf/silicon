-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Canonical.Local

/-! Child component transport preserves the child's step and its port values. -/
namespace Silicon.Core.Semantics

private theorem Component.out_heq_of_eq {ports : List Port} {deps : Deps}
    (a b : Component ports deps) (models : a = b) (state : a.State) (state' : b.State)
    (states : HEq state state') (input : PortValues ports .input) :
    HEq (a.out state input) (b.out state' input) := by
  cases models
  cases states
  rfl

private theorem Component.next_heq_of_eq {ports : List Port} {deps : Deps}
    (a b : Component ports deps) (models : a = b) (state : a.State) (state' : b.State)
    (states : HEq state state') (input : PortValues ports .input) :
    HEq (a.next state input) (b.next state' input) := by
  cases models
  cases states
  rfl

theorem child_ports (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (c : Typed.Module) (child : String)
    (found : d.design.bodies.find? (·.name == child) = some c) :
    m.interfaces child = c.ports := by
  have name : c.name = child := by simpa using List.find?_some found
  rw [(d.design.environments m hm).1, ← name]
  exact portsOf_item d.design.erase d.wellFormed.1.1.1 (.module c.erase)
    (d.design.environments c (List.mem_of_find?_eq_some found)).2.2

theorem designChildren_instance_out (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (found : d.design.bodies.find? (·.name == child) = some c)
    (state : State d env m hm) (childState : State d env c (List.mem_of_find?_eq_some found))
    (states : HEq (state ⟨.inst i p name child inputs, member⟩) childState)
    (input : PortValues (m.interfaces child) .input) (childInput : Input c)
    (sameInput : HEq input childInput) :
    HEq ((designChildren d env m hm ⟨.inst i p name child inputs, member⟩).out
      (state ⟨.inst i p name child inputs, member⟩) input)
      (Interp.step d env c (List.mem_of_find?_eq_some found) childState childInput).2 := by
  rw [interp_step]
  let eq := designChildren_inst_module d env m hm i p name child inputs member c found
  let model := localComponent d c (List.mem_of_find?_eq_some found)
    (designChildren d env c (List.mem_of_find?_eq_some found))
  let transported := moduleChild d.design d.wellFormed m c hm
    (List.mem_of_find?_eq_some found) child (by simpa using List.find?_some found) model
  let intermediate : transported.State := cast (congrArg Component.State eq)
    (state ⟨.inst i p name child inputs, member⟩)
  have middle : HEq intermediate childState := (cast_heq _ _).trans states
  exact (Component.out_heq_of_eq _ _ eq _ intermediate (cast_heq _ _).symm input).trans
    (moduleChild_out d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found) child
      (by simpa using List.find?_some found) model intermediate childState input childInput
      middle sameInput)

theorem designChildren_instance_next (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (found : d.design.bodies.find? (·.name == child) = some c)
    (state : State d env m hm) (childState : State d env c (List.mem_of_find?_eq_some found))
    (states : HEq (state ⟨.inst i p name child inputs, member⟩) childState)
    (input : PortValues (m.interfaces child) .input) (childInput : Input c)
    (sameInput : HEq input childInput) :
    HEq ((designChildren d env m hm ⟨.inst i p name child inputs, member⟩).next
      (state ⟨.inst i p name child inputs, member⟩) input)
      (Interp.step d env c (List.mem_of_find?_eq_some found) childState childInput).1 := by
  rw [interp_step]
  let eq := designChildren_inst_module d env m hm i p name child inputs member c found
  let model := localComponent d c (List.mem_of_find?_eq_some found)
    (designChildren d env c (List.mem_of_find?_eq_some found))
  let transported := moduleChild d.design d.wellFormed m c hm
    (List.mem_of_find?_eq_some found) child (by simpa using List.find?_some found) model
  let intermediate : transported.State := cast (congrArg Component.State eq)
    (state ⟨.inst i p name child inputs, member⟩)
  have middle : HEq intermediate childState := (cast_heq _ _).trans states
  exact (Component.next_heq_of_eq _ _ eq _ intermediate (cast_heq _ _).symm input).trans
    (moduleChild_next d.design d.wellFormed m c hm (List.mem_of_find?_eq_some found) child
      (by simpa using List.find?_some found) model intermediate childState input childInput
      middle sameInput)

end Silicon.Core.Semantics

/-! A permutation preserves the one expression connected to each input port. -/
namespace Silicon.Core.Semantics

private theorem lookup_perm_single (xs ys : List (String × α)) (perm : xs.Perm ys)
    (name : String) (one : (xs.filter (fun x => x.1 == name)).length = 1)
    (a b : α) (ha : xs.lookup name = some a) (hb : ys.lookup name = some b) : a = b := by
  have member (zs : List (String × α)) (v : α) (h : zs.lookup name = some v) :
      (name, v) ∈ zs := by
    obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp h
    simp
  have ma : (name, a) ∈ xs.filter (fun x => x.1 == name) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]
    exact member xs a ha
  have mb : (name, b) ∈ xs.filter (fun x => x.1 == name) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]
    exact perm.mem_iff.mpr (member ys b hb)
  obtain ⟨entry, h⟩ := List.length_eq_one_iff.mp one
  rw [h] at ma mb
  exact congrArg Prod.snd ((List.eq_of_mem_singleton ma).trans
    (List.eq_of_mem_singleton mb).symm)

theorem connectionExpr_erase_reorder (d d' : CertifiedDesign)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (i i' : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    (member' : .inst i' p name child inputs' ∈ m'.body)
    (perm : (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)))
    (port : Port) (hp : port ∈ m.interfaces child) (hp' : port ∈ m'.interfaces child)
    (dir : port.dir = .input) :
    (connectionExpr d m hm i p name child inputs member ⟨port, hp, dir⟩).erase =
      (connectionExpr d' m' hm' i' p name child inputs' member' ⟨port, hp', dir⟩).erase := by
  apply lookup_perm_single _ _ perm port.name
    (by simpa only [List.filter_map, List.length_map, Function.comp_def] using
      typed_input_count d m hm i p name child inputs member ⟨port, hp, dir⟩)
  · exact connectionExpr_lookup d m hm i p name child inputs member ⟨port, hp, dir⟩
  · exact connectionExpr_lookup d' m' hm' i' p name child inputs' member' ⟨port, hp', dir⟩

theorem connectionValues_reorder (d d' : CertifiedDesign)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (lookup : ∀ node, m.ctx.lookup node = m'.ctx.lookup node)
    (values : NamedValues) (memories : NamedMemories)
    (i i' : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    (member' : .inst i' p name child inputs' ∈ m'.body)
    (perm : (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)))
    (port : Port) (hp : port ∈ m.interfaces child) (hp' : port ∈ m'.interfaces child)
    (dir : port.dir = .input) :
    connectionValues d m hm (values.valuation m.ctx) (memories.typed m.ctx)
      ⟨.inst i p name child inputs, member⟩ ⟨port, hp, dir⟩ =
    connectionValues d' m' hm' (values.valuation m'.ctx) (memories.typed m'.ctx)
      ⟨.inst i' p name child inputs', member'⟩ ⟨port, hp', dir⟩ := by
  apply evalExpr_erase_eq lookup
  exact connectionExpr_erase_reorder d d' m m' hm hm' i i' p name child inputs inputs'
    member member' perm port hp hp' dir

theorem portValues_heq {ports ports' : List Port} {dir : PortDir}
    (same : ports = ports') (a : PortValues ports dir) (b : PortValues ports' dir)
    (agree : ∀ p hp hp' hd, a ⟨p, hp, hd⟩ = b ⟨p, hp', hd⟩) : HEq a b := by
  subst ports'
  apply heq_of_eq
  funext p
  exact agree p.val p.property.1 p.property.1 p.property.2

theorem portValues_eq_of_heq {ports ports' : List Port} {dir : PortDir}
    (same : ports = ports') (a : PortValues ports dir) (b : PortValues ports' dir)
    (agree : HEq a b) (p : Port) (hp : p ∈ ports) (hp' : p ∈ ports') (hd : p.dir = dir) :
    a ⟨p, hp, hd⟩ = b ⟨p, hp', hd⟩ := by
  subst ports'
  cases agree
  rfl

end Silicon.Core.Semantics

/-! A module simulation compares named state and port values for one cycle. -/
namespace Silicon.Core

open Semantics

def NamedStepSimulation (d d' : CertifiedDesign) (env : Env d.design) (env' : Env d'.design)
    (noExterns : d.design.externs = []) (noExterns' : d'.design.externs = [])
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies) : Prop :=
  ∀ (state : State d env m hm) (state' : State d' env' m' hm'),
    namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state' →
    ∀ (input : Input m) (input' : Input m'), HEq input input' →
    HEq (Interp.step d env m hm state input).2 (Interp.step d' env' m' hm' state' input').2 ∧
      namedState d env noExterns m hm (Interp.step d env m hm state input).1 =
        namedState d' env' noExterns' m' hm' (Interp.step d' env' m' hm' state' input').1

private theorem instance_step_of_simulation (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (simulate : ∀ child ∈ Typed.childNames m.erase, ∀ c c'
      (found : d.design.bodies.find? (·.name == child) = some c)
      (found' : d'.design.bodies.find? (·.name == child) = some c'),
      NamedStepSimulation d d' env env' noExterns noExterns' c c'
        (List.mem_of_find?_eq_some found) (List.mem_of_find?_eq_some found'))
    (values : NamedValues)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    (i' : Nat) (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member' : .inst i' p name child inputs' ∈ m'.body)
    (perm : (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase))) :
    (let e : EquationRef m := ⟨.inst i p name child inputs, member⟩
     let e' : EquationRef m' := ⟨.inst i' p name child inputs', member'⟩
     HEq ((designChildren d env m hm e).out (state e)
       (connectionValues d m hm (values.valuation m.ctx)
         (stateMemories m (designChildren d env m hm) state) e))
       ((designChildren d' env' m' hm' e').out (state' e')
         (connectionValues d' m' hm' (values.valuation m'.ctx)
           (stateMemories m' (designChildren d' env' m' hm') state') e'))) ∧
    ∀ path, namedState d env noExterns m hm (nextFromValues d env m hm state values)
      (name :: path) = namedState d' env' noExterns' m' hm'
        (nextFromValues d' env' m' hm' state' values) (name :: path) := by
  obtain ⟨c, found⟩ := instance_child_exists d noExterns m hm i p name child inputs member
  obtain ⟨c', found'⟩ := instance_child_exists d' noExterns' m' hm' i' p name child inputs' member'
  let a := cast (State_inst_module d env m hm i p name child inputs member c found)
    (state ⟨.inst i p name child inputs, member⟩)
  let b := cast (State_inst_module d' env' m' hm' i' p name child inputs' member' c' found')
    (state' ⟨.inst i' p name child inputs', member'⟩)
  have states : namedState d env noExterns c (List.mem_of_find?_eq_some found) a =
      namedState d' env' noExterns' c' (List.mem_of_find?_eq_some found') b := by
    funext path
    have eq := congrFun same (name :: path)
    rw [namedState_instance d env noExterns m hm state i p name child inputs member c found,
      namedState_instance d' env' noExterns' m' hm' state' i' p name child inputs' member'
        c' found'] at eq
    exact eq
  let parentInput := connectionValues d m hm (values.valuation m.ctx)
    (stateMemories m (designChildren d env m hm) state) ⟨.inst i p name child inputs, member⟩
  let parentInput' := connectionValues d' m' hm' (values.valuation m'.ctx)
    (stateMemories m' (designChildren d' env' m' hm') state')
      ⟨.inst i' p name child inputs', member'⟩
  have ports := child_ports d m hm c child found
  have ports' := child_ports d' m' hm' c' child found'
  let input : Input c := cast (congrArg (fun ps => PortValues ps .input) ports) parentInput
  let input' : Input c' := cast (congrArg (fun ps => PortValues ps .input) ports') parentInput'
  have interfaces := congrFun (order.typed_interfaces m m' hm hm') child
  have samePorts : c.ports = c'.ports := ports.symm.trans (interfaces.trans ports')
  have parentEq : HEq parentInput parentInput' := by
    apply portValues_heq interfaces
    intro port hp hp' dir
    have lookup := order.typed_context m m' hm hm' related
    have memories := stateMemories_named_eq d d' env env' noExterns noExterns' m m' hm hm'
      state state' lookup same
    have eq := connectionValues_reorder d d' m m' hm hm' lookup values
      (stateMemories m (designChildren d env m hm) state).named
      i i' p name child inputs inputs' member member' perm port hp hp' dir
    rw [Memories.named_typed, memories, Memories.named_typed] at eq
    exact eq
  have inputEq : HEq input input' := (cast_heq _ _).trans (parentEq.trans (cast_heq _ _).symm)
  have childMember : child ∈ Typed.childNames m.erase :=
    List.mem_filterMap.mpr ⟨_, instance_member m i p name child inputs member, rfl⟩
  have results := simulate child childMember c c' found found' a b states input input' inputEq
  constructor
  · have left := designChildren_instance_out d env m hm i p name child inputs member c found
      state a (cast_heq _ _).symm parentInput input (cast_heq _ _).symm
    have right := designChildren_instance_out d' env' m' hm' i' p name child inputs' member'
      c' found' state' b (cast_heq _ _).symm parentInput' input' (cast_heq _ _).symm
    exact left.trans (results.1.trans right.symm)
  · intro path
    rw [namedState_instance d env noExterns m hm _ i p name child inputs member c found,
      namedState_instance d' env' noExterns' m' hm' _ i' p name child inputs' member' c' found']
    have left := designChildren_instance_next d env m hm i p name child inputs member c found
      state a (cast_heq _ _).symm parentInput input (cast_heq _ _).symm
    have right := designChildren_instance_next d' env' m' hm' i' p name child inputs' member'
      c' found' state' b (cast_heq _ _).symm parentInput' input' (cast_heq _ _).symm
    have leftEq := eq_of_heq ((cast_heq (State_inst_module d env m hm i p name child inputs
      member c found) ((nextFromValues d env m hm state values)
        ⟨.inst i p name child inputs, member⟩)).trans left)
    have rightEq := eq_of_heq ((cast_heq (State_inst_module d' env' m' hm' i' p name child inputs'
      member' c' found') ((nextFromValues d' env' m' hm' state' values)
        ⟨.inst i' p name child inputs', member'⟩)).trans right)
    rw [leftEq, rightEq]
    exact congrFun results.2 path

theorem instances_of_simulation (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (simulate : ∀ child ∈ Typed.childNames m.erase, ∀ c c'
      (found : d.design.bodies.find? (·.name == child) = some c)
      (found' : d'.design.bodies.find? (·.name == child) = some c'),
      NamedStepSimulation d d' env env' noExterns noExterns' c c'
        (List.mem_of_find?_eq_some found) (List.mem_of_find?_eq_some found'))
    (values : NamedValues) :
    InstanceOutputsAgree d d' env env' m m' hm hm' state state' values ∧
      InstanceNextAgree d d' env env' noExterns noExterns' m m' hm hm' state state' values := by
  have each := instance_step_of_simulation d d' env env' noExterns noExterns' order m m' hm hm'
    related state state' same simulate values
  constructor
  · intro i p name child inputs member i' inputs' member' perm port hp hp' dir
    exact portValues_eq_of_heq (congrFun (order.typed_interfaces m m' hm hm') child) _ _
      (each i p name child inputs member i' inputs' member' perm).1 port hp hp' dir
  · intro i p name child inputs member i' inputs' member' perm path
    exact (each i p name child inputs member i' inputs' member' perm).2 path

theorem outputValues_named_heq (d d' : CertifiedDesign) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies) (ports : m.ports = m'.ports)
    (values : Valuation m.ctx) (values' : Valuation m'.ctx) (same : values.named = values'.named) :
    HEq (Semantics.outputValues d m hm values) (Semantics.outputValues d' m' hm' values') := by
  apply portValues_heq ports
  intro port hp hp' dir
  rcases port with ⟨pos, direction, name, ty⟩
  cases ty with
  | clock => rfl
  | bits width =>
    have found := port_found d.design d.wellFormed m hm _ hp (width := width) rfl
    have found' := port_found d'.design d'.wellFormed m' hm' _ hp' (width := width) rfl
    have eq := congrFun same (.name name)
    rw [Valuation.named_at _ _ width found, Valuation.named_at _ _ width found'] at eq
    exact BitVec.eq_of_toNat_eq eq

theorem namedStep_of_children (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (simulate : ∀ child ∈ Typed.childNames m.erase, ∀ c c'
      (found : d.design.bodies.find? (·.name == child) = some c)
      (found' : d'.design.bodies.find? (·.name == child) = some c'),
      NamedStepSimulation d d' env env' noExterns noExterns' c c'
        (List.mem_of_find?_eq_some found) (List.mem_of_find?_eq_some found')) :
    NamedStepSimulation d d' env env' noExterns noExterns' m m' hm hm' := by
  intro state state' same input input' inputs
  have ports : m.ports = m'.ports := related.ports
  let values := (Interp.solve d env m hm state input).named
  have solved := IsSolution.named d env m hm state input _ (interp_correct d env m hm state input)
  have instances := instances_of_simulation d d' env env' noExterns noExterns' order m m' hm hm'
    related state state' same simulate values
  have transported := named_solution_reorder d d' env env' noExterns noExterns' order m m' hm hm'
    related state state' same input input'
    (portValues_eq_of_heq ports input input' inputs) values solved instances.1
  obtain ⟨canonical, _, unique⟩ := named_solution_unique d' env' m' hm' state' input'
  have sameValues : values = (Interp.solve d' env' m' hm' state' input').named :=
    (unique values transported).trans (unique _
      (IsSolution.named d' env' m' hm' state' input' _
        (interp_correct d' env' m' hm' state' input'))).symm
  simp only [Interp.step_eq_values]
  constructor
  · exact outputValues_named_heq d d' m m' hm hm' ports _ _ sameValues
  · have next := namedNextState_reorder d d' env env' noExterns noExterns' order m m' hm hm'
      related state state' same values instances.2
    have leftEq : nextFromValues d env m hm state values =
        (Interp.step d env m hm state input).1 := by
      simp only [nextFromValues, values, Valuation.named_valuation, Interp.step_eq_values,
        stepWithValues, localStepWithValues]
    have rightEq : nextFromValues d' env' m' hm' state' values =
        (Interp.step d' env' m' hm' state' input').1 := by
      rw [sameValues]
      simp only [nextFromValues, Valuation.named_valuation, Interp.step_eq_values,
        stepWithValues, localStepWithValues]
    rw [leftEq, rightEq] at next
    simpa only [Interp.step_eq_values] using next

theorem namedStep_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase)) :
    NamedStepSimulation d d' env env' noExterns noExterns' m m' hm hm' := by
  apply namedStep_of_children d d' env env' noExterns noExterns' order m m' hm hm' related
  intro child member c c' found found'
  have name : c.name = child := by simpa using List.find?_some found
  obtain ⟨other, otherFound, childRelated⟩ :=
    order.typed_module c (List.mem_of_find?_eq_some found)
  rw [name, found'] at otherFound
  cases otherFound
  exact namedStep_reorder d d' env env' noExterns noExterns' order c c'
    (List.mem_of_find?_eq_some found) (List.mem_of_find?_eq_some found') childRelated
termination_by moduleLevel d.design.erase d.wellFormed m.name
decreasing_by
  simpa only [name, Typed.Module.erase] using
    moduleLevel_lower d.design.erase d.wellFormed m.erase (module_mem d.design m hm) child member

end Silicon.Core
