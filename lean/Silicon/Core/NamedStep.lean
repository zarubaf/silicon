import Silicon.Core.Semantics.NamedConnections
import Silicon.Core.Semantics.NamedNext

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
    (related : ItemReorder (.module m.erase) (.module m'.erase))
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
    (related : ItemReorder (.module m.erase) (.module m'.erase))
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
    (related : ItemReorder (.module m.erase) (.module m'.erase))
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
  constructor
  · exact outputValues_named_heq d d' m m' hm hm' ports _ _ sameValues
  · have next := namedNextState_reorder d d' env env' noExterns noExterns' order m m' hm hm'
      related state state' same values instances.2
    have leftEq : nextFromValues d env m hm state values =
        (Interp.step d env m hm state input).1 := by
      simp only [nextFromValues, values, Valuation.named_valuation, Interp.step]
    have rightEq : nextFromValues d' env' m' hm' state' values =
        (Interp.step d' env' m' hm' state' input').1 := by
      rw [sameValues]
      simp only [nextFromValues, Valuation.named_valuation, Interp.step]
    rw [leftEq, rightEq] at next
    exact next

theorem namedStep_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder (.module m.erase) (.module m'.erase)) :
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
