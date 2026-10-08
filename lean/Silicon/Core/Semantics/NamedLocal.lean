import Silicon.Core.NamedReorder
import Silicon.Core.Semantics.NamedUpdate

/-! Local named solutions share inputs, state cells, and child outputs. -/
namespace Silicon.Core.Semantics

theorem stateMemories_named_eq (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (state : State d env m hm) (state' : State d' env' m' hm')
    (lookup : ∀ node, m.ctx.lookup node = m'.ctx.lookup node)
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state') :
    (stateMemories m (designChildren d env m hm) state).named =
      (stateMemories m' (designChildren d' env' m' hm') state').named := by
  funext name address
  cases found : m.ctx.lookup (.name name) with
  | none => simp [Memories.named, found, ← lookup]
  | some kind =>
    cases kind with
    | value | clock => simp [Memories.named, found, ← lookup]
    | memory width depth =>
      have found' := (lookup (.name name)).symm.trans found
      have equal := stateMemories_eq_of_named d d' env env' noExterns noExterns' m m' hm hm'
        state state' (fun path => congrFun same path) name width depth found found'
      by_cases bound : address < depth
      · rw [Memories.named_at _ name width depth found ⟨address, bound⟩,
          Memories.named_at _ name width depth found' ⟨address, bound⟩]
        exact congrArg (fun memory => (memory ⟨address, bound⟩).toNat) equal
      · have absent (ctx : Typed.Ctx) (mem : Memories ctx)
            (hf : ctx.lookup (.name name) = some (.memory width depth)) :
            mem.named name address = 0 := by
          unfold Memories.named
          split
          · rename_i w size hs
            have eq : width = w ∧ depth = size := by simpa [hf] using hs
            rcases eq with ⟨rfl, rfl⟩
            simp [bound]
          · rfl
        rw [absent _ _ found, absent _ _ found']

/-! A child output is compared at the same port, with its parent's candidate values. -/
def InstanceOutputsAgree (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (m m' : Typed.Module) (hm : m ∈ d.design.bodies)
    (hm' : m' ∈ d'.design.bodies) (state : State d env m hm) (state' : State d' env' m' hm')
    (values : NamedValues) : Prop :=
  ∀ i p name child (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    i' (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member' : .inst i' p name child inputs' ∈ m'.body),
    (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)) →
    ∀ port (hp : port ∈ m.interfaces child) (hp' : port ∈ m'.interfaces child)
      (dir : port.dir = .output),
    let e : EquationRef m := ⟨.inst i p name child inputs, member⟩
    let e' : EquationRef m' := ⟨.inst i' p name child inputs', member'⟩
    (designChildren d env m hm e).out (state e)
      (connectionValues d m hm (values.valuation m.ctx)
        (stateMemories m (designChildren d env m hm) state) e) ⟨port, hp, dir⟩ =
    (designChildren d' env' m' hm' e').out (state' e')
      (connectionValues d' m' hm' (values.valuation m'.ctx)
        (stateMemories m' (designChildren d' env' m' hm') state') e') ⟨port, hp', dir⟩

theorem named_solution_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (input : Input m) (input' : Input m')
    (inputEq : ∀ port hp hp' dir, input ⟨port, hp, dir⟩ = input' ⟨port, hp', dir⟩)
    (values : NamedValues) (solved : IsNamedSolution d env m hm state input values)
    (children : InstanceOutputsAgree d d' env env' m m' hm hm' state state' values) :
    IsNamedSolution d' env' m' hm' state' input' values := by
  have lookup := order.typed_context m m' hm hm' related
  have interfaces := order.typed_interfaces m m' hm hm'
  have memories := stateMemories_named_eq d d' env env' noExterns noExterns' m m' hm hm'
    state state' lookup same
  cases related with
  | module _ _ _ _ ports body =>
    have portEq : m'.ports = m.ports := ports
    refine ⟨?_, ?_⟩
    · intro node
      rw [← lookup]
      exact solved.1 node
    · intro node width found driver
      cases driver with
      | input port hp dir bits =>
        have hpLeft : port ∈ m.ports := portEq ▸ hp
        have eq := named_solution_input d env m hm state input values solved port hpLeft dir bits
        change BitVec.ofNat width (values (.name port.name)) = _
        rw [eq, inputEq port hpLeft hp dir]
        simp [ValueDriver.eval]
      | let_ i p name width expr member =>
        have raw : Core.Stmt.let_ p name width expr.erase ∈ m'.erase.body :=
          (Ownership.mem_equationsErase m'.body _).mpr
            ⟨_, member, i, .let_ p name width expr, by simp [Typed.Equation.parts], rfl⟩
        obtain ⟨s, hs, rel⟩ := body.right raw
        cases rel
        have eq := named_solution_let d env m hm state input values solved p name width
          expr.erase hs ((lookup (.name name)).trans found)
        rw [evalNamedExpr_lookup_congr lookup, memories, evalNamedExpr_typed,
          Memories.named_typed] at eq
        have eq := congrArg (BitVec.ofNat width) (Option.some.inj eq)
        simpa [ValueDriver.eval, NamedValues.valuation] using eq.symm
      | assign i p name width target expr member =>
        have raw : Core.Stmt.assign p name expr.erase ∈ m'.erase.body :=
          (Ownership.mem_equationsErase m'.body _).mpr
            ⟨_, member, i, .assign p name width target expr,
              by simp [Typed.Equation.parts], rfl⟩
        obtain ⟨s, hs, rel⟩ := body.right raw
        cases rel
        have eq := named_solution_assign d env m hm state input values solved p name width
          expr.erase hs ((lookup (.name name)).trans found)
        rw [evalNamedExpr_lookup_congr lookup, memories, evalNamedExpr_typed,
          Memories.named_typed] at eq
        have eq := congrArg (BitVec.ofNat width) (Option.some.inj eq)
        simpa [ValueDriver.eval, NamedValues.valuation] using eq.symm
      | reg i p name width clock target reset ni np next member =>
        have raw : Core.Stmt.reg p name width clock (reset.map Typed.Reset.erase) ∈
            m'.erase.body := (Ownership.mem_equationsErase m'.body _).mpr
          ⟨_, member, i, .reg p name width clock reset, by simp [Typed.Equation.parts], rfl⟩
        obtain ⟨s, hs, rel⟩ := body.right raw
        cases rel
        have eq := named_solution_register d env noExterns m hm state input values solved
          p name width clock _ hs ((lookup (.name name)).trans found)
        rw [same, namedState_register d' env' noExterns' m' hm' state' i p name width clock
          target reset ni np next member] at eq
        exact (eq_of_heq (NamedCell.register.inj (Option.some.inj eq)).2).symm
      | inst i p name child inputs member port hp dir bits =>
        have raw := instance_member m' i p name child inputs member
        obtain ⟨s, hs, rel⟩ := body.right raw
        have matching : ∃ rawInputs, Core.Stmt.inst p name child rawInputs ∈ m.erase.body ∧
            rawInputs.Perm (inputs.map fun x => (x.1.val.name, x.2.erase)) := by
          cases rel with
          | same => exact ⟨_, hs, .refl _⟩
          | inst => exact ⟨_, hs, by assumption⟩
        obtain ⟨rawInputs, hs, perm⟩ := matching
        obtain ⟨j, ins, memberLeft, erased⟩ := Ownership.inst_equation m.body _ _ _ _ hs
        have hpLeft : port ∈ m.interfaces child := interfaces ▸ hp
        have eq := solved.2 (.port name port.name) width ((lookup _).trans found)
          (.inst j p name child ins memberLeft port hpLeft dir bits)
        have childEq := children j p name child ins memberLeft i inputs member
          (erased ▸ perm) port hpLeft hp dir
        exact eq.trans (congrArg (cast (congrArg TyValue bits)) childEq)

end Silicon.Core.Semantics
