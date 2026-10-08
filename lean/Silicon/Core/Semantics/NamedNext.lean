import Silicon.Core.Semantics.NamedRegisters
import Silicon.Core.Semantics.NamedWrites

/-! Named candidate values update each state cell through its erased equations. -/
namespace Silicon.Core.Semantics

def nextFromValues (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (values : NamedValues) : State d env m hm :=
  let memories := stateMemories m (designChildren d env m hm) state
  nextLocalState m (designChildren d env m hm) state (values.valuation m.ctx) memories
    (connectionValues d m hm (values.valuation m.ctx) memories)

def InstanceNextAgree (d d' : CertifiedDesign) (env : Env d.design) (env' : Env d'.design)
    (noExterns : d.design.externs = []) (noExterns' : d'.design.externs = [])
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (state : State d env m hm) (state' : State d' env' m' hm') (values : NamedValues) : Prop :=
  ∀ i p name child (inputs : List (Connection m.ctx (m.interfaces child)))
    (_member : .inst i p name child inputs ∈ m.body)
    i' (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (_member' : .inst i' p name child inputs' ∈ m'.body),
    (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)) →
    ∀ path, namedState d env noExterns m hm (nextFromValues d env m hm state values)
      (name :: path) = namedState d' env' noExterns' m' hm'
        (nextFromValues d' env' m' hm' state' values) (name :: path)

private theorem next_some_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (values : NamedValues)
    (children : InstanceNextAgree d d' env env' noExterns noExterns' m m' hm hm'
      state state' values)
    (path : List String) (cell : NamedCell)
    (value : namedState d env noExterns m hm (nextFromValues d env m hm state values) path =
      some cell) :
    namedState d' env' noExterns' m' hm' (nextFromValues d' env' m' hm' state' values) path =
      some cell := by
  have lookup := order.typed_context m m' hm hm' related
  have memories := stateMemories_named_eq d d' env env' noExterns noExterns' m m' hm hm'
    state state' lookup same
  cases related with
  | module _ _ _ _ _ body =>
    cases path with
    | nil => simp [namedState] at value
    | cons name path =>
      have original := value
      rw [namedState] at value
      split at value
      · contradiction
      · rename_i equation found
        have member := List.mem_of_find?_eq_some found
        have named : equationName equation = name := by simpa using List.find?_some found
        cases equation with
        | let_ | assign => contradiction
        | reg i p n width clock target reset ni np next =>
          change n = name at named
          subst n
          dsimp only at value
          split at value
          · rename_i empty
            have hp : path = [] := by simpa using empty
            subst path
            have raw : Core.Stmt.reg p name width clock (reset.map Typed.Reset.erase) ∈
                m.erase.body := (Ownership.mem_equationsErase m.body _).mpr
              ⟨_, member, i, .reg p name width clock reset,
                by simp [Typed.Equation.parts], rfl⟩
            obtain ⟨s, hs, rel⟩ := body.left raw
            cases rel
            obtain ⟨j, target', reset', nj, nq, next', member', resetEq⟩ :=
              Ownership.reg_equation m'.body _ _ _ _ _ hs
            have nextEq := next_erase_reorder d m m' hm body i j p p name width clock clock
              target target' reset reset' ni nj np nq next next' member member'
            have eq := nextRegister_erase_eq lookup values
              (stateMemories m (designChildren d env m hm) state).named
              reset reset' next next' resetEq.symm nextEq
            rw [Memories.named_typed, memories, Memories.named_typed] at eq
            rw [namedState_register d' env' noExterns' m' hm' _ j p name width clock target'
              reset' nj nq next' member']
            change some (.register width (nextRegister (values.valuation m'.ctx)
              (stateMemories m' (designChildren d' env' m' hm') state') reset' next')) = some cell
            rw [← eq]
            exact value
          · contradiction
        | mem i p n width depth clock target writes =>
          change n = name at named
          subst n
          dsimp only at value
          split at value
          · rename_i empty
            have hp : path = [] := by simpa using empty
            subst path
            have raw : Core.Stmt.mem p name width depth clock ∈ m.erase.body :=
              (Ownership.mem_equationsErase m.body _).mpr
                ⟨_, member, i, .mem p name width depth clock,
                  by simp [Typed.Equation.parts], rfl⟩
            obtain ⟨s, hs, rel⟩ := body.left raw
            cases rel
            obtain ⟨j, target', writes', member'⟩ := Ownership.mem_equation m'.body _ _ _ _ _ hs
            have writesPerm := writeSyntax_perm d d' m m' hm hm' body i j p p name width depth
              clock clock target target' writes writes' member member'
            have evaluated := evalWrites_perm lookup values
              (stateMemories m (designChildren d env m hm) state).named name
              writes writes' writesPerm
            rw [Memories.named_typed, memories, Memories.named_typed] at evaluated
            have cells := congrFun same [name]
            rw [namedState_memory d env noExterns m hm state i p name width depth clock
              target writes member, namedState_memory d' env' noExterns' m' hm' state' j p
              name width depth clock target' writes' member'] at cells
            have cellsEq := eq_of_heq (NamedCell.memory.inj (Option.some.inj cells)).2.2
            have eq := nextMemory_eq_of_evaluated (values.valuation m.ctx)
              (values.valuation m'.ctx) (stateMemories m (designChildren d env m hm) state)
              (stateMemories m' (designChildren d' env' m' hm') state')
              (state ⟨.mem i p name width depth clock target writes, member⟩) writes writes'
              (typed_write_ports_nodup d m hm i p name width depth clock target writes member)
              evaluated
            rw [cellsEq] at eq
            rw [namedState_memory d' env' noExterns' m' hm' _ j p name width depth clock
              target' writes' member']
            change some (.memory width depth (nextMemory (values.valuation m'.ctx)
              (stateMemories m' (designChildren d' env' m' hm') state')
              (state' ⟨.mem j p name width depth clock target' writes', member'⟩) writes')) =
                some cell
            rw [← eq, ← cellsEq]
            exact value
          · contradiction
        | inst i p n child inputs =>
          change n = name at named
          subst n
          have raw := instance_member m i p name child inputs member
          obtain ⟨s, hs, rel⟩ := body.left raw
          have matching : ∃ rawInputs, Core.Stmt.inst p name child rawInputs ∈ m'.erase.body ∧
              (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm rawInputs := by
            cases rel with
            | same => exact ⟨_, hs, .refl _⟩
            | inst => exact ⟨_, hs, by assumption⟩
          obtain ⟨rawInputs, hs, perm⟩ := matching
          obtain ⟨j, ins, member', erased⟩ := Ownership.inst_equation m'.body _ _ _ _ hs
          exact (children i p name child inputs member j ins member' (erased ▸ perm)
            path).symm.trans original

theorem namedNextState_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (values : NamedValues)
    (children : InstanceNextAgree d d' env env' noExterns noExterns' m m' hm hm'
      state state' values) :
    namedState d env noExterns m hm (nextFromValues d env m hm state values) =
      namedState d' env' noExterns' m' hm' (nextFromValues d' env' m' hm' state' values) := by
  funext path
  apply Option.ext
  intro cell
  constructor
  · exact next_some_reorder d d' env env' noExterns noExterns' order m m' hm hm' related
      state state' same values children path cell
  · apply next_some_reorder d' d env' env noExterns' noExterns order.symm m' m hm' hm related.symm
      state' state same.symm values
    intro i p name child inputs member i' inputs' member' perm path
    exact (children i' p name child inputs' member' i inputs member perm.symm path).symm

end Silicon.Core.Semantics
