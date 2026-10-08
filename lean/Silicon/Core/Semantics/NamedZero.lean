import Silicon.Core.Semantics.NamedState
import Silicon.Core.Canonicalize

/-! Zero state follows register and memory declarations through named instance paths. -/
namespace Silicon.Core.Semantics

inductive ZeroPath (d : Core.Design) : Core.Module → List String → NamedCell → Prop where
  | reg (member : Core.Stmt.reg pos name width clock reset ∈ m.body) :
      ZeroPath d m [name] (.register width 0)
  | mem (member : Core.Stmt.mem pos name width depth clock ∈ m.body) :
      ZeroPath d m [name] (.memory width depth (fun _ => 0))
  | inst (member : Core.Stmt.inst pos name child inputs ∈ m.body)
      (childMember : Core.Item.module c ∈ d.items) (childName : c.name = child)
      (next : ZeroPath d c path cell) : ZeroPath d m (name :: path) cell

theorem ZeroPath.reorder {d d' : Core.Design} (order : Reorder d d')
    {m m' : Core.Module} (body : Permuted StmtReorder m.body m'.body)
    {path : List String} {cell : NamedCell} (zero : ZeroPath d m path cell) :
    ZeroPath d' m' path cell := by
  induction zero generalizing m' with
  | reg member =>
    obtain ⟨s, hs, related⟩ := body.left member
    cases related
    exact .reg hs
  | mem member =>
    obtain ⟨s, hs, related⟩ := body.left member
    cases related
    exact .mem hs
  | inst member childMember childName next ih =>
    obtain ⟨s, hs, related⟩ := body.left member
    obtain ⟨item, hi, relatedItem⟩ := order.2.left childMember
    cases relatedItem with
    | module c c' _ hn _ hb =>
      cases related with
      | same => exact .inst hs hi (hn.trans childName) (ih hb)
      | inst => exact .inst hs hi (hn.trans childName) (ih hb)

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

theorem zeroState_instance (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List ((port : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx port.val.ty))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (found : d.design.bodies.find? (·.name == child) = some c) :
    cast (State_inst_module d env m hm i p name child inputs member c found)
      (Interp.zeroState d env noExterns m hm ⟨.inst i p name child inputs, member⟩) =
        Interp.zeroState d env noExterns c (List.mem_of_find?_eq_some found) := by
  rw [Interp.zeroState]
  dsimp only
  split
  · rename_i c' hc
    have eq := Option.some.inj (hc.symm.trans found)
    subst c'
    simp only [cast_cast, cast_eq]
  · rename_i absent
    rw [found] at absent
    contradiction

theorem namedState_zero_of_path (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (path : List String) (cell : NamedCell) (zero : ZeroPath d.design.erase m.erase path cell) :
    namedState d env noExterns m hm (Interp.zeroState d env noExterns m hm) path =
      some cell := by
  generalize erased : m.erase = raw at zero
  induction zero generalizing m with
  | reg member =>
    rw [← erased] at member
    obtain ⟨i, target, reset, ni, np, next, member, _⟩ :=
      Ownership.reg_equation m.body _ _ _ _ _ member
    rw [namedState_register d env noExterns m hm _ i _ _ _ _ target reset ni np next member]
    congr 2
    rw [Interp.zeroState]
    rfl
  | mem member =>
    rw [← erased] at member
    obtain ⟨i, target, writes, member⟩ := Ownership.mem_equation m.body _ _ _ _ _ member
    rw [namedState_memory d env noExterns m hm _ i _ _ _ _ _ target writes member]
    congr 2
    rw [Interp.zeroState]
  | inst member childMember childName next ih =>
    rw [← erased] at member
    obtain ⟨i, inputs, member, _⟩ := Ownership.inst_equation m.body _ _ _ _ member
    obtain ⟨c, found, hc⟩ := erased_module_found d.design _ childMember
    rw [childName] at found
    rw [namedState_instance d env noExterns m hm _ i _ _ _ inputs member c found,
      zeroState_instance d env noExterns m hm i _ _ _ inputs member c found]
    exact ih c (List.mem_of_find?_eq_some found) hc

theorem path_of_namedState_zero (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (path : List String) (cell : NamedCell)
    (value : namedState d env noExterns m hm (Interp.zeroState d env noExterns m hm) path =
      some cell) : ZeroPath d.design.erase m.erase path cell := by
  induction path generalizing m with
  | nil => simp [namedState] at value
  | cons name path ih =>
    rw [namedState] at value
    split at value
    · contradiction
    · rename_i equation found
      have member := List.mem_of_find?_eq_some found
      have named : equationName equation = name := by simpa using List.find?_some found
      cases equation with
      | let_ | assign => contradiction
      | reg i p n w clock target reset ni np next =>
        change n = name at named
        subst n
        dsimp only at value
        split at value
        · rename_i empty
          have hp : path = [] := by simpa using empty
          subst path
          have vz : Interp.zeroState d env noExterns m hm
              ⟨.reg i p name w clock target reset ni np next, member⟩ = (0 : Value w) := by
            rw [Interp.zeroState]
            rfl
          rw [vz] at value
          cases value
          apply ZeroPath.reg (pos := p) (clock := clock) (reset := reset.map Typed.Reset.erase)
          exact (Ownership.mem_equationsErase m.body _).mpr
            ⟨_, member, i, .reg p name w clock reset, by simp [Typed.Equation.parts], rfl⟩
        · contradiction
      | mem i p n w depth clock target writes =>
        change n = name at named
        subst n
        dsimp only at value
        split at value
        · rename_i empty
          have hp : path = [] := by simpa using empty
          subst path
          have vz : Interp.zeroState d env noExterns m hm
              ⟨.mem i p name w depth clock target writes, member⟩ = (fun _ => 0) := by
            rw [Interp.zeroState]
          rw [vz] at value
          cases value
          apply ZeroPath.mem (pos := p) (clock := clock)
          exact (Ownership.mem_equationsErase m.body _).mpr
            ⟨_, member, i, .mem p name w depth clock, by simp [Typed.Equation.parts], rfl⟩
        · contradiction
      | inst i p n child inputs =>
        change n = name at named
        subst n
        dsimp only at value
        split at value
        · rename_i c childFound
          rw [zeroState_instance d env noExterns m hm i p name child inputs member c childFound]
            at value
          exact .inst (instance_member m i p name child inputs member)
            (d.design.environments c (List.mem_of_find?_eq_some childFound)).2.2
            (by simpa [Typed.Module.erase] using List.find?_some childFound)
            (ih c (List.mem_of_find?_eq_some childFound) value)
        · rename_i absent
          have stmt := instance_member m i p name child inputs member
          obtain ⟨item, found, _⟩ :=
            (d.wellFormed.2.1.2 m.erase (module_mem d.design m hm) _ stmt).1
          have existsItem : ∃ item ∈ d.design.erase.items, Typed.itemName item = child :=
            ⟨item, List.mem_of_find?_eq_some found, by
              simpa [Rules.findItem] using List.find?_some found⟩
          obtain ⟨e, he, _⟩ := external_exists d.design child existsItem absent
          simp [noExterns] at he

theorem namedState_zero_iff (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (path : List String) (cell : NamedCell) :
    namedState d env noExterns m hm (Interp.zeroState d env noExterns m hm) path =
      some cell ↔ ZeroPath d.design.erase m.erase path cell :=
  ⟨path_of_namedState_zero d env noExterns m hm path cell,
    namedState_zero_of_path d env noExterns m hm path cell⟩

theorem namedState_zero_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (body : Permuted StmtReorder m.erase.body m'.erase.body) :
    namedState d env noExterns m hm (Interp.zeroState d env noExterns m hm) =
      namedState d' env' noExterns' m' hm' (Interp.zeroState d' env' noExterns' m' hm') := by
  funext path
  apply Option.ext
  intro cell
  rw [namedState_zero_iff, namedState_zero_iff]
  exact ⟨fun h => h.reorder order body,
    fun h => h.reorder order.symm (body.symm.imp fun _ _ h => h.symm)⟩

end Silicon.Core.Semantics
