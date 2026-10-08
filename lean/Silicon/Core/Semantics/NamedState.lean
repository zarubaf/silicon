import Silicon.Core.Semantics.Named

/-!
A state path lists instance names and then a register or memory name.
Each leaf retains its width. A memory retains its depth and address order.
-/
namespace Silicon.Core.Semantics

inductive NamedCell where
  | register (width : Nat) (value : Value width)
  | memory (width depth : Nat) (values : Fin depth → Value width)

theorem instance_child_exists (d : CertifiedDesign) (noExterns : d.design.externs = [])
    (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (index : Nat) (pos : Pos) (name child : String)
    (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
    (member : Typed.Equation.inst index pos name child inputs ∈ m.body) :
    ∃ c, d.design.bodies.find? (·.name == child) = some c := by
  cases found : d.design.bodies.find? (·.name == child) with
  | some c => exact ⟨c, rfl⟩
  | none =>
    have stmt := instance_member m index pos name child inputs member
    have resolved := (d.wellFormed.2.1.2 m.erase (module_mem d.design m hm) _ stmt).1
    obtain ⟨item, hi, _⟩ := resolved
    have existsItem : ∃ i ∈ d.design.erase.items, Typed.itemName i = child :=
      ⟨item, List.mem_of_find?_eq_some hi, by
        simpa [Rules.findItem] using List.find?_some hi⟩
    obtain ⟨e, he, _⟩ := external_exists d.design child existsItem found
    simp [noExterns] at he

def namedState (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (path : List String) : Option NamedCell :=
  match path with
  | [] => none
  | name :: rest =>
    match found : m.body.find? (fun e => equationName e == name) with
    | none => none
    | some equation =>
      let member := List.mem_of_find?_eq_some found
      match equation, member with
      | .reg i p n width clock target reset ni np next, member =>
        if rest.isEmpty then
          some (.register width
            (state ⟨.reg i p n width clock target reset ni np next, member⟩))
        else none
      | .mem i p n width depth clock target writes, member =>
        if rest.isEmpty then
          some (.memory width depth (state ⟨.mem i p n width depth clock target writes, member⟩))
        else none
      | .inst i p n child inputs, member =>
        match childFound : d.design.bodies.find? (·.name == child) with
        | some c =>
          let childState := cast (State_inst_module d env m hm i p n child inputs member
            c childFound) (state ⟨.inst i p n child inputs, member⟩)
          namedState d env noExterns c (List.mem_of_find?_eq_some childFound) childState rest
        | none => False.elim (by
            obtain ⟨c, hc⟩ := instance_child_exists d noExterns m hm i p n child inputs member
            rw [childFound] at hc
            contradiction)
      | .let_ .., _ | .assign .., _ => none
termination_by path.length

theorem find_equation (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (equation : Typed.Equation m.ctx m.interfaces)
    (member : equation ∈ m.body) :
    m.body.find? (fun e => equationName e == equationName equation) = some equation := by
  have find (body : List (Typed.Equation m.ctx m.interfaces))
      (unique : (body.map equationName).Nodup) (member : equation ∈ body) :
      body.find? (fun e => equationName e == equationName equation) = some equation := by
    induction body with
    | nil => simp at member
    | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have ne : equationName first ≠ equationName equation := by
          intro eq
          exact unique.1 (eq ▸ List.mem_map.mpr ⟨equation, member, rfl⟩)
        simpa [ne] using ih unique.2 member
  exact find m.body (equation_names_nodup d.design d.wellFormed m hm) member

theorem namedState_register (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (i : Nat) (p : Pos) (name : String) (width : Nat)
    (clock : String) (target : Typed.valueTy m.ctx name = some (.bits width))
    (reset : Option (Typed.Reset m.ctx width)) (ni : Nat) (np : Pos)
    (next : Typed.Expr m.ctx (.bits width))
    (member : .reg i p name width clock target reset ni np next ∈ m.body) :
    namedState d env noExterns m hm state [name] =
      some (.register width
        (state ⟨.reg i p name width clock target reset ni np next, member⟩)) := by
  have found := find_equation d m hm _ member
  change m.body.find? (fun e => equationName e == name) = some _ at found
  rw [namedState]
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i equation he
    have eq := Option.some.inj (he.symm.trans found)
    subst equation
    rfl

theorem namedState_memory (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (i : Nat) (p : Pos) (name : String) (width depth : Nat)
    (clock : String) (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body) :
    namedState d env noExterns m hm state [name] =
      some (.memory width depth
        (state ⟨.mem i p name width depth clock target writes, member⟩)) := by
  have found := find_equation d m hm _ member
  change m.body.find? (fun e => equationName e == name) = some _ at found
  rw [namedState]
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i equation he
    have eq := Option.some.inj (he.symm.trans found)
    subst equation
    rfl

theorem namedState_instance (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (i : Nat) (p : Pos) (name child : String)
    (inputs : List ((port : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx port.val.ty))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (childFound : d.design.bodies.find? (·.name == child) = some c) (path : List String) :
    namedState d env noExterns m hm state (name :: path) =
      namedState d env noExterns c (List.mem_of_find?_eq_some childFound)
        (cast (State_inst_module d env m hm i p name child inputs member c childFound)
          (state ⟨.inst i p name child inputs, member⟩)) path := by
  have found := find_equation d m hm _ member
  change m.body.find? (fun e => equationName e == name) = some _ at found
  rw [namedState]
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i equation he
    have eq := Option.some.inj (he.symm.trans found)
    subst equation
    dsimp only
    split
    · rename_i c' hc
      have eq := Option.some.inj (hc.symm.trans childFound)
      subst c'
      rfl
    · rename_i absent
      rw [childFound] at absent
      contradiction

theorem namedState_injective (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (a b : State d env m hm)
    (same : ∀ path, namedState d env noExterns m hm a path =
      namedState d env noExterns m hm b path) : a = b := by
  funext equation
  rcases equation with ⟨equation, member⟩
  cases equation with
  | let_ | assign =>
    change (_ : Unit) = _
    exact Subsingleton.elim _ _
  | reg i p name width clock target reset ni np next =>
    have eq := same [name]
    rw [namedState_register d env noExterns m hm a i p name width clock target reset ni np
      next member, namedState_register d env noExterns m hm b i p name width clock target
      reset ni np next member] at eq
    exact eq_of_heq (NamedCell.register.inj (Option.some.inj eq)).2
  | mem i p name width depth clock target writes =>
    have eq := same [name]
    rw [namedState_memory d env noExterns m hm a i p name width depth clock target writes
      member, namedState_memory d env noExterns m hm b i p name width depth clock target
      writes member] at eq
    exact eq_of_heq (NamedCell.memory.inj (Option.some.inj eq)).2.2
  | inst i p name child inputs =>
    obtain ⟨c, found⟩ := instance_child_exists d noExterns m hm i p name child inputs member
    let typeEq := State_inst_module d env m hm i p name child inputs member c found
    have eq := namedState_injective d env noExterns c (List.mem_of_find?_eq_some found)
      (cast typeEq (a ⟨.inst i p name child inputs, member⟩))
      (cast typeEq (b ⟨.inst i p name child inputs, member⟩)) (fun path => by
        have eq := same (name :: path)
        rw [namedState_instance d env noExterns m hm a i p name child inputs member c found,
          namedState_instance d env noExterns m hm b i p name child inputs member c found] at eq
        exact eq)
    have uncast := congrArg (cast typeEq.symm) eq
    simpa only [cast_cast, cast_eq] using uncast
termination_by moduleLevel d.design.erase d.wellFormed m.name
decreasing_by
  have stmt := instance_member m i p name child inputs member
  have childMem : child ∈ Typed.childNames m.erase := List.mem_filterMap.mpr ⟨_, stmt, rfl⟩
  have named : c.name = child := by simpa using List.find?_some found
  simpa only [named, Typed.Module.erase] using
    moduleLevel_lower d.design.erase d.wellFormed m.erase (module_mem d.design m hm)
      child childMem

theorem namedState_memories (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth)) :
    namedState d env noExterns m hm state [name] = some (.memory width depth
      (stateMemories m (designChildren d env m hm) state name width depth found)) := by
  unfold stateMemories
  cases decodeMemory m name width depth found with
  | mem i p n w size clock target writes member =>
    exact namedState_memory d env noExterns m hm state i p name width depth clock target
      writes member

theorem stateMemories_eq_of_named (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : ∀ path, namedState d env noExterns m hm state path =
      namedState d' env' noExterns' m' hm' state' path)
    (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth))
    (found' : m'.ctx.lookup (.name name) = some (.memory width depth)) :
    stateMemories m (designChildren d env m hm) state name width depth found =
      stateMemories m' (designChildren d' env' m' hm') state' name width depth found' := by
  have eq := same [name]
  rw [namedState_memories d env noExterns m hm state name width depth found,
    namedState_memories d' env' noExterns' m' hm' state' name width depth found'] at eq
  exact eq_of_heq (NamedCell.memory.inj (Option.some.inj eq)).2.2

theorem named_solution_register (d : CertifiedDesign) (env : Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (state : State d env m hm) (input : Input m) (values : NamedValues)
    (solved : IsNamedSolution d env m hm state input values)
    (pos : Pos) (name : String) (width : Nat) (clock : String) (reset : Option Core.Reset)
    (member : Core.Stmt.reg pos name width clock reset ∈ m.erase.body)
    (found : m.ctx.lookup (.name name) = some (.value (.bits width))) :
    namedState d env noExterns m hm state [name] =
      some (.register width (BitVec.ofNat width (values (.name name)))) := by
  obtain ⟨index, target, reset, ni, np, next, member, _⟩ :=
    Ownership.reg_equation m.body pos name width clock reset member
  have equation := solved.2 (.name name) width found
    (ValueDriver.reg index pos name width clock target reset ni np next member)
  change BitVec.ofNat width (values (.name name)) =
    state ⟨.reg index pos name width clock target reset ni np next, member⟩ at equation
  rw [namedState_register d env noExterns m hm state index pos name width clock target
    reset ni np next member, ← equation]

end Silicon.Core.Semantics
