import Silicon.Core.Interp
import Silicon.Core.Canonical.Reorder
import Silicon.Core.Canonical.WellFormed

/-!
Named values use natural numbers. The context fixes each value width.
Names outside the data context have value zero.
-/
namespace Silicon.Core.Semantics

abbrev NamedValues := Deps.Node → Nat

def Valuation.named (values : Valuation ctx) : NamedValues :=
  fun node => match found : ctx.lookup node with
  | some (.value (.bits width)) => (values node width found).toNat
  | _ => 0

def NamedValues.valuation (values : NamedValues) (ctx : Typed.Ctx) : Valuation ctx :=
  fun node width _ => BitVec.ofNat width (values node)

def NamedValues.Normalized (values : NamedValues) (ctx : Typed.Ctx) : Prop :=
  ∀ node, match ctx.lookup node with
  | some (.value (.bits width)) => values node < 2 ^ width
  | _ => values node = 0

@[simp] theorem Valuation.named_at (values : Valuation ctx) (node : Deps.Node)
    (width : Nat) (found : ctx.lookup node = some (.value (.bits width))) :
    values.named node = (values node width found).toNat := by
  unfold Valuation.named
  split
  · rename_i w hw
    have eq : width = w := by simpa [found] using hw
    subst w
    rfl
  · rename_i absent
    exact False.elim (absent width found)

@[simp] theorem Valuation.named_valuation (values : Valuation ctx) :
    values.named.valuation ctx = values := by
  funext node width found
  simp [NamedValues.valuation, values.named_at node width found]

theorem Valuation.named_normalized (values : Valuation ctx) :
    values.named.Normalized ctx := by
  intro node
  cases found : ctx.lookup node with
  | none => simp [Valuation.named, found]
  | some kind =>
    cases kind with
    | clock => simp [Valuation.named, found]
    | memory => simp [Valuation.named, found]
    | value ty =>
      cases ty with
      | clock => simp [Valuation.named, found]
      | bits width =>
        simp only [values.named_at node width found]
        exact (values node width found).isLt

@[simp] theorem NamedValues.valuation_named (values : NamedValues)
    (normalized : values.Normalized ctx) : (values.valuation ctx).named = values := by
  funext node
  have norm := normalized node
  cases found : ctx.lookup node with
  | none =>
    simp only [found] at norm
    simpa [Valuation.named, found] using norm.symm
  | some kind =>
    simp only [found] at norm
    cases kind with
    | clock => simpa [Valuation.named, found] using norm.symm
    | memory => simpa [Valuation.named, found] using norm.symm
    | value ty =>
      cases ty with
      | clock => simpa [Valuation.named, found] using norm.symm
      | bits width =>
        rw [Valuation.named_at _ node width found]
        exact Nat.mod_eq_of_lt norm

/-! A named solution satisfies every driver equation at the declared width. -/
def IsNamedSolution (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : NamedValues) : Prop :=
  values.Normalized m.ctx ∧ IsSolution d env m hm state input (values.valuation m.ctx)

theorem IsSolution.named (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : Valuation m.ctx)
    (solved : IsSolution d env m hm state input values) :
    IsNamedSolution d env m hm state input values.named := by
  exact ⟨values.named_normalized, by simpa using solved⟩

theorem named_solution_unique (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) :
    ∃ values, IsNamedSolution d env m hm state input values ∧
      ∀ other, IsNamedSolution d env m hm state input other → other = values := by
  obtain ⟨values, solved, unique⟩ := solution_unique d env m hm state input
  refine ⟨values.named, IsSolution.named d env m hm state input values solved, ?_⟩
  intro other ho
  have same := congrArg Valuation.named (unique (other.valuation m.ctx) ho.2)
  simpa only [other.valuation_named ho.1] using same

end Silicon.Core.Semantics

/-!
Expression values depend on erased operands and named lookups.
They do not depend on the positions of declarations in a context.
-/
namespace Silicon.Core.Semantics

abbrev NamedMemories := String → Nat → Nat

def NamedMemories.typed (memories : NamedMemories) (ctx : Typed.Ctx) : Memories ctx :=
  fun name width _ _ address => BitVec.ofNat width (memories name address.val)

def Memories.named (memories : Memories ctx) : NamedMemories :=
  fun name address => match found : ctx.lookup (.name name) with
  | some (.memory width depth) =>
    if bound : address < depth then (memories name width depth found ⟨address, bound⟩).toNat
    else 0
  | _ => 0

@[simp] theorem Memories.named_at (memories : Memories ctx) (name : String)
    (width depth : Nat) (found : ctx.lookup (.name name) = some (.memory width depth))
    (address : Fin depth) :
    memories.named name address.val = (memories name width depth found address).toNat := by
  unfold Memories.named
  split
  · rename_i w size hs
    have eq : width = w ∧ depth = size := by simpa [found] using hs
    rcases eq with ⟨rfl, rfl⟩
    simp only [address.isLt, dite_true]
  · rename_i absent
    exact False.elim (absent width depth found)

@[simp] theorem Memories.named_typed (memories : Memories ctx) :
    memories.named.typed ctx = memories := by
  funext name width depth found address
  simp [NamedMemories.typed, memories.named_at name width depth found address]

private theorem expr_erase_injective (a b : Typed.Expr ctx ty) (erase : a.erase = b.erase) :
    a = b := by
  have same := Typed.infer_complete a
  rw [erase, Typed.infer_complete b] at same
  cases same
  rfl

theorem evalExpr_recontext {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (e : Typed.Expr ctx ty) :
    evalExpr (values.valuation ctx') (memories.typed ctx') (e.recontext lookup) =
      evalExpr (values.valuation ctx) (memories.typed ctx) e := by
  induction e <;> simp_all [Typed.Expr.recontext, evalExpr, NamedValues.valuation]
  rfl

theorem evalExpr_erase_eq {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (a : Typed.Expr ctx ty) (b : Typed.Expr ctx' ty)
    (erase : a.erase = b.erase) :
    evalExpr (values.valuation ctx) (memories.typed ctx) a =
      evalExpr (values.valuation ctx') (memories.typed ctx') b := by
  have equal : a.recontext lookup = b :=
    expr_erase_injective _ _ ((a.recontext_erase lookup).trans erase)
  rw [← equal]
  exact (evalExpr_recontext lookup values memories a).symm

def evalNamedExpr (ctx : Typed.Ctx) (values : NamedValues) (memories : NamedMemories)
    (raw : Core.Expr) (width : Nat) : Option Nat :=
  (Typed.expression ctx raw (.bits width)).map fun (expr : Typed.Expr ctx (.bits width)) =>
    (evalExpr (values.valuation ctx) (memories.typed ctx) expr).toNat

theorem evalNamedExpr_typed (values : NamedValues) (memories : NamedMemories)
    (expr : Typed.Expr ctx (.bits width)) :
    evalNamedExpr ctx values memories expr.erase width =
      some (evalExpr (values.valuation ctx) (memories.typed ctx) expr).toNat := by
  simp [evalNamedExpr, Typed.expression, Typed.expressionWith, Typed.infer_complete,
    Typed.castTerm]

private theorem expression_erase (expr : Typed.Expr ctx ty)
    (found : Typed.expression ctx raw ty = some expr) : expr.erase = raw := by
  obtain ⟨term, inferred, casted⟩ := Option.bind_eq_some_iff.mp found
  exact (Typed.castTerm_erase term ty expr casted).trans
    (Typed.infer_erase ctx raw term inferred)

private theorem expression_complete (expr : Typed.Expr ctx ty) :
    Typed.expression ctx expr.erase ty = some expr := by
  simp [Typed.expression, Typed.expressionWith, Typed.infer_complete, Typed.castTerm]

theorem evalNamedExpr_lookup_congr {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (raw : Core.Expr) (width : Nat) :
    evalNamedExpr ctx values memories raw width =
      evalNamedExpr ctx' values memories raw width := by
  cases found : Typed.expression ctx raw (.bits width) with
  | none =>
    cases found' : Typed.expression ctx' raw (.bits width) with
    | none => simp [evalNamedExpr, found, found']
    | some expr =>
      let back := expr.recontext (fun n => (lookup n).symm)
      have erase : back.erase = raw :=
        (expr.recontext_erase (fun n => (lookup n).symm)).trans (expression_erase expr found')
      have complete := expression_complete back
      rw [erase, found] at complete
      contradiction
  | some expr =>
    let next := expr.recontext lookup
    have erase : next.erase = raw := (expr.recontext_erase lookup).trans
      (expression_erase expr found)
    have complete := expression_complete next
    rw [erase] at complete
    simp only [evalNamedExpr, found, complete, Option.map_some]
    exact congrArg (fun value : Value width => some value.toNat)
      (evalExpr_recontext lookup values memories expr).symm

/-! Erased let and output equations determine their named solution values. -/
theorem named_solution_let (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : NamedValues)
    (solved : IsNamedSolution d env m hm state input values)
    (pos : Pos) (name : String) (width : Nat) (raw : Core.Expr)
    (member : Core.Stmt.let_ pos name width raw ∈ m.erase.body)
    (found : m.ctx.lookup (.name name) = some (.value (.bits width))) :
    evalNamedExpr m.ctx values (stateMemories m (designChildren d env m hm) state).named
      raw width = some (values (.name name)) := by
  obtain ⟨index, expr, member, erase⟩ :=
    Ownership.let_equation m.body pos name width raw member
  have equation := solved.2 (.name name) width found
    (ValueDriver.let_ index pos name width expr member)
  change BitVec.ofNat width (values (.name name)) =
    evalExpr (values.valuation m.ctx) (stateMemories m (designChildren d env m hm) state) expr
    at equation
  have normalized := solved.1 (.name name)
  simp only [found] at normalized
  rw [← erase, evalNamedExpr_typed, Memories.named_typed, ← equation]
  simp [Nat.mod_eq_of_lt normalized]

theorem named_solution_assign (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : NamedValues)
    (solved : IsNamedSolution d env m hm state input values)
    (pos : Pos) (name : String) (width : Nat) (raw : Core.Expr)
    (member : Core.Stmt.assign pos name raw ∈ m.erase.body)
    (found : m.ctx.lookup (.name name) = some (.value (.bits width))) :
    evalNamedExpr m.ctx values (stateMemories m (designChildren d env m hm) state).named
      raw width = some (values (.name name)) := by
  obtain ⟨index, w, target, expr, member, erase⟩ :=
    Ownership.assign_equation m.body pos name raw member
  have widths : w = width := by
    simpa [Typed.valueTy, found] using target.symm
  subst w
  have equation := solved.2 (.name name) width found
    (ValueDriver.assign index pos name width target expr member)
  change BitVec.ofNat width (values (.name name)) =
    evalExpr (values.valuation m.ctx) (stateMemories m (designChildren d env m hm) state) expr
    at equation
  have normalized := solved.1 (.name name)
  simp only [found] at normalized
  rw [← erase, evalNamedExpr_typed, Memories.named_typed, ← equation]
  simp [Nat.mod_eq_of_lt normalized]

theorem named_solution_input (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (input : Input m) (values : NamedValues)
    (solved : IsNamedSolution d env m hm state input values)
    (port : Port) (member : port ∈ m.ports) (dir : port.dir = .input)
    (bits : port.ty = .bits width) :
    values (.name port.name) =
      (cast (congrArg TyValue bits) (input ⟨port, member, dir⟩)).toNat := by
  have found := port_found d.design d.wellFormed m hm port member bits
  have equation := solved.2 (.name port.name) width found
    (ValueDriver.input port member dir bits)
  have normalized := solved.1 (.name port.name)
  simp only [found] at normalized
  have numbers := congrArg BitVec.toNat equation
  simpa [NamedValues.valuation, ValueDriver.eval, Nat.mod_eq_of_lt normalized] using numbers

end Silicon.Core.Semantics

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

/-!
A named run reads inputs by port name and records outputs in port order.
It starts with zero state and requires a design without externs.
-/
namespace Silicon.Core

open Semantics

namespace NamedRun

def inputValues (m : Typed.Module) (values : List (String × Nat)) : Input m :=
  fun p => match p.val.ty with
  | .clock => ()
  | .bits w => BitVec.ofNat w ((values.lookup p.val.name).getD 0)

def encodeOutputs (ports : List Port) (values : PortValues ports .output) :
    List (String × Nat) :=
  ports.attach.filterMap fun p =>
    if h : p.val.dir = .output then
      match ht : p.val.ty with
      | .clock => none
      | .bits _ => some (p.val.name,
          (cast (congrArg TyValue ht) (values ⟨p.val, p.property, h⟩)).toNat)
    else none

def outputValues (m : Typed.Module) (values : Output m) : List (String × Nat) :=
  encodeOutputs m.ports values

def emptyEnv (t : CertifiedDesign) (noExterns : t.design.externs = []) : Env t.design :=
  fun _ member => False.elim (by simp [noExterns] at member)

theorem top_exists (t : CertifiedDesign) (noExterns : t.design.externs = []) :
    ∃ m, t.design.bodies.find? (·.name == t.design.top) = some m := by
  cases found : t.design.bodies.find? (·.name == t.design.top) with
  | some m => exact ⟨m, rfl⟩
  | none =>
    have resolved := t.wellFormed.2.1.1
    have item : ∃ i ∈ t.design.erase.items, Typed.itemName i = t.design.top := by
      cases hi : Rules.findItem t.design.erase t.design.erase.top with
      | none => simp [hi] at resolved
      | some i =>
        exact ⟨i, List.mem_of_find?_eq_some hi, by
          simpa [Rules.findItem, Typed.Design.erase, Typed.assembleDesign] using
            List.find?_some hi⟩
    obtain ⟨e, he, _⟩ := external_exists t.design t.design.top item found
    simp [noExterns] at he

def top (t : CertifiedDesign) (noExterns : t.design.externs = []) :
    {m : Typed.Module // m ∈ t.design.bodies} :=
  match found : t.design.bodies.find? (·.name == t.design.top) with
  | some m => ⟨m, List.mem_of_find?_eq_some found⟩
  | none => False.elim (by
      obtain ⟨m, hm⟩ := top_exists t noExterns
      rw [found] at hm
      contradiction)

end NamedRun

def namedRun (t : CertifiedDesign) (inputs : List (List (String × Nat)))
    (noExterns : t.design.externs = []) : List (List (String × Nat)) :=
  let env := NamedRun.emptyEnv t noExterns
  let m := NamedRun.top t noExterns
  (Interp.run t env m.val m.property (Interp.zeroState t env noExterns m.val m.property)
    (inputs.map (NamedRun.inputValues m.val))).map (NamedRun.outputValues m.val)

end Silicon.Core

/-! A step simulation gives equal named traces for every finite input sequence. -/
namespace Silicon.Core

open Semantics

namespace NamedRun

theorem run_eq_of_named_step (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (simulate : ∀ (a : State d env m hm) (b : State d' env' m' hm'),
      namedState d env noExterns m hm a = namedState d' env' noExterns' m' hm' b →
      ∀ vector : List (String × Nat),
      let left := Interp.step d env m hm a (inputValues m vector)
      let right := Interp.step d' env' m' hm' b (inputValues m' vector)
      outputValues m left.2 = outputValues m' right.2 ∧
        namedState d env noExterns m hm left.1 =
          namedState d' env' noExterns' m' hm' right.1)
    (a : State d env m hm) (b : State d' env' m' hm')
    (same : namedState d env noExterns m hm a = namedState d' env' noExterns' m' hm' b)
    (inputs : List (List (String × Nat))) :
    (Interp.run d env m hm a (inputs.map (inputValues m))).map (outputValues m) =
      (Interp.run d' env' m' hm' b (inputs.map (inputValues m'))).map (outputValues m') := by
  induction inputs generalizing a b with
  | nil => rfl
  | cons vector rest ih =>
    obtain ⟨outputs, states⟩ := simulate a b same vector
    simp only [List.map_cons, Interp.run]
    rw [outputs, ih _ _ states]

end NamedRun

end Silicon.Core

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
    obtain ⟨item, hi, relatedItem⟩ := order.items.left childMember
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

/-! Reordered erased modules retain their named interfaces and context lookups. -/
namespace Silicon.Core

open Semantics

namespace Reorder

theorem typed_module {d d' : CertifiedDesign} (order : Reorder d.design.erase d'.design.erase)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    ∃ m', d'.design.bodies.find? (·.name == m.name) = some m' ∧
      ItemReorder (.module m.erase) (.module m'.erase) := by
  obtain ⟨item, member, related⟩ := order.items.left (d.design.environments m hm).2.2
  cases related with
  | module raw raw' pos name ports body =>
    obtain ⟨m', found, erased⟩ := erased_module_found d'.design raw' member
    refine ⟨m', ?_, ?_⟩
    · simpa only [name, Typed.Module.erase] using found
    · rw [erased]
      exact .module _ _ pos name ports body

theorem typed_context {d d' : CertifiedDesign} (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder (.module m.erase) (.module m'.erase)) (node : Deps.Node) :
    m.ctx.lookup node = m'.ctx.lookup node := by
  rw [d.design.module_context m hm, d'.design.module_context m' hm']
  cases related with
  | module _ _ _ _ ports body =>
    exact order.context_lookup d.wellFormed.1 (module_mem d.design m hm) ports body node

theorem typed_interfaces {d d' : CertifiedDesign}
    (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies) :
    m.interfaces = m'.interfaces := by
  rw [(d.design.environments m hm).1, (d'.design.environments m' hm').1]
  exact order.portsOf d.wellFormed.1

end Reorder

namespace NamedRun

theorem top_found (d : CertifiedDesign) (noExterns : d.design.externs = []) :
    d.design.bodies.find? (·.name == d.design.top) = some (top d noExterns).val := by
  unfold top
  split
  · assumption
  · rename_i absent
    obtain ⟨m, found⟩ := top_exists d noExterns
    rw [absent] at found
    contradiction

theorem top_reorder (d d' : CertifiedDesign) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase) :
    ItemReorder (.module (top d noExterns).val.erase)
      (.module (top d' noExterns').val.erase) := by
  obtain ⟨m', found, related⟩ := order.typed_module (top d noExterns).val
    (top d noExterns).property
  have named : (top d noExterns).val.name = d.design.top := by
    simpa using List.find?_some (top_found d noExterns)
  have tops : d'.design.top = d.design.top := order.1
  rw [named, ← tops, top_found d' noExterns'] at found
  cases found
  exact related

theorem zero_top_reorder (d d' : CertifiedDesign) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase) :
    let m := top d noExterns
    let m' := top d' noExterns'
    namedState d (emptyEnv d noExterns) noExterns m.val m.property
      (Interp.zeroState d (emptyEnv d noExterns) noExterns m.val m.property) =
    namedState d' (emptyEnv d' noExterns') noExterns' m'.val m'.property
      (Interp.zeroState d' (emptyEnv d' noExterns') noExterns' m'.val m'.property) := by
  obtain related := top_reorder d d' noExterns noExterns' order
  cases related with
  | module _ _ _ _ _ body =>
    exact namedState_zero_reorder d d' _ _ noExterns noExterns' order _ _ _ _ body

end NamedRun

end Silicon.Core
