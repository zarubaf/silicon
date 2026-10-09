import Silicon.Core.Canonical.Values

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
