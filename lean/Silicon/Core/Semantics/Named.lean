import Silicon.Core.Interp

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
