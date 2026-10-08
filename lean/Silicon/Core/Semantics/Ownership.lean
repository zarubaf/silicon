import Silicon.Core.Typed

/-! Context entries and erased statements retain their typed source declarations. -/
namespace Silicon.Core.Semantics.Ownership

open Typed

/-! A value context entry comes from a port, a local definition, or an instance output. -/
theorem value_origin (m : Typed.Module) (node : Deps.Node) (width : Nat)
    (found : m.ctx.lookup node = some (.value (.bits width))) :
    (∃ p ∈ m.ports, node = .name p.name ∧ p.ty = .bits width) ∨
    (∃ pos name value, Core.Stmt.let_ pos name width value ∈ m.erase.body ∧
      node = .name name) ∨
    (∃ pos name clock reset, Core.Stmt.reg pos name width clock reset ∈ m.erase.body ∧
      node = .name name) ∨
    (∃ pos name child inputs p, Core.Stmt.inst pos name child inputs ∈ m.erase.body ∧
      p ∈ m.interfaces child ∧ p.dir = .output ∧ p.ty = .bits width ∧
      node = .port name p.name) := by
  rw [m.context_eq] at found
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp found
  have hm : (node, Kind.value (.bits width)) ∈ contextFromPorts m.interfaces m.erase := by
    rw [show contextFromPorts m.interfaces m.erase = _ from he]
    simp
  simp only [contextFromPorts, List.mem_append] at hm
  rcases hm with hp | hs
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp hp
    split at he
    · cases he
    · have hn := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      simp only [Kind.value.injEq] at ht
      exact Or.inl ⟨p, hp, hn.symm, ht⟩
  · obtain ⟨stmt, hs, he⟩ := List.mem_flatMap.mp hs
    cases stmt <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    case let_ pos name w value =>
      cases he
      exact Or.inr (Or.inl ⟨pos, name, value, hs, rfl⟩)
    case reg pos name w clock reset =>
      cases he
      exact Or.inr (Or.inr (Or.inl ⟨pos, name, clock, reset, hs, rfl⟩))
    case mem pos name w depth clock => cases he
    case inst pos name child inputs =>
      obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp he
      split at he <;> try contradiction
      next h =>
        simp only [beq_iff_eq] at h
        have he := Option.some.inj he
        have hn := congrArg Prod.fst he
        have ht := congrArg Prod.snd he
        simp only [Kind.value.injEq] at ht
        exact Or.inr (Or.inr (Or.inr ⟨pos, name, child, inputs, p, hs, hp, h,
          ht, hn.symm⟩))
    all_goals contradiction

/-! Sorting restores source order but does not add or remove equation parts. -/
theorem mem_equationsErase {ctx : Ctx} {ports : String → List Port}
    (body : List (Equation ctx ports)) (stmt : Core.Stmt) :
    stmt ∈ equationsErase body ↔
      ∃ eq ∈ body, ∃ index typed, (index, typed) ∈ eq.parts ∧ typed.erase = stmt := by
  simp only [equationsErase, List.mem_map, List.mem_mergeSort, List.mem_flatMap]
  constructor
  · rintro ⟨⟨index, typed⟩, ⟨eq, he, hp⟩, hs⟩
    exact ⟨eq, he, index, typed, hp, hs⟩
  · rintro ⟨eq, he, index, typed, hp, hs⟩
    exact ⟨(index, typed), ⟨eq, he, hp⟩, hs⟩

/-! A raw let statement comes from a typed let equation with the same value syntax. -/
theorem let_equation {ctx : Ctx} {ports : String → List Port}
    (body : List (Equation ctx ports)) (pos : Pos) (name : String)
    (width : Nat) (raw : Core.Expr)
    (hm : Core.Stmt.let_ pos name width raw ∈ equationsErase body) :
    ∃ index, ∃ value : Typed.Expr ctx (.bits width),
      Equation.let_ index pos name width value ∈ body ∧ value.erase = raw := by
  obtain ⟨eq, he, index, typed, hp, hs⟩ := (mem_equationsErase body _).mp hm
  cases eq <;> simp only [Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  case let_ i p n w value =>
    cases hp
    cases hs
    exact ⟨_, _, he, rfl⟩
  case reg i p n w clock target reset ni np ne =>
    rcases hp with hp | hp <;> cases hp <;> cases hs
  case mem i p n w depth clock target writes =>
    rcases hp with hp | hp
    · cases hp; cases hs
    · obtain ⟨wr, _, hp⟩ := List.mem_map.mp hp
      cases hp
      cases hs
  all_goals cases hp; cases hs

/-! A register declaration retains its reset and owns a typed next value. -/
theorem reg_equation {ctx : Ctx} {ports : String → List Port}
    (body : List (Equation ctx ports)) (pos : Pos) (name : String)
    (width : Nat) (clock : String) (raw : Option Core.Reset)
    (hm : Core.Stmt.reg pos name width clock raw ∈ equationsErase body) :
    ∃ index target reset nextIndex nextPos next,
      Equation.reg index pos name width clock target reset nextIndex nextPos next ∈ body ∧
        reset.map Typed.Reset.erase = raw := by
  obtain ⟨eq, he, index, typed, hp, hs⟩ := (mem_equationsErase body _).mp hm
  cases eq <;> simp only [Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  case reg i p n w clock target reset ni np ne =>
    rcases hp with hp | hp
    · cases hp
      cases hs
      exact ⟨_, _, _, _, _, _, he, rfl⟩
    · cases hp; cases hs
  case mem i p n w depth clock target writes =>
    rcases hp with hp | hp
    · cases hp; cases hs
    · obtain ⟨wr, _, hp⟩ := List.mem_map.mp hp
      cases hp
      cases hs
  all_goals cases hp; cases hs

/-! An output assignment retains its typed value and target lookup proof. -/
theorem assign_equation {ctx : Ctx} {ports : String → List Port}
    (body : List (Equation ctx ports)) (pos : Pos) (name : String) (raw : Core.Expr)
    (hm : Core.Stmt.assign pos name raw ∈ equationsErase body) :
    ∃ index width target value,
      Equation.assign index pos name width target value ∈ body ∧ value.erase = raw := by
  obtain ⟨eq, he, index, typed, hp, hs⟩ := (mem_equationsErase body _).mp hm
  cases eq <;> simp only [Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  case assign i p n w target value =>
    cases hp
    cases hs
    exact ⟨_, _, _, _, he, rfl⟩
  case reg i p n w clock target reset ni np ne =>
    rcases hp with hp | hp <;> cases hp <;> cases hs
  case mem i p n w depth clock target writes =>
    rcases hp with hp | hp
    · cases hp; cases hs
    · obtain ⟨wr, _, hp⟩ := List.mem_map.mp hp
      cases hp
      cases hs
  all_goals cases hp; cases hs

/-! Instance connections retain their port membership proofs and expression syntax. -/
theorem inst_equation {ctx : Ctx} {ports : String → List Port}
    (body : List (Equation ctx ports)) (pos : Pos) (name child : String)
    (raw : List (String × Core.Expr))
    (hm : Core.Stmt.inst pos name child raw ∈ equationsErase body) :
    ∃ index inputs, Equation.inst index pos name child inputs ∈ body ∧
      inputs.map (fun input => (input.1.val.name, input.2.erase)) = raw := by
  obtain ⟨eq, he, index, typed, hp, hs⟩ := (mem_equationsErase body _).mp hm
  cases eq <;> simp only [Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  case inst i p n child inputs =>
    cases hp
    cases hs
    exact ⟨_, _, he, rfl⟩
  case reg i p n w clock target reset ni np ne =>
    rcases hp with hp | hp <;> cases hp <;> cases hs
  case mem i p n w depth clock target writes =>
    rcases hp with hp | hp
    · cases hp; cases hs
    · obtain ⟨wr, _, hp⟩ := List.mem_map.mp hp
      cases hp
      cases hs
  all_goals cases hp; cases hs

end Silicon.Core.Semantics.Ownership
