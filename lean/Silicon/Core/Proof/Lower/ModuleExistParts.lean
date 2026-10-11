-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleImage

/-!
Each instance op of a lowered module belongs to one source instance or one memory. Each
instance result has the type of its child port in the context.
-/
namespace Silicon.Core.LowerProof

open Semantics

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)

include h hm in
theorem port_lookup (i : Nat) (p : Pos) (n child : String)
    (conns : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
    (member : Typed.Equation.inst i p n child conns ∈ m.body) (q : Port)
    (hq : q ∈ m.interfaces child) (dir : q.dir = .output) :
    m.ctx.lookup (.port n q.name) = some (.value q.ty) := by
  have raw₀ := instance_member m i p n child conns member
  have entry : (Deps.Node.port n q.name, Typed.Kind.value q.ty) ∈ m.ctx := by
    rw [m.context_eq]
    unfold Typed.contextFromPorts
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨_, raw₀, ?_⟩
    simp only
    exact List.mem_filterMap.mpr ⟨q, hq, by simp [dir]⟩
  cases found : m.ctx.lookup (.port n q.name) with
  | none =>
    have := List.lookup_eq_none_iff.mp found _ entry
    simp at this
  | some k =>
    have member' := lookup_member _ _ _ found
    rw [m.context_eq] at member'
    rcases context_member _ _ _ _ member' with ⟨p', _, same, _⟩ | ⟨stmt, hs, decl⟩
    · cases same
    · cases stmt with
      | let_ | reg => obtain ⟨same, _⟩ := decl; cases same
      | mem => obtain ⟨same, _⟩ := decl; cases same
      | inst p'' n' child' xs =>
        obtain ⟨q', hq', _, same, kind⟩ := decl
        injection same with sameName samePort
        subst sameName
        have unique := (List.nodup_append.mp (scope_nodup raw t h m hm)).2.1
        have eqStmt := filterMap_unique unique hs raw₀ n rfl rfl
        cases eqStmt
        have interfaces : m.interfaces = Typed.portsOf t.erase := (t.environments m hm).1
        have hq₁ : q' ∈ Typed.portsOf t.erase child := by rw [← interfaces]; exact hq'
        have hq₂ : q ∈ Typed.portsOf t.erase child := by rw [← interfaces]; exact hq
        have := Check.interface_unique t.erase (certified raw t h).wellFormed.1 child q' hq₁ q hq₂
          samePort.symm
        subst this
        rw [kind]
      | _ => exact decl.elim

include h noExterns hm in
theorem inst_entry_unique (names₁ names₂ : List String) (inst c₁ c₂ : String)
    (a₁ a₂ : List (String × String × Mlir.Ty)) (r₁ r₂ : List (String × Mlir.Ty))
    (h₁ : (names₁, Mlir.Op.instance inst c₁ a₁ r₁) ∈ (Lower.module m).1.body)
    (h₂ : (names₂, Mlir.Op.instance inst c₂ a₂ r₂) ∈ (Lower.module m).1.body) :
    names₁ = names₂ ∧ c₁ = c₂ ∧ a₁ = a₂ ∧ r₁ = r₂ := by
  have same := filterMap_unique (module_instNames raw t h noExterns m hm _ rfl) h₁ h₂ inst rfl rfl
  simp only [Prod.mk.injEq, Mlir.Op.instance.injEq, true_and] at same
  exact same

omit raw t h noExterns hm in
/-- Each instance op is a source instance or a memory instance of the same name. -/
theorem instance_entry_cases (names : List String) (inst callee : String)
    (args : List (String × String × Mlir.Ty)) (results : List (String × Mlir.Ty))
    (he : (names, .instance inst callee args results) ∈ (Lower.module m).1.body) :
    (∃ i p conns, Typed.Equation.inst i p inst callee conns ∈ m.body) ∨
      ∃ i p w depth clk target ws, Typed.Equation.mem i p inst w depth clk target ws ∈ m.body ∧
        callee = (memConfig (finalState m) inst w depth).moduleName := by
  rw [module_body] at he
  obtain ⟨⟨names', op⟩, hraw, same⟩ := List.mem_map.mp he
  have op_shape : ∃ args', op = .instance inst callee args' results := by
    cases op <;> simp only [Lower.substitute, Prod.mk.injEq, reduceCtorEq, and_false] at same
    case «instance» inst' callee' args' results' =>
      obtain ⟨_, rfl, rfl, _, rfl⟩ := same
      exact ⟨args', rfl⟩
  obtain ⟨args', rfl⟩ := op_shape
  unfold rawBody at hraw
  rcases List.mem_append.mp hraw with hraw | hraw
  · rcases List.mem_append.mp hraw with hraw | hraw
    · obtain ⟨⟨tail, body, _, shapes⟩, _⟩ :=
        statements_step (Lower.registers m) (Lower.statements m) {}
      rw [← run_state] at body
      have tailEq : tail = (Lower.statementState m).body.toList := by simpa using body.symm
      rw [← tailEq] at hraw
      obtain ⟨stmt, hs, shape⟩ := shapes _ hraw rfl
      cases stmt <;> simp only [InstShape] at shape
      case inst p i child inputs =>
        obtain ⟨_, _, same⟩ := shape
        simp only [Prod.mk.injEq, Mlir.Op.instance.injEq] at same
        obtain ⟨_, rfl, rfl, _⟩ := same
        obtain ⟨eq, heq, part, hp, partEq⟩ := (statement_of_eq m _).mp hs
        cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
          List.not_mem_nil, or_false] at hp
        all_goals try (rcases hp with rfl | rfl <;> cases partEq)
        all_goals try (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases partEq)
        all_goals try (subst hp; cases partEq)
        exact Or.inl ⟨_, _, _, heq⟩
    · obtain ⟨x, hx, same⟩ := List.mem_map.mp hraw
      obtain ⟨i, p, memory, w, depth, clk, target, ws, heq, rfl⟩ := memoryEntries_mem m _ x hx
      simp only [memEntry, Prod.mk.injEq, Mlir.Op.instance.injEq] at same
      obtain ⟨_, rfl, rfl, _⟩ := same
      exact Or.inr ⟨i, p, w, depth, clk, target, ws, heq, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := registerEntries_mem m _ _ hraw
    simp only [Prod.mk.injEq, reduceCtorEq, and_false] at same

omit raw t h noExterns hm in
theorem let_equation (p : Pos) (x : String) (w : Nat) (e : Typed.Expr m.ctx (.bits w))
    (hs : Typed.Stmt.let_ p x w e ∈ Lower.statements m) :
    ∃ index, Typed.Equation.let_ index p x w e ∈ m.body := by
  obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
  cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  all_goals try (rcases hp with rfl | rfl <;> cases same)
  all_goals try (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases same)
  all_goals try (subst hp; cases same)
  exact ⟨_, he⟩

omit raw t h noExterns hm in
theorem assign_equation (p : Pos) (x : String) (w : Nat) (target)
    (e : Typed.Expr m.ctx (.bits w))
    (hs : Typed.Stmt.assign p x w target e ∈ Lower.statements m) :
    ∃ index, Typed.Equation.assign index p x w target e ∈ m.body := by
  obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
  cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  all_goals try (rcases hp with rfl | rfl <;> cases same)
  all_goals try (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases same)
  all_goals try (subst hp; cases same)
  exact ⟨_, he⟩

omit noExterns in
include h hm in
theorem clock_lookup (c : String) (hc : Rules.clockName m.erase c = true) :
    m.ctx.lookup (.name c) = some .clock := by
  unfold Rules.clockName at hc
  obtain ⟨port, found, ok⟩ := (Option.any_eq_true _ _).mp hc
  have member := List.mem_of_find?_eq_some found
  have named : port.name = c := by simpa using List.find?_some found
  have ok : port.dir = .input ∧ port.ty = .clock := by simpa using ok
  apply lookup_name raw t h m hm
  have entry := port_in_context m port member
  rw [named] at entry
  simpa [portKind, ok.1, ok.2] using entry

end

end Silicon.Core.LowerProof
