import Silicon.Core.Proof.Lower.Counts
import Silicon.Core.Proof.Lower.Typing

/-!
The final build state retains each op, port, and update that a statement adds.
-/
namespace Silicon.Core.LowerProof

theorem statements_presence (registers : List String) (stmts : List (Typed.Stmt ctx ports))
    (s₀ : Lower.State) (stmt : Typed.Stmt ctx ports) (hs : stmt ∈ stmts) :
    ∃ s, Grows (Lower.statement registers stmt s).2
      ((do for stmt in stmts do Lower.statement registers stmt) s₀).2 := by
  induction stmts generalizing s₀ with
  | nil => cases hs
  | cons first rest ih =>
    rw [run_cons]
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨s₀, grows_statements registers rest _⟩
    · exact ih _ hs

theorem emit_mem (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    ([dest.getD (toString s.nextTemp)], op) ∈ (Lower.emit dest op s).2.body.toList := by
  rw [emit_body]
  simp

/-- An expression that adds no alias defines its destination with its own type. -/
theorem expr_dest_entry (registers : List String) (e : Typed.Expr ctx (.bits w)) (name : String)
    (fresh : NotAliased e) (s : Lower.State) :
    ∃ op, ([name], op) ∈ (Lower.expr registers e (some name) s).2.body.toList ∧
      op.resultTypes = [.int w] := by
  cases e with
  | ref => exact fresh.elim
  | const p w v => exact ⟨_, emit_mem (some name) _ s, rfl⟩
  | un p op a =>
    cases op
    exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | bin => exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | concat => exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | icmp => exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | mux => exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | extract => exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | replicate => exact ⟨_, emit_mem (some name) _ _, rfl⟩
  | @read width depth p memory found addr =>
    cases hw : Lower.expr registers addr none (reserve s memory) with
    | mk a walked =>
    let index := (s.readCounts.lookup memory).getD 0
    have result := inRange_result depth a (record walked ⟨memory, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨memory, index, a⟩) with
    | mk guard state =>
    rw [hg] at result
    rw [read_eq registers p memory found addr (some name) s a walked hw guard state hg]
    cases guard with
    | none =>
      have e : (none : Option String) = some _ :=
        result.trans (ite_eq_right_of_eq_false _ _ (eq_false fresh))
      cases e
    | some ok => exact ⟨_, emit_mem (some name) _ _, rfl⟩

end Silicon.Core.LowerProof
