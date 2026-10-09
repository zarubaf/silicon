import Silicon.Core.Proof.Lower.ModuleFacts

/-!
A named statement either defines its own name or aliases it to its expression result.
The final module renames the name and the result to one definition.
-/
namespace Silicon.Core.LowerProof

def letResult (registers : List String) : Typed.Stmt ctx ports → Lower.State → String
  | .let_ _ name _ e, s | .assign _ name _ _ e, s => (Lower.expr registers e (some name) s).1
  | _, _ => ""

def ResultAlias (result name : String) : Option String → Prop
  | some v => v = result
  | none => result = name

theorem expr_named_result (registers : List String) (e : Typed.Expr ctx (.bits w))
    (name : String) (s : Lower.State) : ∃ v,
      (Lower.expr registers e (some name) s).2.aliases = withAlias s.aliases name v ∧
      ResultAlias (Lower.expr registers e (some name) s).1 name v := by
  cases e with
  | ref p node found => exact ⟨some (Lower.valueName registers node), rfl, rfl⟩
  | const p w v => exact ⟨none, emit_aliases (some name) _ s, emit_result (some name) _ s⟩
  | un p op a =>
    cases op
    exact ⟨none, (emit_aliases (some name) _ _).trans ((emit_aliases none _ _).trans
      (expr_aliases registers a s)), emit_result (some name) _ _⟩
  | bin p op ordinary a b =>
    exact ⟨none, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      (expr_aliases registers a s)), emit_result (some name) _ _⟩
  | concat p a b bound =>
    exact ⟨none, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      (expr_aliases registers a s)), emit_result (some name) _ _⟩
  | icmp p pred a b =>
    exact ⟨none, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      (expr_aliases registers a s)), emit_result (some name) _ _⟩
  | mux p c a b =>
    exact ⟨none, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      ((expr_aliases registers a _).trans (expr_aliases registers c s))),
      emit_result (some name) _ _⟩
  | extract p a lo count bound =>
    exact ⟨none, (emit_aliases (some name) _ _).trans (expr_aliases registers a s),
      emit_result (some name) _ _⟩
  | replicate p a count bound =>
    exact ⟨none, (emit_aliases (some name) _ _).trans (expr_aliases registers a s),
      emit_result (some name) _ _⟩
  | @read width depth p memory found addr =>
    have walk := expr_aliases registers addr (reserve s memory)
    let index := (s.readCounts.lookup memory).getD 0
    cases hw : Lower.expr registers addr none (reserve s memory) with
    | mk a walked =>
    rw [hw] at walk
    have guarded := inRange_aliases depth a (record walked ⟨memory, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨memory, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded
    rw [read_eq registers p memory found addr (some name) s a walked hw guard state hg]
    have base : state.aliases = s.aliases := guarded.trans walk
    cases guard with
    | none =>
      refine ⟨some s!"{memory}.r{index}_data", ?_, rfl⟩
      change (state.aliases.insert name _) = _
      rw [base]
      rfl
    | some ok =>
      exact ⟨none, (emit_aliases (some name) _ _).trans ((emit_aliases none _ _).trans base),
        emit_result (some name) _ _⟩

theorem statement_named_result (registers : List String) (stmt : Typed.Stmt ctx ports)
    (s : Lower.State) (name : String) (named : LetName stmt = some name) : ∃ v,
      (Lower.statement registers stmt s).2.aliases = withAlias s.aliases name v ∧
      ResultAlias (letResult registers stmt s) name v := by
  cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
  all_goals subst named
  case let_ p n w e | assign p n w target e =>
    obtain ⟨v, eq, result⟩ := expr_named_result registers e n s
    exact ⟨v, eq, result⟩

theorem statements_named_results (registers : List String)
    (stmts : List (Typed.Stmt ctx ports)) (s : Lower.State)
    (unique : (stmts.filterMap LetName).Nodup)
    (clean : ∀ n ∈ stmts.filterMap LetName, s.aliases[n]? = none) :
    let t := ((do for stmt in stmts do Lower.statement registers stmt) s).2
    ∀ stmt ∈ stmts, ∀ name, LetName stmt = some name → ∃ s',
      Grows (Lower.statement registers stmt s').2 t ∧
      ResultAlias (letResult registers stmt s') name t.aliases[name]? := by
  induction stmts generalizing s with
  | nil => intro t stmt hs; cases hs
  | cons stmt stmts ih =>
    intro t st hs name named
    rw [show t = _ from run_cons registers stmt stmts s]
    let first := (Lower.statement registers stmt s).2
    cases hn : LetName stmt with
    | none =>
      have same := statement_aliases_other registers stmt s hn
      simp only [List.filterMap_cons, hn] at unique clean
      have clean' : ∀ n ∈ stmts.filterMap LetName, first.aliases[n]? = none := fun n hn' => by
        change (Lower.statement registers stmt s).2.aliases[n]? = none
        rw [same]
        exact clean n hn'
      rcases List.mem_cons.mp hs with rfl | hs
      · rw [hn] at named
        cases named
      · exact ih first unique clean' st hs name named
    | some other =>
      obtain ⟨v, eq, result⟩ := statement_named_result registers stmt s other hn
      simp only [List.filterMap_cons, hn, List.nodup_cons, List.mem_cons,
        forall_eq_or_imp] at unique clean
      have keep (k : String) (ne : k ≠ other) : first.aliases[k]? = s.aliases[k]? := by
        change (Lower.statement registers stmt s).2.aliases[k]? = _
        rw [eq]
        cases v with
        | none => rfl
        | some x =>
          simp only [withAlias, Std.HashMap.getElem?_insert,
            show (other == k) = false from beq_eq_false_iff_ne.mpr (Ne.symm ne)]
          rfl
      have clean' : ∀ n ∈ stmts.filterMap LetName, first.aliases[n]? = none := fun n hn' => by
        rw [keep n (fun same => unique.1 (same ▸ hn'))]
        exact clean.2 n hn'
      rcases List.mem_cons.mp hs with rfl | hs
      · rw [hn] at named
        cases named
        refine ⟨s, grows_statements registers stmts first, ?_⟩
        rw [(statements_aliases registers stmts first unique.2 clean').1 name unique.1]
        change ResultAlias _ name (Lower.statement registers st s).2.aliases[name]?
        rw [eq]
        cases v with
        | none => simpa [withAlias, clean.1] using result
        | some x => simpa [withAlias] using result
      · exact ih first unique.2 clean' st hs name named

theorem let_results (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (stmt : Typed.Stmt m.ctx m.interfaces)
    (hs : stmt ∈ Lower.statements m) (name : String) (named : LetName stmt = some name) :
    ∃ s, Grows (Lower.statement (Lower.registers m) stmt s).2 (Lower.statementState m) ∧
      rename m name = rename m (letResult (Lower.registers m) stmt s) := by
  obtain ⟨s, grows, result⟩ := statements_named_results (Lower.registers m) (Lower.statements m)
    {} (letNames_nodup raw t h m hm) (fun _ _ => Std.HashMap.getElem?_empty) stmt hs name named
  refine ⟨s, grows, ?_⟩
  change ResultAlias _ name (finalAliases m)[name]? at result
  cases found : (finalAliases m)[name]? with
  | none =>
    rw [found] at result
    change _ = name at result
    rw [result]
  | some v =>
    rw [found] at result
    change v = _ at result
    rw [← result]
    exact rename_alias raw t h m hm name v found

end Silicon.Core.LowerProof
