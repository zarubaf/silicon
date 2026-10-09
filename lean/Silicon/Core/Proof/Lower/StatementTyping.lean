import Silicon.Core.Proof.Lower.Typing
import Silicon.Core.Proof.Lower.Counts

/-!
Each statement types its new ops, ports, and state updates from typed expression results.
-/
namespace Silicon.Core.LowerProof

variable {ctx : Typed.Ctx} (E : Typing ctx)

def StmtLegal : Typed.Stmt ctx ports → Prop
  | .let_ _ _ _ e | .assign _ _ _ _ e | .next _ _ _ _ e => Legal e
  | .reg _ _ _ _ reset => ∀ r ∈ reset.toList, Legal r.signal ∧ Legal r.value
  | .write _ _ _ _ _ _ a d en => Legal a ∧ Legal d ∧ Legal en
  | .inst _ _ _ inputs => ∀ i ∈ inputs, Legal i.2
  | .mem .. => True

def Typing.StmtFresh : Typed.Stmt ctx ports → Prop
  | .let_ _ name _ e | .assign _ name _ _ e => NotAliased e → E.rename name = name
  | _ => True

def RegWidth : Typed.Stmt ctx ports → Prop
  | .reg _ name w _ _ => ctx.lookup (.name name) = some (.value (.bits w))
  | _ => True

/-- An instance op types its operands when each argument has its port type. -/
def Typing.GoodArgs (args : List (String × String × Mlir.Ty)) : Prop :=
  ∀ arg ∈ args, E.Has arg.2.1 arg.2.2

theorem Typing.step_mapM (xs : List α) (f : α → Lower.Build β) (P : β → Prop)
    (h : ∀ x ∈ xs, E.Step (f x) True P) :
    E.Step (xs.mapM f) True (fun ys => ∀ y ∈ ys, P y) := by
  induction xs with
  | nil =>
    rw [List.mapM_nil]
    exact E.step_weaken _ _ _ _ _ (E.step_pure [] True) id
      (fun _ _ h y hy => by rw [h.1] at hy; cases hy)
  | cons x xs ih =>
    rw [List.mapM_cons]
    apply E.step_bind _ _ _ _ _ (h x (List.mem_cons_self ..))
    intro y
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha))) (fun _ => trivial) (fun _ _ h => h)))
    intro ys
    exact E.step_weaken _ _ _ _ _ (E.step_pure (y :: ys) _) id
      (fun _ _ h z hz => by
        rw [h.1] at hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact h.2.1
        · exact h.2.2 z hz)

theorem Typing.step_statement (stmt : Typed.Stmt ctx ports) (legal : StmtLegal stmt)
    (fresh : E.StmtFresh stmt) (width : RegWidth stmt) :
    E.Step (Lower.statement E.registers stmt) True (fun _ => True) := by
  cases stmt with
  | let_ p name w e | assign p name w target e =>
    simp only [Lower.statement]
    apply E.step_bind _ _ _ _ _ (E.step_expr e legal (some name)
      (fun n h ne => Option.some.inj h ▸ fresh ne))
    intro _
    exact E.step_weaken _ _ _ _ _ (E.step_pure () _) (fun _ => trivial) (fun _ _ _ => trivial)
  | next p name w target e =>
    simp only [Lower.statement]
    apply E.step_bind _ _ _ _ _ (E.step_expr e legal none (fun _ h => nomatch h))
    intro next s
    refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _,
      List.suffix_refl _⟩, fun _ hn => ⟨⟨fun _ h => Or.inl h, fun _ h => Or.inl h,
        fun _ h => Or.inl h, fun x h => ?_, fun _ h => Or.inl h⟩, trivial⟩⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr ⟨w, target, hn⟩
    · exact Or.inl h
  | mem => exact E.step_weaken _ _ _ _ _ (E.step_pure () True) id (fun _ _ _ => trivial)
  | reg p name w clk reset =>
    simp only [Lower.statement]
    have record (opt : Option (String × String)) :
        E.Step (modify fun s : Lower.State => { s with resets := (name, opt) :: s.resets })
          (∀ pair ∈ opt.toList, E.Has pair.1 (.int 1) ∧ E.Has pair.2 (.int w))
          (fun _ => True) := by
      intro s
      refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
        List.suffix_cons _ _⟩, fun _ good => ⟨⟨fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun _ h => Or.inl h, fun _ h => Or.inl h, fun x h => ?_⟩, trivial⟩⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨w, width, good⟩
      · exact Or.inl h
    have values : E.Step (reset.mapM fun r => do
        let signal ← Lower.expr E.registers r.signal none
        let value ← Lower.expr E.registers r.value none
        return (signal, value)) True
        (fun opt => ∀ pair ∈ opt.toList, E.Has pair.1 (.int 1) ∧ E.Has pair.2 (.int w)) := by
      cases reset with
      | none =>
        rw [Option.mapM_none]
        exact E.step_weaken _ _ _ _ _ (E.step_pure none True) id
          (fun _ _ h pair hp => by rw [h.1] at hp; cases hp)
      | some r =>
        have hr := legal r (List.mem_singleton_self r)
        rw [Option.mapM_some, map_eq_pure_bind]
        have inner : E.Step (do
            let signal ← Lower.expr E.registers r.signal none
            let value ← Lower.expr E.registers r.value none
            return (signal, value)) True
            (fun pair => E.Has pair.1 (.int 1) ∧ E.Has pair.2 (.int w)) := by
          apply E.step_bind _ _ _ _ _ (E.step_expr r.signal hr.1 none (fun _ h => nomatch h))
          intro signal
          apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
            (E.step_expr r.value hr.2 none (fun _ h => nomatch h)) (fun _ => trivial)
            (fun _ _ h => h)))
          intro value
          exact E.step_weaken _ _ _ _ _ (E.step_pure (signal, value) _) id
            (fun _ _ h => by rw [h.1]; exact h.2)
        apply E.step_bind _ _ _ _ _ inner
        intro pair
        exact E.step_weaken _ _ _ _ _ (E.step_pure (some pair) _) id
          (fun _ _ h x hx => by
            rw [h.1] at hx
            cases List.mem_singleton.mp hx
            exact h.2)
    apply E.step_bind _ _ _ _ _ values
    intro opt
    exact record opt
  | write p name index w depth target addr data enable =>
    simp only [Lower.statement]
    apply E.step_bind _ _ _ _ _ (E.step_expr addr legal.1 none (fun _ h => nomatch h))
    intro a
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (E.step_expr data legal.2.1 none (fun _ h => nomatch h)) (fun _ => trivial)
      (fun _ _ h => h)))
    intro d
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (E.step_expr enable legal.2.2 none (fun _ h => nomatch h)) (fun _ => trivial)
      (fun _ _ h => h)))
    intro en
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (E.step_inRange depth a) (fun h => h.1.1) (fun _ _ h => h)))
    intro guard
    have finish (enabled : String) :
        E.Step (modify fun s : Lower.State =>
          { s with writes := ⟨name, index, a, d, enabled⟩ :: s.writes })
          ((E.Has a (.int (Typed.addressWidth depth)) ∧ E.Has d (.int w)) ∧
            E.Has enabled (.int 1)) (fun _ => True) := by
      intro s
      refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _,
        List.suffix_refl _⟩, fun _ good => ⟨⟨fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun x h => ?_, fun _ h => Or.inl h, fun _ h => Or.inl h⟩, trivial⟩⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨w, depth, target, good.1.1, good.1.2, good.2⟩
      · exact Or.inl h
    cases guard with
    | none =>
      apply E.step_bind _ _ _ _ _ (E.step_pure en _)
      intro enabled
      exact E.step_weaken _ _ _ _ _ (finish enabled) (fun h => by rw [h.1]; exact h.2.1)
        (fun _ _ h => h)
    | some ok =>
      apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_emit none (.comb .and en ok 1)
        (.int 1) rfl _ (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1.2, h.2⟩⟩)
        (fun _ _ h => nomatch h)))
      intro enabled
      exact E.step_weaken _ _ _ _ _ (finish enabled) (fun h => ⟨h.1.1.1, h.2⟩)
        (fun _ _ h => h)
  | inst p name child inputs =>
    simp only [Lower.statement]
    apply E.step_bind _ _ _ _ _ (E.step_mapM inputs _ (fun arg => E.Has arg.2.1 arg.2.2)
      (fun i hi => by
        apply E.step_bind _ _ _ _ _ (E.step_expr i.2 (legal i hi) none (fun _ h => nomatch h))
        intro value
        exact E.step_weaken _ _ _ _ _ (E.step_pure _ _) id
          (fun _ _ h => by rw [h.1]; exact h.2)))
    intro args s
    refine ⟨grows_push _ _, fun _ good => ⟨⟨fun entry h => ?_, fun _ h => Or.inl h,
      fun _ h => Or.inl h, fun _ h => Or.inl h, fun _ h => Or.inl h⟩, trivial⟩⟩
    change entry ∈ (s.body.push _).toList at h
    rw [Array.toList_push] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · cases List.mem_singleton.mp h
      refine Or.inr ⟨by simp [Mlir.Op.resultTypes], trivial, ?_⟩
      intro o ho
      simp only [Mlir.Op.operands, List.mem_map, List.mem_filterMap] at ho
      obtain ⟨arg, ⟨port, _, found⟩, rfl⟩ := ho
      split at found
      · exact good arg (List.mem_of_find?_eq_some found)
      · cases found

theorem Typing.step_statements (stmts : List (Typed.Stmt ctx ports))
    (conditions : ∀ stmt ∈ stmts, StmtLegal stmt ∧ E.StmtFresh stmt ∧ RegWidth stmt)
    (s : Lower.State) :
    let t := ((do for stmt in stmts do Lower.statement E.registers stmt) s).2
    Grows s t ∧ (Grows t E.final → E.NewGood s t) := by
  induction stmts generalizing s with
  | nil =>
    intro t
    rw [show t = s from run_nil E.registers s]
    exact ⟨Grows.refl s, fun _ => E.newGood_refl s⟩
  | cons stmt stmts ih =>
    intro t
    rw [show t = _ from run_cons E.registers stmt stmts s]
    have c := conditions stmt (List.mem_cons_self ..)
    obtain ⟨g₁, t₁⟩ := E.step_statement stmt c.1 c.2.1 c.2.2 s
    obtain ⟨g₂, t₂⟩ := ih (fun x hx => conditions x (List.mem_cons_of_mem _ hx))
      (Lower.statement E.registers stmt s).2
    exact ⟨g₁.trans g₂, fun grows => E.newGood_trans (t₁ (g₂.trans grows) trivial).1
      (t₂ grows)⟩

end Silicon.Core.LowerProof
