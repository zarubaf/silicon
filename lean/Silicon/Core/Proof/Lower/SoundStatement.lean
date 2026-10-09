import Silicon.Core.Proof.Lower.Sound

/-!
Each state update and instance op of the final build state carries the core values of the
statement that adds it.
-/
namespace Silicon.Core.LowerProof

open Semantics

variable {ctx : Typed.Ctx} {ports : String → List Port} (M : Meaning ctx)
  (stmts : List (Typed.Stmt ctx ports))

def Meaning.core (e : Typed.Expr ctx ty) : TyValue ty := evalExpr M.values M.memories e

def Meaning.GoodNext (next : String × String) : Prop :=
  ∃ p w target e, Typed.Stmt.next p next.1 w target e ∈ stmts ∧
    M.env next.2 = some (.bits w (M.core e))

def Meaning.ResetValues : Option (Typed.Reset ctx w) → Option (String × String) → Prop
  | none, none => True
  | some r, some (signal, value) => M.env signal = some (.bits 1 (M.core r.signal)) ∧
      M.env value = some (.bits w (M.core r.value))
  | _, _ => False

def Meaning.GoodReset (reset : String × Option (String × String)) : Prop :=
  ∃ p w clk r, Typed.Stmt.reg p reset.1 w clk r ∈ stmts ∧ M.ResetValues r reset.2

def Meaning.GoodWrite (write : Lower.WritePort) : Prop :=
  ∃ p w depth target addr data enable,
    Typed.Stmt.write p write.memory write.index w depth target addr data enable ∈ stmts ∧
    M.env write.addr = some (.bits _ (M.core addr)) ∧
    M.env write.data = some (.bits w (M.core data)) ∧
    M.env write.enable = some (.bits 1
      (M.core enable &&& BitVec.ofBool ((M.core addr).toNat < depth)))

/-- The arguments of an instance follow its connections in source order. -/
def Meaning.ArgsMatch
    (inputs : List ((p : {p : Port // p ∈ ports child}) × Typed.Expr ctx p.val.ty))
    (args : List (String × String × Mlir.Ty)) : Prop :=
  args.length = inputs.length ∧ ∀ pair ∈ inputs.zip args,
    pair.2.1 = pair.1.1.val.name ∧ pair.2.2.2 = Lower.type pair.1.1.val.ty ∧
    M.env pair.2.2.1 = some (coreValue _ (M.core pair.1.2))

def Meaning.GoodInst (entry : List String × Mlir.Op) : Prop :=
  ∀ inst callee args results, entry.2 = .instance inst callee args results →
    ∃ p inputs args₀, Typed.Stmt.inst p inst callee inputs ∈ stmts ∧
      M.ArgsMatch inputs args₀ ∧ args = instArgs ports callee args₀ ∧
      results = instResults ports callee ∧
      entry.1 = (instResults ports callee).map (fun q => s!"{inst}.{q.1}")

def Meaning.NewGood (s t : Lower.State) : Prop :=
  (∀ e ∈ t.body.toList, e ∈ s.body.toList ∨ M.GoodInst stmts e) ∧
  (∀ w ∈ t.writes, w ∈ s.writes ∨ M.GoodWrite stmts w) ∧
  (∀ n ∈ t.nexts, n ∈ s.nexts ∨ M.GoodNext stmts n) ∧
  (∀ r ∈ t.resets, r ∈ s.resets ∨ M.GoodReset stmts r)

private theorem or_chain {P : α → Prop} {xs ys zs : List α}
    (ab : ∀ x ∈ ys, x ∈ xs ∨ P x) (bc : ∀ x ∈ zs, x ∈ ys ∨ P x) : ∀ x ∈ zs, x ∈ xs ∨ P x := by
  intro x h
  rcases bc x h with h | h
  · exact ab x h
  · exact Or.inr h

theorem Meaning.newGood_refl (s : Lower.State) : M.NewGood stmts s s :=
  ⟨fun _ h => Or.inl h, fun _ h => Or.inl h, fun _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem Meaning.newGood_trans {a b c : Lower.State} (ab : M.NewGood stmts a b)
    (bc : M.NewGood stmts b c) : M.NewGood stmts a c :=
  ⟨or_chain ab.1 bc.1, or_chain ab.2.1 bc.2.1, or_chain ab.2.2.1 bc.2.2.1,
    or_chain ab.2.2.2 bc.2.2.2⟩

/-- The register updates of a state. An expression leaves them alone. -/
def Updates (s : Lower.State) :
    List (String × String) × List (String × Option (String × String)) :=
  (s.nexts, s.resets)

theorem emit_updates (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    Updates (Lower.emit dest op s).2 = Updates s := by
  cases dest <;> rfl

theorem named_updates (dest : Option String) (value : String) (s : Lower.State) :
    Updates (Lower.named dest value s).2 = Updates s := by
  cases dest <;> rfl

theorem inRange_updates (depth : Nat) (addr : String) (s : Lower.State) :
    Updates (Lower.inRange depth addr s).2 = Updates s := by
  rw [inRange_state]
  split
  · rfl
  · simp only [emit_updates]

theorem expr_updates (registers : List String) (e : Typed.Expr ctx ty) (dest : Option String)
    (s : Lower.State) : Updates (Lower.expr registers e dest s).2 = Updates s := by
  induction e generalizing s dest with
  | ref p node found => exact named_updates dest _ s
  | clock p name found => rfl
  | const p w v => exact emit_updates dest _ s
  | un p op a ih =>
    cases op
    exact (emit_updates dest _ _).trans ((emit_updates none _ _).trans (ih none s))
  | bin p op ordinary a b ia ib =>
    exact (emit_updates dest _ _).trans ((ib none _).trans (ia none s))
  | concat p a b bound ia ib =>
    exact (emit_updates dest _ _).trans ((ib none _).trans (ia none s))
  | icmp p pred a b ia ib =>
    exact (emit_updates dest _ _).trans ((ib none _).trans (ia none s))
  | mux p c a b ic ia ib =>
    exact (emit_updates dest _ _).trans ((ib none _).trans ((ia none _).trans (ic none s)))
  | extract p a lo count bound ih => exact (emit_updates dest _ _).trans (ih none s)
  | replicate p a count bound ih => exact (emit_updates dest _ _).trans (ih none s)
  | @read width depth p name found addr ih =>
    have walk := ih none (reserve s name)
    cases hw : Lower.expr registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    let index := (s.readCounts.lookup name).getD 0
    have guarded := inRange_updates depth a (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded
    rw [read_eq registers p name found addr dest s a walked hw guard state hg]
    have base : Updates state = Updates s := guarded.trans walk
    cases guard with
    | none => exact (named_updates dest _ _).trans base
    | some ok => exact (emit_updates dest _ _).trans ((emit_updates none _ _).trans base)

/-- An expression step adds plain ops only, and no state update. -/
theorem Meaning.newGood_expr (e : Typed.Expr ctx ty) (dest : Option String) (s : Lower.State) :
    M.NewGood stmts s (Lower.expr M.registers e dest s).2 := by
  obtain ⟨⟨tail, body, plain⟩, _, writes⟩ := exprStep_expr M.registers e dest s
  have updates := expr_updates M.registers e dest s
  simp only [Updates, Prod.mk.injEq] at updates
  refine ⟨fun entry h => ?_, fun _ h => Or.inl (writes ▸ h),
    fun _ h => Or.inl (updates.1 ▸ h), fun _ h => Or.inl (updates.2 ▸ h)⟩
  rw [body] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · refine Or.inr fun inst callee args results same => ?_
    have := plain entry h
    rw [same] at this
    cases this

/-- A statement step: with the final state, its new entries are good and its result holds. -/
def Meaning.SStep (action : Lower.Build α) (pre : Prop) (post : α → Prop) : Prop :=
  ∀ s, Grows s (action s).2 ∧
    (Grows (action s).2 M.final → pre → M.NewGood stmts s (action s).2 ∧ post (action s).1)

theorem Meaning.sstep_bind (a : Lower.Build α) (b : α → Lower.Build β) (p : Prop)
    (q : α → Prop) (r : β → Prop) (ha : M.SStep stmts a p q)
    (hb : ∀ x, M.SStep stmts (b x) (q x) r) : M.SStep stmts (a >>= b) p r := by
  intro s
  obtain ⟨ga, ta⟩ := ha s
  obtain ⟨gb, tb⟩ := hb (a s).1 (a s).2
  refine ⟨ga.trans gb, fun grows hp => ?_⟩
  have first := ta (gb.trans grows) hp
  have second := tb grows first.2
  exact ⟨M.newGood_trans stmts first.1 second.1, second.2⟩

theorem Meaning.sstep_weaken (a : Lower.Build α) (p p' : Prop) (q q' : α → Prop)
    (h : M.SStep stmts a p q) (hp : p' → p) (hq : ∀ x, p' → q x → q' x) :
    M.SStep stmts a p' q' := by
  intro s
  obtain ⟨g, t⟩ := h s
  exact ⟨g, fun grows pre => ⟨(t grows (hp pre)).1, hq _ pre (t grows (hp pre)).2⟩⟩

theorem Meaning.sstep_keep (a : Lower.Build α) (p : Prop) (q : α → Prop)
    (h : M.SStep stmts a p q) : M.SStep stmts a p (fun x => p ∧ q x) :=
  M.sstep_weaken stmts a p p q _ h id (fun _ hp hq => ⟨hp, hq⟩)

theorem Meaning.sstep_pure (x : α) (p : Prop) :
    M.SStep stmts (pure x) p (fun y => y = x ∧ p) :=
  fun s => ⟨Grows.refl s, fun _ hp => ⟨M.newGood_refl stmts s, rfl, hp⟩⟩

theorem Meaning.sstep_expr (e : Typed.Expr ctx ty) (legal : Legal e) (dest : Option String) :
    M.SStep stmts (Lower.expr M.registers e dest) True
      (fun name => M.env name = some (coreValue ty (M.core e))) := by
  intro s
  obtain ⟨g, t⟩ := M.step_expr e legal dest s
  exact ⟨g, fun grows _ => ⟨M.newGood_expr stmts e dest s, t grows trivial⟩⟩

theorem Meaning.sstep_mapM (xs : List α) (f : α → Lower.Build β) (P : α → β → Prop)
    (h : ∀ x ∈ xs, M.SStep stmts (f x) True (P x)) :
    M.SStep stmts (xs.mapM f) True
      (fun ys => ys.length = xs.length ∧ ∀ pair ∈ xs.zip ys, P pair.1 pair.2) := by
  induction xs with
  | nil =>
    rw [List.mapM_nil]
    exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts [] True) id
      (fun _ _ h => by rw [h.1]; exact ⟨rfl, fun _ hp => by cases hp⟩)
  | cons x xs ih =>
    rw [List.mapM_cons]
    apply M.sstep_bind stmts _ _ _ _ _ (h x (List.mem_cons_self ..))
    intro y
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_keep stmts _ _ _ (M.sstep_weaken stmts _ _ _ _ _
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha))) (fun _ => trivial) (fun _ _ h => h)))
    intro ys
    exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts (y :: ys) _) id
      (fun _ _ h => by
        rw [h.1]
        refine ⟨by simp [h.2.2.1], fun pair hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact h.2.1
        · exact h.2.2.2 pair hp)

theorem Meaning.sstep_emit (dest : Option String) (op : Mlir.Op) (value : Mlir.Value)
    (plain : isInstance op = false) (stateless : isCompreg op = false) (p : Prop)
    (eval : p → op.eval M.env = some value) :
    M.SStep stmts (Lower.emit dest op) p (fun name => M.env name = some value) := by
  intro s
  obtain ⟨g, t⟩ := M.step_emit dest op value plain stateless p eval s
  refine ⟨g, fun grows hp => ⟨?_, t grows hp⟩⟩
  obtain ⟨⟨tail, body, plains⟩, _, writes⟩ := exprStep_emit dest op plain s
  have updates := emit_updates dest op s
  simp only [Updates, Prod.mk.injEq] at updates
  refine ⟨fun entry h => ?_, fun _ h => Or.inl (writes ▸ h),
    fun _ h => Or.inl (updates.1 ▸ h), fun _ h => Or.inl (updates.2 ▸ h)⟩
  rw [body] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · refine Or.inr fun inst callee args results same => ?_
    have := plains entry h
    rw [same] at this
    cases this

theorem and_allOnes_one (x : BitVec 1) (b : Bool) (hb : b = true) :
    x &&& BitVec.ofBool b = x := by
  subst hb
  exact BitVec.and_allOnes

theorem Meaning.step_statement (stmt : Typed.Stmt ctx ports) (hs : stmt ∈ stmts)
    (legal : StmtLegal stmt) :
    M.SStep stmts (Lower.statement M.registers stmt) True (fun _ => True) := by
  cases stmt with
  | let_ p name w e | assign p name w target e =>
    simp only [Lower.statement]
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_expr stmts e legal (some name))
    intro _
    exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts () _) (fun _ => trivial)
      (fun _ _ _ => trivial)
  | next p name w target e =>
    simp only [Lower.statement]
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_expr stmts e legal none)
    intro next s
    refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _,
      List.suffix_refl _⟩, fun _ hn => ⟨⟨fun _ h => Or.inl h, fun _ h => Or.inl h,
        fun x h => ?_, fun _ h => Or.inl h⟩, trivial⟩⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr ⟨p, w, target, e, hs, hn⟩
    · exact Or.inl h
  | mem =>
    exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts () True) id (fun _ _ _ => trivial)
  | reg p name w clk reset =>
    simp only [Lower.statement]
    have record (opt : Option (String × String)) :
        M.SStep stmts (modify fun s : Lower.State => { s with resets := (name, opt) :: s.resets })
          (M.ResetValues reset opt) (fun _ => True) := by
      intro s
      refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
        List.suffix_cons _ _⟩, fun _ good => ⟨⟨fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun _ h => Or.inl h, fun x h => ?_⟩, trivial⟩⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨p, w, clk, reset, hs, good⟩
      · exact Or.inl h
    have values : M.SStep stmts (reset.mapM fun r => do
        let signal ← Lower.expr M.registers r.signal none
        let value ← Lower.expr M.registers r.value none
        return (signal, value)) True (fun opt => M.ResetValues reset opt) := by
      cases reset with
      | none =>
        rw [Option.mapM_none]
        exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts none True) id
          (fun _ _ h => by rw [h.1]; trivial)
      | some r =>
        have hr := legal r (List.mem_singleton_self r)
        rw [Option.mapM_some, map_eq_pure_bind]
        have inner : M.SStep stmts (do
            let signal ← Lower.expr M.registers r.signal none
            let value ← Lower.expr M.registers r.value none
            return (signal, value)) True
            (fun pair => M.env pair.1 = some (.bits 1 (M.core r.signal)) ∧
              M.env pair.2 = some (.bits w (M.core r.value))) := by
          apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_expr stmts r.signal hr.1 none)
          intro signal
          apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_keep stmts _ _ _
            (M.sstep_weaken stmts _ _ _ _ _ (M.sstep_expr stmts r.value hr.2 none)
              (fun _ => trivial) (fun _ _ h => h)))
          intro value
          exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts (signal, value) _) id
            (fun _ _ h => by rw [h.1]; exact h.2)
        apply M.sstep_bind stmts _ _ _ _ _ inner
        intro pair
        exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts (some pair) _) id
          (fun _ _ h => by rw [h.1]; exact h.2)
    apply M.sstep_bind stmts _ _ _ _ _ values
    intro opt
    exact record opt
  | write p name index w depth target addr data enable =>
    simp only [Lower.statement]
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_expr stmts addr legal.1 none)
    intro a
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_keep stmts _ _ _ (M.sstep_weaken stmts _ _ _ _ _
      (M.sstep_expr stmts data legal.2.1 none) (fun _ => trivial) (fun _ _ h => h)))
    intro d
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_keep stmts _ _ _ (M.sstep_weaken stmts _ _ _ _ _
      (M.sstep_expr stmts enable legal.2.2 none) (fun _ => trivial) (fun _ _ h => h)))
    intro en
    have guardStep : M.SStep stmts (Lower.inRange depth a)
        (M.env a = some (.bits _ (M.core addr)))
        (fun result => match result with
          | none => depth = 2 ^ Typed.addressWidth depth
          | some ok => M.env ok =
              some (.bits 1 (BitVec.ofBool ((M.core addr).toNat < depth)))) := by
      intro s
      obtain ⟨g, t⟩ := M.step_inRange depth a (M.core addr) s
      refine ⟨g, fun grows hp => ⟨?_, t grows hp⟩⟩
      obtain ⟨⟨tail, body, plain⟩, _, writes⟩ := exprStep_inRange depth a s
      have updates := inRange_updates depth a s
      simp only [Updates, Prod.mk.injEq] at updates
      refine ⟨fun entry h => ?_, fun _ h => Or.inl (writes ▸ h),
        fun _ h => Or.inl (updates.1 ▸ h), fun _ h => Or.inl (updates.2 ▸ h)⟩
      rw [body] at h
      rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · refine Or.inr fun inst callee args results same => ?_
        have := plain entry h
        rw [same] at this
        cases this
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_keep stmts _ _ _ (M.sstep_weaken stmts _ _ _ _ _
      guardStep (fun h => h.1.1) (fun _ _ h => h)))
    intro guard
    have finish (enabled : String) :
        M.SStep stmts (modify fun s : Lower.State =>
          { s with writes := ⟨name, index, a, d, enabled⟩ :: s.writes })
          ((M.env a = some (.bits _ (M.core addr)) ∧
            M.env d = some (.bits w (M.core data))) ∧
            M.env enabled = some (.bits 1
              (M.core enable &&& BitVec.ofBool ((M.core addr).toNat < depth))))
          (fun _ => True) := by
      intro s
      refine ⟨⟨List.prefix_refl _, List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _,
        List.suffix_refl _⟩, fun _ good => ⟨⟨fun _ h => Or.inl h, fun x h => ?_,
          fun _ h => Or.inl h, fun _ h => Or.inl h⟩, trivial⟩⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨p, w, depth, target, addr, data, enable, hs, good.1.1, good.1.2, good.2⟩
      · exact Or.inl h
    cases guard with
    | none =>
      apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_pure stmts en _)
      intro enabled
      refine M.sstep_weaken stmts _ _ _ _ _ (finish enabled) (fun h => ?_) (fun _ _ h => h)
      obtain ⟨same, ⟨⟨ha, hd⟩, he⟩, full⟩ := h
      subst same
      refine ⟨⟨ha, hd⟩, ?_⟩
      rw [he, and_allOnes_one _ _ (decide_eq_true (Nat.lt_of_lt_of_eq (M.core addr).isLt
        full.symm))]
      rfl
    | some ok =>
      apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_keep stmts _ _ _ (M.sstep_emit stmts none
        (.comb .and en ok 1) (.bits 1
          (M.core enable &&& BitVec.ofBool ((M.core addr).toNat < depth))) rfl rfl _
        (fun h => eval_binary M.env .and (by decide) en ok _ _ h.1.2 h.2)))
      intro enabled
      exact M.sstep_weaken stmts _ _ _ _ _ (finish enabled) (fun h => ⟨h.1.1.1, h.2⟩)
        (fun _ _ h => h)
  | inst p name child inputs =>
    simp only [Lower.statement]
    apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_mapM stmts inputs _
      (fun input arg => arg.1 = input.1.val.name ∧ arg.2.2 = Lower.type input.1.val.ty ∧
        M.env arg.2.1 = some (coreValue _ (M.core input.2)))
      (fun i hi => by
        apply M.sstep_bind stmts _ _ _ _ _ (M.sstep_expr stmts i.2 (legal i hi) none)
        intro value
        exact M.sstep_weaken stmts _ _ _ _ _ (M.sstep_pure stmts _ _) id
          (fun _ _ h => by rw [h.1]; exact ⟨rfl, rfl, h.2⟩)))
    intro args s
    refine ⟨grows_push _ _, fun _ good => ⟨⟨fun entry h => ?_, fun _ h => Or.inl h,
      fun _ h => Or.inl h, fun _ h => Or.inl h⟩, trivial⟩⟩
    change entry ∈ (s.body.push _).toList at h
    rw [Array.toList_push] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · cases List.mem_singleton.mp h
      refine Or.inr fun inst callee args' results same => ?_
      simp only [Mlir.Op.instance.injEq] at same
      obtain ⟨rfl, rfl, rfl, rfl⟩ := same
      exact ⟨p, inputs, args, hs, ⟨good.1, fun pair hp => (good.2 pair hp)⟩, rfl, rfl, rfl⟩

theorem Meaning.step_statements (xs : List (Typed.Stmt ctx ports))
    (sub : ∀ x ∈ xs, x ∈ stmts) (legal : ∀ x ∈ xs, StmtLegal x) (s : Lower.State) :
    let t := ((do for stmt in xs do Lower.statement M.registers stmt) s).2
    Grows s t ∧ (Grows t M.final → M.NewGood stmts s t) := by
  induction xs generalizing s with
  | nil =>
    intro t
    rw [show t = s from run_nil M.registers s]
    exact ⟨Grows.refl s, fun _ => M.newGood_refl stmts s⟩
  | cons stmt rest ih =>
    intro t
    rw [show t = _ from run_cons M.registers stmt rest s]
    obtain ⟨g₁, t₁⟩ := M.step_statement stmts stmt (sub stmt (List.mem_cons_self ..))
      (legal stmt (List.mem_cons_self ..)) s
    obtain ⟨g₂, t₂⟩ := ih (fun x hx => sub x (List.mem_cons_of_mem _ hx))
      (fun x hx => legal x (List.mem_cons_of_mem _ hx)) (Lower.statement M.registers stmt s).2
    exact ⟨g₁.trans g₂, fun grows => M.newGood_trans stmts (t₁ (g₂.trans grows) trivial).1
      (t₂ grows)⟩

end Silicon.Core.LowerProof
