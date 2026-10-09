import Silicon.Core.Proof.Lower.Growth

/-!
An expression adds no instance op. Its new read ports use the reserved indices of each memory.
-/
namespace Silicon.Core.LowerProof

def readCount (s : Lower.State) (memory : String) : Nat :=
  (s.readCounts.lookup memory).getD 0

def isInstance : Mlir.Op → Bool
  | .instance .. => true
  | _ => false

def indicesOf (reads : List Lower.ReadPort) (memory : String) : List Nat :=
  (reads.filter (·.memory == memory)).map (·.index)

def ReadsCounted (s t : Lower.State) : Prop :=
  ∃ new, t.reads = new ++ s.reads ∧ ∀ memory, readCount s memory ≤ readCount t memory ∧
    (indicesOf new memory).Perm
      (List.range' (readCount s memory) (readCount t memory - readCount s memory))

/-- New ops are plain, and new read ports take exactly the newly reserved indices. -/
def ExprStep (s t : Lower.State) : Prop :=
  (∃ tail, t.body.toList = s.body.toList ++ tail ∧ ∀ e ∈ tail, isInstance e.2 = false) ∧
  ReadsCounted s t ∧ t.writes = s.writes

private theorem range'_split {a b c : Nat} (ab : a ≤ b) (bc : b ≤ c) :
    List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
  have h := List.range'_append_1 (s := a) (m := b - a) (n := c - b)
  rw [Nat.add_sub_cancel' ab] at h
  rw [h]
  congr 1
  omega

theorem ReadsCounted.refl (s : Lower.State) : ReadsCounted s s :=
  ⟨[], by simp, fun _ => ⟨Nat.le_refl _, by simp [indicesOf]⟩⟩

theorem ReadsCounted.trans {a b c : Lower.State} (ab : ReadsCounted a b)
    (bc : ReadsCounted b c) : ReadsCounted a c := by
  obtain ⟨new₁, h₁, c₁⟩ := ab
  obtain ⟨new₂, h₂, c₂⟩ := bc
  refine ⟨new₂ ++ new₁, by simp [h₂, h₁], fun memory => ?_⟩
  obtain ⟨l₁, p₁⟩ := c₁ memory
  obtain ⟨l₂, p₂⟩ := c₂ memory
  refine ⟨Nat.le_trans l₁ l₂, ?_⟩
  rw [range'_split l₁ l₂]
  simp only [indicesOf, List.filter_append, List.map_append] at p₁ p₂ ⊢
  exact List.perm_append_comm.trans (p₁.append p₂)

theorem ReadsCounted.same {s t : Lower.State} (reads : t.reads = s.reads)
    (counts : t.readCounts = s.readCounts) : ReadsCounted s t :=
  ⟨[], by simp [reads], fun memory => by simp [readCount, counts, indicesOf]⟩

theorem ExprStep.refl (s : Lower.State) : ExprStep s s :=
  ⟨⟨[], by simp, by simp⟩, ReadsCounted.refl s, rfl⟩

theorem ExprStep.same {s t : Lower.State} (tail : List (List String × Mlir.Op))
    (body : t.body.toList = s.body.toList ++ tail) (plain : ∀ e ∈ tail, isInstance e.2 = false)
    (reads : t.reads = s.reads) (counts : t.readCounts = s.readCounts)
    (writes : t.writes = s.writes) : ExprStep s t :=
  ⟨⟨tail, body, plain⟩, ReadsCounted.same reads counts, writes⟩

theorem ExprStep.trans {a b c : Lower.State} (ab : ExprStep a b) (bc : ExprStep b c) :
    ExprStep a c := by
  obtain ⟨⟨xs, hx, px⟩, r₁, w₁⟩ := ab
  obtain ⟨⟨ys, hy, py⟩, r₂, w₂⟩ := bc
  refine ⟨⟨xs ++ ys, by simp [hy, hx], fun e he => ?_⟩, r₁.trans r₂, w₂.trans w₁⟩
  rcases List.mem_append.mp he with he | he
  · exact px e he
  · exact py e he

theorem exprStep_emit (dest : Option String) (op : Mlir.Op) (plain : isInstance op = false)
    (s : Lower.State) : ExprStep s (Lower.emit dest op s).2 :=
  ExprStep.same _ (emit_body dest op s) (by simpa using plain) (by cases dest <;> rfl)
    (emit_readCounts dest op s) (by cases dest <;> rfl)

theorem exprStep_named (dest : Option String) (value : String) (s : Lower.State) :
    ExprStep s (Lower.named dest value s).2 :=
  ExprStep.same [] (by cases dest <;> simp [Lower.named] <;> rfl) (by simp)
    (by cases dest <;> rfl) (named_readCounts dest value s) (by cases dest <;> rfl)

theorem exprStep_inRange (depth : Nat) (addr : String) (s : Lower.State) :
    ExprStep s (Lower.inRange depth addr s).2 := by
  rw [inRange_state]
  split
  · exact ExprStep.refl s
  · exact (exprStep_emit none _ rfl s).trans (exprStep_emit none _ rfl _)

private theorem lookup_insert_other (counts : List (String × Nat)) (memory other : String)
    (n : Nat) (ne : other ≠ memory) :
    ((memory, n) :: counts).lookup other = counts.lookup other := by
  simp [List.lookup, show (other == memory) = false from beq_eq_false_iff_ne.mpr ne]

theorem exprStep_expr (registers : List String) (e : Typed.Expr ctx ty) (dest : Option String)
    (s : Lower.State) : ExprStep s (Lower.expr registers e dest s).2 := by
  induction e generalizing s dest with
  | ref p node found => exact exprStep_named dest _ s
  | clock p name found => exact ExprStep.refl s
  | const p w v => exact exprStep_emit dest _ rfl s
  | un p op a ih =>
    cases op
    exact ((ih none s).trans (exprStep_emit none _ rfl _)).trans (exprStep_emit dest _ rfl _)
  | bin p op ordinary a b ia ib =>
    exact ((ia none s).trans (ib none _)).trans (exprStep_emit dest _ rfl _)
  | concat p a b bound ia ib =>
    exact ((ia none s).trans (ib none _)).trans (exprStep_emit dest _ rfl _)
  | icmp p pred a b ia ib =>
    exact ((ia none s).trans (ib none _)).trans (exprStep_emit dest _ rfl _)
  | mux p c a b ic ia ib =>
    exact (((ic none s).trans (ia none _)).trans (ib none _)).trans (exprStep_emit dest _ rfl _)
  | extract p a lo count bound ih => exact (ih none s).trans (exprStep_emit dest _ rfl _)
  | replicate p a count bound ih => exact (ih none s).trans (exprStep_emit dest _ rfl _)
  | @read width depth p name found addr ih =>
    have walk := ih none (reserve s name)
    cases hw : Lower.expr registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    dsimp only at walk
    let index := (s.readCounts.lookup name).getD 0
    have guarded := exprStep_inRange depth a (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded
    rw [read_eq registers p name found addr dest s a walked hw guard state hg]
    have middle : ExprStep s (record walked ⟨name, index, a⟩) := by
      obtain ⟨⟨tail, body, plain⟩, ⟨new, reads, counts⟩, writes⟩ := walk
      refine ⟨⟨tail, body, plain⟩, ⟨⟨name, index, a⟩ :: new, by simp [record, reads, reserve],
        fun memory => ?_⟩, writes⟩
      obtain ⟨le, perm⟩ := counts memory
      change readCount s memory ≤ readCount walked memory ∧
        (indicesOf (⟨name, index, a⟩ :: new) memory).Perm
          (List.range' (readCount s memory) (readCount walked memory - readCount s memory))
      by_cases same : memory = name
      · subst same
        have reserved : readCount (reserve s memory) memory = index + 1 := by
          simp [readCount, reserve, index]
        have start : readCount s memory = index := rfl
        rw [reserved] at le perm
        rw [start]
        refine ⟨by omega, ?_⟩
        have shape : List.range' index (readCount walked memory - index) =
            index :: List.range' (index + 1) (readCount walked memory - (index + 1)) := by
          rw [show readCount walked memory - index =
            (readCount walked memory - (index + 1)) + 1 by omega]
          rfl
        rw [shape]
        simpa [indicesOf] using perm
      · have other : readCount (reserve s name) memory = readCount s memory := by
          simp [readCount, reserve, lookup_insert_other _ _ _ _ same]
        rw [other] at le perm
        refine ⟨le, ?_⟩
        have skip : indicesOf (⟨name, index, a⟩ :: new) memory = indicesOf new memory := by
          simp [indicesOf, show (name == memory) = false from
            beq_eq_false_iff_ne.mpr (Ne.symm same)]
        rw [skip]
        exact perm
    have base := middle.trans guarded
    cases guard with
    | none => exact base.trans (exprStep_named dest _ _)
    | some ok =>
      exact (base.trans (exprStep_emit none _ rfl _)).trans (exprStep_emit dest _ rfl _)

def instName (entry : List String × Mlir.Op) : Option String :=
  match entry.2 with
  | .instance inst .. => some inst
  | _ => none

def stmtInstances : Typed.Stmt ctx ports → List String
  | .inst _ name .. => [name]
  | _ => []

def stmtWrites : Typed.Stmt ctx ports → List (String × Nat)
  | .write _ name index .. => [(name, index)]
  | _ => []

def instResults (ports : String → List Port) (child : String) : List (String × Mlir.Ty) :=
  (ports child).filterMap fun p =>
    if p.dir == .output then some (p.name, Lower.type p.ty) else none

def instArgs (ports : String → List Port) (child : String)
    (args : List (String × String × Mlir.Ty)) : List (String × String × Mlir.Ty) :=
  (ports child).filterMap fun p =>
    if p.dir == .input then args.find? (fun arg => arg.1 == p.name) else none

/-- The instance op of a statement. Only its argument values depend on the build. -/
def InstShape : Typed.Stmt ctx ports → (List String × Mlir.Op) → Prop
  | .inst _ name child inputs, entry => ∃ args : List (String × String × Mlir.Ty),
      args.map (fun arg => (arg.1, arg.2.2)) =
        inputs.map (fun input => (input.1.val.name, Lower.type input.1.val.ty)) ∧
      entry = ((instResults ports child).map (fun p => s!"{name}.{p.1}"),
        .instance name child (instArgs ports child args) (instResults ports child))
  | _, _ => False

/-- A statement adds its own instance op and write port, and only reserved read ports. -/
def StmtStep (stmt : Typed.Stmt ctx ports) (s t : Lower.State) : Prop :=
  (∃ tail, t.body.toList = s.body.toList ++ tail ∧
    tail.filterMap instName = stmtInstances stmt ∧
    ∀ e ∈ tail, isInstance e.2 = true → InstShape stmt e) ∧
  ReadsCounted s t ∧
  ∃ new, t.writes = new ++ s.writes ∧ new.map (fun w => (w.memory, w.index)) = stmtWrites stmt

theorem ExprStep.plain_nil {s t : Lower.State} (h : ExprStep s t) :
    ∃ tail, t.body.toList = s.body.toList ++ tail ∧ tail.filterMap instName = [] ∧
      ∀ e ∈ tail, isInstance e.2 = false := by
  obtain ⟨⟨tail, body, plain⟩, _⟩ := h
  refine ⟨tail, body, List.filterMap_eq_nil_iff.mpr fun e he => ?_, plain⟩
  have := plain e he
  unfold instName
  unfold isInstance at this
  split <;> simp_all

theorem ExprStep.keep {s t : Lower.State} (body : t.body = s.body) (reads : t.reads = s.reads)
    (counts : t.readCounts = s.readCounts) (writes : t.writes = s.writes) : ExprStep s t :=
  ExprStep.same [] (by rw [body, List.append_nil]) (by simp) reads counts writes

theorem stmtStep_of_expr {stmt : Typed.Stmt ctx ports} {s t : Lower.State} (h : ExprStep s t)
    (insts : stmtInstances stmt = []) (writes : stmtWrites stmt = []) : StmtStep stmt s t := by
  obtain ⟨tail, body, none, plain⟩ := h.plain_nil
  exact ⟨⟨tail, body, none.trans insts.symm, fun e he hi => by simp [plain e he] at hi⟩,
    h.2.1, [], by simp [h.2.2], by simp [writes]⟩

theorem exprStep_mapM (xs : List α) (f : α → Lower.Build β) (s : Lower.State)
    (step : ∀ x ∈ xs, ∀ state, ExprStep state (f x state).2) : ExprStep s (xs.mapM f s).2 := by
  induction xs generalizing s with
  | nil => exact ExprStep.refl s
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact (step x (List.mem_cons_self ..) s).trans
      (ih _ (fun a ha => step a (List.mem_cons_of_mem _ ha)))

theorem mapM_results (xs : List α) (f : α → Lower.Build β) (g : β → γ) (k : α → γ)
    (same : ∀ x s, g (f x s).1 = k x) (s : Lower.State) :
    (xs.mapM f s).1.map g = xs.map k := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure]
    cases hx : f x s with
    | mk y s₁ =>
      cases hs : List.mapM f xs s₁ with
      | mk ys s₂ =>
        have hy := same x s
        have hys := ih s₁
        rw [hx] at hy
        rw [hs] at hys
        simp only [List.map_cons, ← hy, ← hys]
        rw [hs]
        rfl

theorem statement_step (registers : List String) (stmt : Typed.Stmt ctx ports)
    (s : Lower.State) : StmtStep stmt s (Lower.statement registers stmt s).2 := by
  cases stmt with
  | let_ p name w e | assign p name w target e =>
    exact stmtStep_of_expr (exprStep_expr registers e (some name) s) rfl rfl
  | next p name w target e =>
    have h := exprStep_expr registers e none s
    exact stmtStep_of_expr (h.trans (ExprStep.keep rfl rfl rfl rfl)) rfl rfl
  | mem => exact stmtStep_of_expr (ExprStep.refl s) rfl rfl
  | reg p name w clk reset =>
    cases reset with
    | none => exact stmtStep_of_expr (ExprStep.keep rfl rfl rfl rfl) rfl rfl
    | some r =>
      have h := (exprStep_expr registers r.signal none s).trans
        (exprStep_expr registers r.value none _)
      exact stmtStep_of_expr (h.trans (ExprStep.keep rfl rfl rfl rfl)) rfl rfl
  | write p name index w depth target addr data enable =>
    have base := ((exprStep_expr registers addr none s).trans
      (exprStep_expr registers data none _)).trans (exprStep_expr registers enable none _)
    let a := Lower.expr registers addr none s
    let d := Lower.expr registers data none a.2
    let e := Lower.expr registers enable none d.2
    have guarded := exprStep_inRange depth a.1 e.2
    let finish : String → Lower.Build Unit := fun enable =>
      modify fun state => { state with
        writes := ⟨name, index, a.1, d.1, enable⟩ :: state.writes }
    change StmtStep _ s ((match (Lower.inRange depth a.1 e.2).1 with
      | none => (pure e.1 >>= finish)
      | some ok => (Lower.emit none (.comb .and e.1 ok 1) >>= finish))
        (Lower.inRange depth a.1 e.2).2).2
    cases eq : Lower.inRange depth a.1 e.2 with
    | mk result state =>
      rw [eq] at guarded
      have push (x : Lower.State) (en : String) (h : ExprStep s x) :
          StmtStep (ports := ports) (.write p name index w depth target addr data enable) s
            (finish en x).2 := by
        obtain ⟨tail, body, none, plain⟩ := h.plain_nil
        exact ⟨⟨tail, body, none, fun e he hi => by simp [plain e he] at hi⟩, h.2.1,
          [⟨name, index, a.1, d.1, en⟩], by change _ :: x.writes = _; rw [h.2.2]; rfl, rfl⟩
      cases result with
      | none => exact push _ _ (base.trans guarded)
      | some ok =>
        exact push _ _ ((base.trans guarded).trans (exprStep_emit none _ rfl _))
  | inst p name child inputs =>
    have h := exprStep_mapM inputs (inputArgument registers) s
      (fun i _ state => exprStep_expr registers i.2 none state)
    obtain ⟨tail, body, none, plain⟩ := h.plain_nil
    let args0 := (inputs.mapM (inputArgument registers) s).1
    let entry : List String × Mlir.Op :=
      ((instResults ports child).map (fun p => s!"{name}.{p.1}"),
        .instance name child (instArgs ports child args0) (instResults ports child))
    refine ⟨⟨tail ++ [entry], ?_, ?_, ?_⟩, h.2.1.trans (ReadsCounted.same rfl rfl), [], ?_, rfl⟩
    · change ((inputs.mapM (inputArgument registers) s).2.body.push entry).toList = _
      rw [Array.toList_push, body, List.append_assoc]
    · simp [none, instName, stmtInstances, entry]
    · intro e he hi
      rcases List.mem_append.mp he with he | he
      · simp [plain e he] at hi
      · cases List.mem_singleton.mp he
        refine ⟨args0, ?_, rfl⟩
        apply mapM_results
        intro x s
        rfl
    · exact h.2.2

theorem run_nil (registers : List String) (s : Lower.State) :
    ((do for stmt in ([] : List (Typed.Stmt ctx ports)) do
      Lower.statement registers stmt) s).2 = s := rfl

theorem run_cons (registers : List String) (stmt : Typed.Stmt ctx ports)
    (stmts : List (Typed.Stmt ctx ports)) (s : Lower.State) :
    ((do for stmt in stmt :: stmts do Lower.statement registers stmt) s).2 =
      ((do for stmt in stmts do Lower.statement registers stmt)
        (Lower.statement registers stmt s).2).2 := by
  simp only [List.forIn_cons, bind_assoc, pure_bind]
  rfl

theorem statements_step (registers : List String) (stmts : List (Typed.Stmt ctx ports))
    (s : Lower.State) :
    let t := ((do for stmt in stmts do Lower.statement registers stmt) s).2
    (∃ tail, t.body.toList = s.body.toList ++ tail ∧
      tail.filterMap instName = stmts.flatMap stmtInstances ∧
      ∀ e ∈ tail, isInstance e.2 = true → ∃ stmt ∈ stmts, InstShape stmt e) ∧
    ReadsCounted s t ∧
    ∃ new, t.writes = new ++ s.writes ∧
      (new.map fun w => (w.memory, w.index)).Perm (stmts.flatMap stmtWrites) := by
  induction stmts generalizing s with
  | nil =>
    intro t
    rw [show t = s from run_nil registers s]
    exact ⟨⟨[], by simp, rfl, by simp⟩, ReadsCounted.refl s, [], by simp, by simp⟩
  | cons stmt stmts ih =>
    intro t
    rw [show t = _ from run_cons registers stmt stmts s]
    obtain ⟨⟨xs, hx, ix, sx⟩, rx, ws, hw, kw⟩ := statement_step registers stmt s
    obtain ⟨⟨ys, hy, iy, sy⟩, ry, vs, hv, kv⟩ := ih (Lower.statement registers stmt s).2
    refine ⟨⟨xs ++ ys, by rw [hy, hx, List.append_assoc], ?_, ?_⟩, rx.trans ry, vs ++ ws,
      by rw [hv, hw, List.append_assoc], ?_⟩
    · rw [List.filterMap_append, ix, iy, List.flatMap_cons]
    · intro e he hi
      rcases List.mem_append.mp he with he | he
      · exact ⟨stmt, List.mem_cons_self .., sx e he hi⟩
      · obtain ⟨st, hs, shape⟩ := sy e he hi
        exact ⟨st, List.mem_cons_of_mem _ hs, shape⟩
    · rw [List.map_append, List.flatMap_cons, kw]
      exact List.perm_append_comm.trans (List.Perm.append_left _ kv)

end Silicon.Core.LowerProof
