import Silicon.Core.Proof.Lower.Defs

/-!
A build step only appends ops and ports. Only a named statement result adds an alias.
-/
namespace Silicon.Core.LowerProof

structure Grows (s t : Lower.State) : Prop where
  body : s.body.toList <+: t.body.toList
  reads : s.reads <:+ t.reads
  writes : s.writes <:+ t.writes
  nexts : s.nexts <:+ t.nexts
  resets : s.resets <:+ t.resets

theorem Grows.refl (s : Lower.State) : Grows s s :=
  ⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
    List.suffix_refl _⟩

theorem Grows.trans {a b c : Lower.State} (ab : Grows a b) (bc : Grows b c) : Grows a c :=
  ⟨ab.body.trans bc.body, ab.reads.trans bc.reads, ab.writes.trans bc.writes,
    ab.nexts.trans bc.nexts, ab.resets.trans bc.resets⟩

theorem grows_of {s t : Lower.State} (tail : List (List String × Mlir.Op))
    (body : t.body.toList = s.body.toList ++ tail) (reads : t.reads = s.reads)
    (writes : t.writes = s.writes) (nexts : t.nexts = s.nexts) (resets : t.resets = s.resets) :
    Grows s t :=
  ⟨⟨tail, body.symm⟩, reads ▸ List.suffix_refl _, writes ▸ List.suffix_refl _,
    nexts ▸ List.suffix_refl _, resets ▸ List.suffix_refl _⟩

theorem grows_push (s : Lower.State) (entry : List String × Mlir.Op) :
    Grows s { s with body := s.body.push entry } :=
  grows_of [entry] (Array.toList_push ..) rfl rfl rfl rfl

theorem emit_body (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    (Lower.emit dest op s).2.body.toList =
      s.body.toList ++ [([dest.getD s!"silicon_t{s.nextTemp}"], op)] := by
  cases dest <;> exact Array.toList_push ..

theorem emit_result (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    (Lower.emit dest op s).1 = dest.getD s!"silicon_t{s.nextTemp}" := by
  cases dest <;> rfl

theorem emit_nextTemp (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    (Lower.emit dest op s).2.nextTemp = if dest.isSome then s.nextTemp else s.nextTemp + 1 := by
  cases dest <;> rfl

theorem grows_emit (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    Grows s (Lower.emit dest op s).2 := by
  apply grows_of _ (emit_body dest op s) <;> cases dest <;> rfl

theorem emit_aliases (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    (Lower.emit dest op s).2.aliases = s.aliases := by
  cases dest <;> rfl

theorem emit_readCounts (dest : Option String) (op : Mlir.Op) (s : Lower.State) :
    (Lower.emit dest op s).2.readCounts = s.readCounts := by
  cases dest <;> rfl

theorem named_aliases (dest : Option String) (value : String) (s : Lower.State) :
    (Lower.named dest value s).2.aliases = match dest with
      | some name => s.aliases.insert name value
      | none => s.aliases := by
  cases dest <;> rfl

theorem named_result (dest : Option String) (value : String) (s : Lower.State) :
    (Lower.named dest value s).1 = value := by
  cases dest <;> rfl

theorem grows_named (dest : Option String) (value : String) (s : Lower.State) :
    Grows s (Lower.named dest value s).2 := by
  apply grows_of [] <;> cases dest <;> simp [Lower.named] <;> rfl

theorem named_readCounts (dest : Option String) (value : String) (s : Lower.State) :
    (Lower.named dest value s).2.readCounts = s.readCounts := by
  cases dest <;> rfl

theorem inRange_state (depth : Nat) (addr : String) (s : Lower.State) :
    (Lower.inRange depth addr s).2 =
      if depth = 2 ^ Typed.addressWidth depth then s else
        let bound := Lower.emit none (.constant (Typed.addressWidth depth) depth) s
        (Lower.emit none (.icmp .ult addr bound.1 (Typed.addressWidth depth)) bound.2).2 := by
  unfold Lower.inRange
  by_cases full : depth = 2 ^ Typed.addressWidth depth
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = true from beq_iff_eq.mpr full,
      ↓reduceIte, ite_eq_left_of_eq_true _ _ (eq_true full)]
    rfl
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = false from by simp [full],
      Bool.false_eq_true, ↓reduceIte, ite_eq_right_of_eq_false _ _ (eq_false full)]
    rfl

theorem inRange_result (depth : Nat) (addr : String) (s : Lower.State) :
    (Lower.inRange depth addr s).1 =
      if depth = 2 ^ Typed.addressWidth depth then none else
        let bound := Lower.emit none (.constant (Typed.addressWidth depth) depth) s
        some (Lower.emit none (.icmp .ult addr bound.1 (Typed.addressWidth depth)) bound.2).1 := by
  unfold Lower.inRange
  by_cases full : depth = 2 ^ Typed.addressWidth depth
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = true from beq_iff_eq.mpr full,
      ↓reduceIte, ite_eq_left_of_eq_true _ _ (eq_true full)]
    rfl
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = false from by simp [full],
      Bool.false_eq_true, ↓reduceIte, ite_eq_right_of_eq_false _ _ (eq_false full)]
    rfl

theorem grows_inRange (depth : Nat) (addr : String) (s : Lower.State) :
    Grows s (Lower.inRange depth addr s).2 := by
  rw [inRange_state]
  split
  · exact Grows.refl s
  · exact (grows_emit _ _ s).trans (grows_emit _ _ _)

theorem inRange_aliases (depth : Nat) (addr : String) (s : Lower.State) :
    (Lower.inRange depth addr s).2.aliases = s.aliases := by
  rw [inRange_state]
  split
  · rfl
  · simp only [emit_aliases]

def readTail (dest : Option String) (data : String) (width : Nat) :
    Option String → Lower.Build String
  | none => Lower.named dest data
  | some ok => do
    let zero ← Lower.emit none (.constant width 0)
    Lower.emit dest (.mux ok data zero (.int width))

def reserve (s : Lower.State) (name : String) : Lower.State :=
  { s with readCounts := (name, (s.readCounts.lookup name).getD 0 + 1) :: s.readCounts }

def record (walked : Lower.State) (r : Lower.ReadPort) : Lower.State :=
  { walked with reads := r :: walked.reads }

theorem read_eq (registers : List String) (p : Pos) (name : String)
    (found : ctx.lookup (.name name) = some (.memory width depth))
    (addr : Typed.Expr ctx (.bits (Typed.addressWidth depth))) (dest : Option String)
    (s : Lower.State) (a : String) (walked : Lower.State)
    (hw : Lower.expr registers addr none (reserve s name) = (a, walked))
    (guard : Option String) (guarded : Lower.State)
    (hg : Lower.inRange depth a (record walked ⟨name, (s.readCounts.lookup name).getD 0, a⟩) =
      (guard, guarded)) :
    Lower.expr registers (.read p name found addr) dest s =
      readTail dest s!"{name}.r{(s.readCounts.lookup name).getD 0}_data" width guard guarded := by
  simp only [Lower.expr, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  simp only [reserve, record] at hw hg
  rw [hw]
  dsimp only
  rw [hg]
  cases guard <;> rfl

theorem grows_reserve (s : Lower.State) (name : String) : Grows s (reserve s name) :=
  grows_of [] (by simp [reserve]) rfl rfl rfl rfl

theorem grows_record (s : Lower.State) (r : Lower.ReadPort) : Grows s (record s r) :=
  ⟨List.prefix_refl _, List.suffix_cons _ _, List.suffix_refl _, List.suffix_refl _,
    List.suffix_refl _⟩

theorem grows_expr (registers : List String) (e : Typed.Expr ctx ty) (dest : Option String)
    (s : Lower.State) : Grows s (Lower.expr registers e dest s).2 := by
  induction e generalizing s dest with
  | ref p node found => exact grows_named dest _ s
  | clock p name found => exact Grows.refl s
  | const p w v => exact grows_emit dest _ s
  | un p op a ih =>
    cases op
    exact ((ih none s).trans (grows_emit none _ _)).trans (grows_emit dest _ _)
  | bin p op ordinary a b ia ib =>
    exact ((ia none s).trans (ib none _)).trans (grows_emit dest _ _)
  | concat p a b bound ia ib =>
    exact ((ia none s).trans (ib none _)).trans (grows_emit dest _ _)
  | icmp p pred a b ia ib =>
    exact ((ia none s).trans (ib none _)).trans (grows_emit dest _ _)
  | mux p c a b ic ia ib =>
    exact (((ic none s).trans (ia none _)).trans (ib none _)).trans (grows_emit dest _ _)
  | extract p a lo count bound ih => exact (ih none s).trans (grows_emit dest _ _)
  | replicate p a count bound ih => exact (ih none s).trans (grows_emit dest _ _)
  | @read width depth p name found addr ih =>
    have walk := ih none (reserve s name)
    cases hw : Lower.expr registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    let index := (s.readCounts.lookup name).getD 0
    have guarded := grows_inRange depth a (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded
    rw [read_eq registers p name found addr dest s a walked hw guard state hg]
    have base : Grows s state :=
      (((grows_reserve s _).trans walk).trans (grows_record _ _)).trans guarded
    cases guard with
    | none => exact base.trans (grows_named dest _ _)
    | some ok => exact (base.trans (grows_emit none _ _)).trans (grows_emit dest _ _)

theorem expr_aliases (registers : List String) (e : Typed.Expr ctx ty) (s : Lower.State) :
    (Lower.expr registers e none s).2.aliases = s.aliases := by
  induction e generalizing s with
  | ref p node found => rfl
  | clock p name found => rfl
  | const p w v => exact emit_aliases none _ s
  | un p op a ih =>
    cases op
    exact (emit_aliases none _ _).trans ((emit_aliases none _ _).trans (ih s))
  | bin p op ordinary a b ia ib =>
    exact (emit_aliases none _ _).trans ((ib _).trans (ia s))
  | concat p a b bound ia ib =>
    exact (emit_aliases none _ _).trans ((ib _).trans (ia s))
  | icmp p pred a b ia ib =>
    exact (emit_aliases none _ _).trans ((ib _).trans (ia s))
  | mux p c a b ic ia ib =>
    exact (emit_aliases none _ _).trans ((ib _).trans ((ia _).trans (ic s)))
  | extract p a lo count bound ih => exact (emit_aliases none _ _).trans (ih s)
  | replicate p a count bound ih => exact (emit_aliases none _ _).trans (ih s)
  | @read width depth p name found addr ih =>
    have walk := ih (reserve s name)
    cases hw : Lower.expr registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    let index := (s.readCounts.lookup name).getD 0
    have guarded := inRange_aliases depth a (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded
    rw [read_eq registers p name found addr none s a walked hw guard state hg]
    have base : state.aliases = s.aliases := guarded.trans walk
    cases guard with
    | none => exact base
    | some ok => exact (emit_aliases none _ _).trans ((emit_aliases none _ _).trans base)

def readName (r : Lower.ReadPort) : String := s!"{r.memory}.r{r.index}_data"

/-- The alias that a named expression adds, if any. -/
def AliasOf (registers : List String) (t : Lower.State) :
    Typed.Expr ctx ty → Option String → Prop
  | .ref _ node _, v => v = some (Lower.valueName registers node)
  | .read (depth := depth) _ name _ _, v =>
      (depth = 2 ^ Typed.addressWidth depth ∧
        ∃ r ∈ t.reads, r.memory = name ∧ v = some (readName r)) ∨
      (depth ≠ 2 ^ Typed.addressWidth depth ∧ v = none)
  | _, v => v = none

theorem aliasOf_grows (registers : List String) {s t : Lower.State} (grows : Grows s t)
    (e : Typed.Expr ctx ty) (v : Option String) (h : AliasOf registers s e v) :
    AliasOf registers t e v := by
  cases e <;> try exact h
  case read depth p name found addr =>
    rcases h with ⟨full, r, hr, same, hv⟩ | h
    · exact Or.inl ⟨full, r, grows.reads.subset hr, same, hv⟩
    · exact Or.inr h

def withAlias (aliases : Std.HashMap String String) (name : String) :
    Option String → Std.HashMap String String
  | some v => aliases.insert name v
  | none => aliases

theorem expr_named_aliases (registers : List String) (e : Typed.Expr ctx ty) (name : String)
    (s : Lower.State) : ∃ v, AliasOf registers (Lower.expr registers e (some name) s).2 e v ∧
      (Lower.expr registers e (some name) s).2.aliases = withAlias s.aliases name v := by
  cases e with
  | ref p node found => exact ⟨_, rfl, rfl⟩
  | clock p n found => exact ⟨none, rfl, rfl⟩
  | const p w v => exact ⟨none, rfl, emit_aliases (some name) _ s⟩
  | un p op a =>
    cases op
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans ((emit_aliases none _ _).trans
      (expr_aliases registers a s))⟩
  | bin p op ordinary a b =>
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      (expr_aliases registers a s))⟩
  | concat p a b bound =>
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      (expr_aliases registers a s))⟩
  | icmp p pred a b =>
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      (expr_aliases registers a s))⟩
  | mux p c a b =>
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans ((expr_aliases registers b _).trans
      ((expr_aliases registers a _).trans (expr_aliases registers c s)))⟩
  | extract p a lo count bound =>
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans (expr_aliases registers a s)⟩
  | replicate p a count bound =>
    exact ⟨none, rfl, (emit_aliases (some name) _ _).trans (expr_aliases registers a s)⟩
  | @read width depth p memory found addr =>
    have walk := expr_aliases registers addr (reserve s memory)
    let index := (s.readCounts.lookup memory).getD 0
    cases hw : Lower.expr registers addr none (reserve s memory) with
    | mk a walked =>
    rw [hw] at walk
    have guarded := inRange_aliases depth a (record walked ⟨memory, index, a⟩)
    have reads := (grows_inRange depth a (record walked ⟨memory, index, a⟩)).reads
    have result := inRange_result depth a (record walked ⟨memory, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨memory, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded reads result
    rw [read_eq registers p memory found addr (some name) s a walked hw guard state hg]
    have base : state.aliases = s.aliases := guarded.trans walk
    cases guard with
    | none =>
      have full : depth = 2 ^ Typed.addressWidth depth := by
        by_cases h : depth = 2 ^ Typed.addressWidth depth
        · exact h
        · have e := (result.trans (ite_eq_right_of_eq_false _ _ (eq_false h))).symm
          cases e
      refine ⟨some (readName ⟨memory, index, a⟩), ?_, ?_⟩
      · exact Or.inl ⟨full, _, reads.subset (List.mem_cons_self ..), rfl, rfl⟩
      · change (state.aliases.insert name _) = _
        rw [base]
        rfl
    | some ok =>
      have short : depth ≠ 2 ^ Typed.addressWidth depth := by
        intro h
        have e : some ok = none := result.trans (ite_eq_left_of_eq_true _ _ (eq_true h))
        cases e
      exact ⟨none, Or.inr ⟨short, rfl⟩,
        (emit_aliases (some name) _ _).trans ((emit_aliases none _ _).trans base)⟩

theorem grows_mapM (xs : List α) (f : α → Lower.Build β) (s : Lower.State)
    (step : ∀ x ∈ xs, ∀ state, Grows state (f x state).2) : Grows s (xs.mapM f s).2 := by
  induction xs generalizing s with
  | nil => exact Grows.refl s
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact (step x (List.mem_cons_self ..) s).trans
      (ih _ (fun a ha => step a (List.mem_cons_of_mem _ ha)))

theorem mapM_aliases (xs : List α) (f : α → Lower.Build β) (s : Lower.State)
    (step : ∀ x ∈ xs, ∀ state, (f x state).2.aliases = state.aliases) :
    (xs.mapM f s).2.aliases = s.aliases := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact (ih _ (fun a ha => step a (List.mem_cons_of_mem _ ha))).trans
      (step x (List.mem_cons_self ..) s)

def inputArgument (registers : List String) {ports : String → List Port} {child : String}
    (input : (port : {p : Port // p ∈ ports child}) × Typed.Expr ctx port.val.ty) :
    Lower.Build (String × String × Mlir.Ty) := do
  let value ← Lower.expr registers input.2 none
  return (input.1.val.name, value, Lower.type input.1.val.ty)

theorem grows_statement (registers : List String) (stmt : Typed.Stmt ctx ports)
    (s : Lower.State) : Grows s (Lower.statement registers stmt s).2 := by
  cases stmt with
  | let_ p name w e | assign p name w target e => exact grows_expr registers e (some name) s
  | next p name w target e =>
    exact (grows_expr registers e none s).trans
      ⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_cons _ _,
        List.suffix_refl _⟩
  | mem => exact Grows.refl s
  | reg p name w clk reset =>
    cases reset with
    | none =>
      exact ⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
        List.suffix_cons _ _⟩
    | some r =>
      exact ((grows_expr registers r.signal none s).trans
        (grows_expr registers r.value none _)).trans
        ⟨List.prefix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
          List.suffix_cons _ _⟩
  | write p name index w depth target addr data enable =>
    have base := ((grows_expr registers addr none s).trans (grows_expr registers data none _)).trans
      (grows_expr registers enable none _)
    let a := Lower.expr registers addr none s
    let d := Lower.expr registers data none a.2
    let e := Lower.expr registers enable none d.2
    have guarded := grows_inRange depth a.1 e.2
    let finish : String → Lower.Build Unit := fun enable =>
      modify fun state => { state with
        writes := ⟨name, index, a.1, d.1, enable⟩ :: state.writes }
    change Grows s ((match (Lower.inRange depth a.1 e.2).1 with
      | none => (pure e.1 >>= finish)
      | some ok => (Lower.emit none (.comb .and e.1 ok 1) >>= finish))
        (Lower.inRange depth a.1 e.2).2).2
    cases eq : Lower.inRange depth a.1 e.2 with
    | mk result state =>
      rw [eq] at guarded
      have push (x : Lower.State) (en : String) : Grows x (finish en x).2 :=
        ⟨List.prefix_refl _, List.suffix_refl _, List.suffix_cons _ _, List.suffix_refl _,
          List.suffix_refl _⟩
      cases result with
      | none => exact (base.trans guarded).trans (push _ _)
      | some ok => exact ((base.trans guarded).trans (grows_emit none _ _)).trans (push _ _)
  | inst p name child inputs =>
    exact (grows_mapM inputs (inputArgument registers) s
      (fun i _ state => grows_expr registers i.2 none state)).trans (grows_push _ _)

theorem grows_statements (registers : List String) (stmts : List (Typed.Stmt ctx ports))
    (s : Lower.State) :
    Grows s ((do for stmt in stmts do Lower.statement registers stmt) s).2 := by
  induction stmts generalizing s with
  | nil => exact Grows.refl s
  | cons stmt stmts ih =>
    simp only [List.forIn_cons, bind_assoc, pure_bind]
    exact (grows_statement registers stmt s).trans (ih _)

def LetName : Typed.Stmt ctx ports → Option String
  | .let_ _ name .. | .assign _ name .. => some name
  | _ => none

def StmtAlias (registers : List String) (t : Lower.State) (aliases : Std.HashMap String String) :
    Typed.Stmt ctx ports → Prop
  | .let_ _ name _ e | .assign _ name _ _ e => AliasOf registers t e aliases[name]?
  | _ => True

theorem statement_aliases_other (registers : List String) (stmt : Typed.Stmt ctx ports)
    (s : Lower.State) (other : LetName stmt = none) :
    (Lower.statement registers stmt s).2.aliases = s.aliases := by
  cases stmt with
  | let_ | assign => cases other
  | next p name w target e => exact expr_aliases registers e s
  | mem => rfl
  | reg p name w clk reset =>
    cases reset with
    | none => rfl
    | some r => exact (expr_aliases registers r.value _).trans (expr_aliases registers r.signal s)
  | write p name index w depth target addr data enable =>
    have base := ((expr_aliases registers enable _).trans (expr_aliases registers data _)).trans
      (expr_aliases registers addr s)
    let a := Lower.expr registers addr none s
    let d := Lower.expr registers data none a.2
    let e := Lower.expr registers enable none d.2
    have guarded := inRange_aliases depth a.1 e.2
    let finish : String → Lower.Build Unit := fun enable =>
      modify fun state => { state with
        writes := ⟨name, index, a.1, d.1, enable⟩ :: state.writes }
    change ((match (Lower.inRange depth a.1 e.2).1 with
      | none => (pure e.1 >>= finish)
      | some ok => (Lower.emit none (.comb .and e.1 ok 1) >>= finish))
        (Lower.inRange depth a.1 e.2).2).2.aliases = _
    cases eq : Lower.inRange depth a.1 e.2 with
    | mk result state =>
      rw [eq] at guarded
      cases result with
      | none => exact guarded.trans base
      | some ok => exact (emit_aliases none (.comb .and e.1 ok 1) state).trans (guarded.trans base)
  | inst p name child inputs =>
    exact mapM_aliases inputs (inputArgument registers) s
      (fun i _ state => expr_aliases registers i.2 state)

theorem statement_aliases_named (registers : List String) (stmt : Typed.Stmt ctx ports)
    (s : Lower.State) (name : String) (named : LetName stmt = some name) :
    ∃ v, (Lower.statement registers stmt s).2.aliases = withAlias s.aliases name v ∧
      ∀ t aliases, Grows (Lower.statement registers stmt s).2 t → aliases[name]? = v →
        StmtAlias registers t aliases stmt := by
  cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
  all_goals subst named
  case let_ p n w e | assign p n w target e =>
    obtain ⟨v, alias, eq⟩ := expr_named_aliases registers e n s
    exact ⟨v, eq, fun t aliases grows found => by
      simp only [StmtAlias, found]
      exact aliasOf_grows registers grows e v alias⟩

theorem statements_aliases (registers : List String) (stmts : List (Typed.Stmt ctx ports))
    (s : Lower.State) (unique : (stmts.filterMap LetName).Nodup)
    (clean : ∀ n ∈ stmts.filterMap LetName, s.aliases[n]? = none) :
    let t := ((do for stmt in stmts do Lower.statement registers stmt) s).2
    (∀ k, k ∉ stmts.filterMap LetName → t.aliases[k]? = s.aliases[k]?) ∧
    ∀ stmt ∈ stmts, StmtAlias registers t t.aliases stmt := by
  induction stmts generalizing s with
  | nil => exact ⟨fun _ _ => rfl, fun _ h => nomatch h⟩
  | cons stmt stmts ih =>
    simp only [List.forIn_cons, bind_assoc, pure_bind]
    let first := (Lower.statement registers stmt s).2
    have restGrows := grows_statements registers stmts first
    change (∀ k, k ∉ (stmt :: stmts).filterMap LetName →
        ((do for stmt in stmts do Lower.statement registers stmt) first).2.aliases[k]? =
          s.aliases[k]?) ∧
      ∀ st ∈ stmt :: stmts, StmtAlias registers
        ((do for stmt in stmts do Lower.statement registers stmt) first).2
        ((do for stmt in stmts do Lower.statement registers stmt) first).2.aliases st
    cases named : LetName stmt with
    | none =>
      have same := statement_aliases_other registers stmt s named
      simp only [List.filterMap_cons, named] at unique clean
      have rest := ih first unique (fun n hn => by
        change first.aliases[n]? = none
        rw [same]
        exact clean n hn)
      refine ⟨fun k hk => ?_, fun st hs => ?_⟩
      · simp only [List.filterMap_cons, named] at hk
        rw [rest.1 k hk]
        change first.aliases[k]? = _
        rw [same]
      · rcases List.mem_cons.mp hs with rfl | hs
        · cases st <;> simp_all [LetName, StmtAlias]
        · exact rest.2 st hs
    | some name =>
      obtain ⟨v, eq, alias⟩ := statement_aliases_named registers stmt s name named
      simp only [List.filterMap_cons, named, List.nodup_cons, List.mem_cons,
        forall_eq_or_imp] at unique clean
      have keep (k : String) (ne : k ≠ name) : first.aliases[k]? = s.aliases[k]? := by
        change (Lower.statement registers stmt s).2.aliases[k]? = _
        rw [eq]
        cases v with
        | none => rfl
        | some x =>
          simp only [withAlias, Std.HashMap.getElem?_insert,
            show (name == k) = false from beq_eq_false_iff_ne.mpr (Ne.symm ne)]
          rfl
      have rest := ih first unique.2 (fun n hn => by
        rw [keep n (fun same => unique.1 (same ▸ hn))]
        exact clean.2 n hn)
      refine ⟨fun k hk => ?_, fun st hs => ?_⟩
      · simp only [List.filterMap_cons, named, List.mem_cons, not_or] at hk
        rw [rest.1 k hk.2, keep k hk.1]
      · rcases List.mem_cons.mp hs with rfl | hs
        · apply alias _ _ restGrows
          rw [rest.1 name unique.1]
          change (Lower.statement registers st s).2.aliases[name]? = v
          rw [eq]
          cases v with
          | none => exact clean.1
          | some x => simp [withAlias]
        · exact rest.2 st hs

end Silicon.Core.LowerProof
