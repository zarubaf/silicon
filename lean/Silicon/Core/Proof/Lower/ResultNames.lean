import Silicon.Core.Proof.Lower.ModuleTyping

/-!
A plain op of the statement state defines a temporary or the name of an unaliased statement.
The final module keeps both names.
-/
namespace Silicon.Core.LowerProof

def ResultName (dest : Option String) (fresh : Prop) (names : List String) : Prop :=
  (∃ i : Nat, names = [s!"silicon_t{i}"]) ∨ ∃ x, dest = some x ∧ names = [x] ∧ fresh

def NewNames (dest : Option String) (fresh : Prop) (s t : Lower.State) : Prop :=
  ∃ tail, t.body.toList = s.body.toList ++ tail ∧
    ∀ entry ∈ tail, ResultName dest fresh entry.1 ∧ isCompreg entry.2 = false

theorem NewNames.trans {s t u : Lower.State} {p q : Prop}
    (st : NewNames none p s t) (tu : NewNames dest q t u) : NewNames dest q s u := by
  obtain ⟨xs, hx, px⟩ := st
  obtain ⟨ys, hy, py⟩ := tu
  refine ⟨xs ++ ys, by rw [hy, hx, List.append_assoc], fun entry he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · obtain ⟨name, plain⟩ := px entry he
    rcases name with temp | ⟨x, none, _⟩
    · exact ⟨Or.inl temp, plain⟩
    · cases none
  · exact py entry he

theorem NewNames.same {s t : Lower.State} (p : Prop) (body : t.body = s.body) :
    NewNames dest p s t :=
  ⟨[], by rw [body, List.append_nil], fun _ h => nomatch h⟩

theorem NewNames.none {s t : Lower.State} {p : Prop} (q : Prop)
    (h : NewNames none p s t) : NewNames none q s t := by
  obtain ⟨tail, body, names⟩ := h
  refine ⟨tail, body, fun entry he => ?_⟩
  obtain ⟨name, plain⟩ := names entry he
  rcases name with temp | ⟨x, none, _⟩
  · exact ⟨Or.inl temp, plain⟩
  · cases none

theorem newNames_emit (dest : Option String) (op : Mlir.Op) (stateless : isCompreg op = false)
    (s : Lower.State) (fresh : Prop) (h : fresh) :
    NewNames dest fresh s (Lower.emit dest op s).2 := by
  refine ⟨_, emit_body dest op s, fun entry he => ?_⟩
  cases List.mem_singleton.mp he
  cases dest with
  | none => exact ⟨Or.inl ⟨_, rfl⟩, stateless⟩
  | some x => exact ⟨Or.inr ⟨x, rfl, rfl, h⟩, stateless⟩

theorem newNames_temp (op : Mlir.Op) (stateless : isCompreg op = false) (s : Lower.State)
    (p : Prop) : NewNames none p s (Lower.emit none op s).2 :=
  ⟨_, emit_body none op s, fun entry he => by
    cases List.mem_singleton.mp he
    exact ⟨Or.inl ⟨_, rfl⟩, stateless⟩⟩

theorem newNames_inRange (depth : Nat) (addr : String) (s : Lower.State) (p : Prop) :
    NewNames none p s (Lower.inRange depth addr s).2 := by
  rw [inRange_state]
  split
  · exact NewNames.same p rfl
  · exact (newNames_temp _ rfl s p).trans (newNames_temp _ rfl _ p)

theorem expr_names (registers : List String) (e : Typed.Expr ctx ty) (dest : Option String)
    (s : Lower.State) : NewNames dest (NotAliased e) s (Lower.expr registers e dest s).2 := by
  induction e generalizing s dest with
  | ref p node found => exact NewNames.same _ (by cases dest <;> rfl)
  | clock p name found => exact NewNames.same _ rfl
  | const p w v => exact newNames_emit dest _ rfl s _ trivial
  | un p op a ih =>
    cases op
    exact ((ih none s).trans (newNames_temp _ rfl _ True)).trans
      (newNames_emit dest _ rfl _ _ trivial)
  | bin p op ordinary a b ia ib =>
    exact ((ia none s).trans ((ib none _).none True)).trans (newNames_emit dest _ rfl _ _ trivial)
  | concat p a b bound ia ib =>
    exact ((ia none s).trans ((ib none _).none True)).trans (newNames_emit dest _ rfl _ _ trivial)
  | icmp p pred a b ia ib =>
    exact ((ia none s).trans ((ib none _).none True)).trans (newNames_emit dest _ rfl _ _ trivial)
  | mux p c a b ic ia ib =>
    exact (((ic none s).trans ((ia none _).none True)).trans ((ib none _).none True)).trans
      (newNames_emit dest _ rfl _ _ trivial)
  | extract p a lo count bound ih =>
    exact (ih none s).trans (newNames_emit dest _ rfl _ _ trivial)
  | replicate p a count bound ih =>
    exact (ih none s).trans (newNames_emit dest _ rfl _ _ trivial)
  | @read width depth p name found addr ih =>
    have walk := ih none (reserve s name)
    cases hw : Lower.expr registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    let index := (s.readCounts.lookup name).getD 0
    have guarded := newNames_inRange depth a (record walked ⟨name, index, a⟩) True
    have result := inRange_result depth a (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guarded result
    rw [read_eq registers p name found addr dest s a walked hw guard state hg]
    have base : NewNames none True s state :=
      ((NewNames.same True rfl).trans walk).trans ((NewNames.same (dest := none) True rfl).trans
        guarded)
    cases guard with
    | none => exact base.trans (NewNames.same _ (by cases dest <;> rfl))
    | some ok =>
      have short : depth ≠ 2 ^ Typed.addressWidth depth := by
        intro full
        have e : some ok = none := result.trans (ite_eq_left_of_eq_true _ _ (eq_true full))
        cases e
      exact (base.trans (newNames_temp _ rfl _ True)).trans (newNames_emit dest _ rfl _ _ short)

def StmtResult (stmt : Typed.Stmt ctx ports) (names : List String) : Prop :=
  (∃ i : Nat, names = [s!"silicon_t{i}"]) ∨
    match stmt with
    | .let_ _ x _ e | .assign _ x _ _ e => names = [x] ∧ NotAliased e
    | _ => False

def EntryOk (stmt : Typed.Stmt ctx ports) (entry : List String × Mlir.Op) : Prop :=
  isCompreg entry.2 = false ∧ (isInstance entry.2 = false → StmtResult stmt entry.1)

/-- A statement adds only plain ops with temporaries or its own unaliased name, and instances.
It adds no register. -/
theorem statement_names (registers : List String) (stmt : Typed.Stmt ctx ports)
    (s : Lower.State) : ∃ tail,
      (Lower.statement registers stmt s).2.body.toList = s.body.toList ++ tail ∧
      ∀ entry ∈ tail, EntryOk stmt entry := by
  have temps {q : Prop} {t u : Lower.State} (h : NewNames none q t u) :
      ∃ tail, u.body.toList = t.body.toList ++ tail ∧ ∀ entry ∈ tail, EntryOk stmt entry := by
    obtain ⟨tail, body, names⟩ := h
    refine ⟨tail, body, fun entry he => ?_⟩
    obtain ⟨name, plain⟩ := names entry he
    refine ⟨plain, fun _ => ?_⟩
    rcases name with temp | ⟨x, none, _⟩
    · exact Or.inl temp
    · cases none
  have join {t u v : Lower.State}
      (tu : ∃ tail, u.body.toList = t.body.toList ++ tail ∧ ∀ entry ∈ tail, EntryOk stmt entry)
      (uv : ∃ tail, v.body.toList = u.body.toList ++ tail ∧ ∀ entry ∈ tail, EntryOk stmt entry) :
      ∃ tail, v.body.toList = t.body.toList ++ tail ∧ ∀ entry ∈ tail, EntryOk stmt entry := by
    obtain ⟨xs, hx, px⟩ := tu
    obtain ⟨ys, hy, py⟩ := uv
    refine ⟨xs ++ ys, by rw [hy, hx, List.append_assoc], fun entry he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact px entry he
    · exact py entry he
  have keep {t u : Lower.State} (body : u.body = t.body) :
      ∃ tail, u.body.toList = t.body.toList ++ tail ∧ ∀ entry ∈ tail, EntryOk stmt entry :=
    ⟨[], by rw [body, List.append_nil], fun _ h => nomatch h⟩
  cases stmt with
  | let_ p name w e | assign p name w target e =>
    obtain ⟨tail, body, names⟩ := expr_names registers e (some name) s
    refine ⟨tail, body, fun entry he => ?_⟩
    obtain ⟨result, plain⟩ := names entry he
    refine ⟨plain, fun _ => ?_⟩
    rcases result with temp | ⟨x, same, hn, fresh⟩
    · exact Or.inl temp
    · cases same
      exact Or.inr ⟨hn, fresh⟩
  | next p name w target e => exact temps (expr_names registers e none s)
  | mem => exact keep rfl
  | reg p name w clk reset =>
    cases reset with
    | none => exact keep rfl
    | some r =>
      exact join (temps (expr_names registers r.signal none s))
        (temps (expr_names registers r.value none _))
  | write p name index w depth target addr data enable =>
    let a := Lower.expr registers addr none s
    let d := Lower.expr registers data none a.2
    let e := Lower.expr registers enable none d.2
    have base := join (join (temps (expr_names registers addr none s))
      (temps (expr_names registers data none _))) (temps (expr_names registers enable none _))
    have guarded := temps (newNames_inRange depth a.1 e.2 True)
    let finish : String → Lower.Build Unit := fun enable =>
      modify fun state => { state with
        writes := ⟨name, index, a.1, d.1, enable⟩ :: state.writes }
    change ∃ tail, ((match (Lower.inRange depth a.1 e.2).1 with
      | none => (pure e.1 >>= finish)
      | some ok => (Lower.emit none (.comb .and e.1 ok 1) >>= finish))
        (Lower.inRange depth a.1 e.2).2).2.body.toList = s.body.toList ++ tail ∧ _
    cases eq : Lower.inRange depth a.1 e.2 with
    | mk result state =>
      rw [eq] at guarded
      cases result with
      | none => exact join base guarded
      | some ok => exact join (join base guarded) (temps (newNames_temp _ rfl state True))
  | inst p name child inputs =>
    have walk : ∀ (xs : List ((q : {q : Port // q ∈ ports child}) × Typed.Expr ctx q.val.ty))
        (t : Lower.State), ∃ tail,
        (xs.mapM (inputArgument registers) t).2.body.toList = t.body.toList ++ tail ∧
        ∀ entry ∈ tail, EntryOk (Typed.Stmt.inst p name child inputs) entry := by
      intro xs
      induction xs with
      | nil => intro t; exact ⟨[], by simp [List.mapM_nil]; rfl, fun _ h => nomatch h⟩
      | cons x xs ih =>
        intro t
        rw [List.mapM_cons]
        obtain ⟨tail, body, names⟩ := temps (expr_names registers x.2 none t)
        obtain ⟨rest, hr, pr⟩ := ih (inputArgument registers x t).2
        refine ⟨tail ++ rest, ?_, fun entry he => ?_⟩
        · change (List.mapM (inputArgument registers) xs
            (inputArgument registers x t).2).2.body.toList = _
          rw [hr]
          change (Lower.expr registers x.2 none t).2.body.toList ++ rest = _
          rw [body, List.append_assoc]
        · rcases List.mem_append.mp he with he | he
          · exact names entry he
          · exact pr entry he
    obtain ⟨tail, body, names⟩ := walk inputs s
    let args0 := (inputs.mapM (inputArgument registers) s).1
    let entry : List String × Mlir.Op :=
      ((instResults ports child).map (fun p => s!"{name}.{p.1}"),
        .instance name child (instArgs ports child args0) (instResults ports child))
    refine ⟨tail ++ [entry], ?_, fun entry he => ?_⟩
    · change ((inputs.mapM (inputArgument registers) s).2.body.push _).toList = _
      rw [Array.toList_push, body, List.append_assoc]
      rfl
    · rcases List.mem_append.mp he with he | he
      · exact names entry he
      · cases List.mem_singleton.mp he
        exact ⟨rfl, fun hi => by cases hi⟩

theorem statements_names (registers : List String) (stmts : List (Typed.Stmt ctx ports))
    (s : Lower.State) : ∃ tail,
      ((do for stmt in stmts do Lower.statement registers stmt) s).2.body.toList =
        s.body.toList ++ tail ∧
      ∀ entry ∈ tail, ∃ stmt ∈ stmts, EntryOk stmt entry := by
  induction stmts generalizing s with
  | nil => exact ⟨[], by rw [run_nil, List.append_nil], fun _ h => nomatch h⟩
  | cons stmt stmts ih =>
    rw [run_cons]
    obtain ⟨xs, hx, px⟩ := statement_names registers stmt s
    obtain ⟨ys, hy, py⟩ := ih (Lower.statement registers stmt s).2
    refine ⟨xs ++ ys, by rw [hy, hx, List.append_assoc], fun entry he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨stmt, List.mem_cons_self .., px entry he⟩
    · obtain ⟨st, hs, r⟩ := py entry he
      exact ⟨st, List.mem_cons_of_mem _ hs, r⟩

theorem final_entries (m : Typed.Module) (entry : List String × Mlir.Op)
    (he : entry ∈ (Lower.statementState m).body.toList) :
    ∃ stmt ∈ Lower.statements m, EntryOk stmt entry := by
  obtain ⟨tail, body, names⟩ := statements_names (Lower.registers m) (Lower.statements m) {}
  rw [← run_state] at body
  have tailEq : tail = (Lower.statementState m).body.toList := by simpa using body.symm
  rw [← tailEq] at he
  exact names entry he

/-- The final module keeps the result name of every plain statement op. -/
theorem result_renamed (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (entry : List String × Mlir.Op)
    (he : entry ∈ (Lower.statementState m).body.toList) (plain : isInstance entry.2 = false) :
    ∃ n, entry.1 = [n] ∧ rename m n = n := by
  obtain ⟨stmt, hs, _, result⟩ := final_entries m entry he
  rcases result plain with ⟨i, hi⟩ | named
  · exact ⟨_, hi, rename_invalid raw t h m hm _ (temporary_invalid i)⟩
  · have fresh := stmt_fresh raw t h m hm stmt hs
    cases stmt <;> simp only at named
    case let_ p x w e => exact ⟨x, named.1, fresh named.2⟩
    case assign p x w target e => exact ⟨x, named.1, fresh named.2⟩

end Silicon.Core.LowerProof
