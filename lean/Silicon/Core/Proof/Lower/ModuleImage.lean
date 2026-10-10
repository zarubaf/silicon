import Silicon.Core.Proof.Lower.CoreNames

/-!
The image of the core solution gives each statement result its core value. Ports, registers,
and aliased names keep the core value of their source node.
-/
namespace Silicon.Core.LowerProof

open Semantics

/-- The environment of an image, with a fallback outside its keys. -/
def imageEnv (image : Image) (fallback : String → Mlir.Value) : Mlir.Env :=
  fun y => some ((image.lookup y).getD (fallback y))

theorem lookup_of_nodup (image : Image) (unique : (image.map Prod.fst).Nodup)
    (b : String × Mlir.Value) (hb : b ∈ image) : image.lookup b.1 = some b.2 := by
  induction image with
  | nil => cases hb
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [List.lookup]
    · have ne : first.1 ≠ b.1 := fun eq => unique.1 (eq ▸ List.mem_map_of_mem hb)
      simp [List.lookup, show (b.1 == first.1) = false from beq_eq_false_iff_ne.mpr (Ne.symm ne),
        ih unique.2 hb]

theorem imageEnv_agrees (image : Image) (fallback : String → Mlir.Value)
    (unique : (image.map Prod.fst).Nodup) : image.Agrees (imageEnv image fallback) := by
  intro b hb
  simp [imageEnv, lookup_of_nodup image unique b hb]

theorem imageEnv_outside (image : Image) (fallback : String → Mlir.Value) (y : String)
    (absent : y ∉ image.map Prod.fst) : imageEnv image fallback y = some (fallback y) := by
  have none : image.lookup y = none := by
    induction image with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp [List.lookup, show (y == first.1) = false from beq_eq_false_iff_ne.mpr absent.1,
        ih absent.2]
  simp [imageEnv, none]

theorem expressionInputs_of_reads (registers : List String) (values : Valuation ctx)
    (env : Mlir.Env) (e : Typed.Expr ctx ty)
    (refs : ∀ node ∈ Deps.reads e.erase, ∀ w found,
      env (Lower.valueName registers node) = some (.bits w (values node w found)))
    (clocks : ∀ name, ctx.lookup (.name name) = some .clock → env name = some .clock) :
    ExpressionInputs registers values env e := by
  induction e with
  | ref p node found =>
    apply refs node _ _ found
    cases node <;> simp [Typed.Expr.erase, Deps.reads]
  | clock p name found => exact clocks name found
  | const => trivial
  | un p op a ih => exact ih refs
  | bin p op ordinary a b ia ib =>
    exact ⟨ia fun n hn => refs n (List.mem_append_left _ hn),
      ib fun n hn => refs n (List.mem_append_right _ hn)⟩
  | concat p a b bound ia ib =>
    exact ⟨ia fun n hn => refs n (List.mem_append_left _ hn),
      ib fun n hn => refs n (List.mem_append_right _ hn)⟩
  | icmp p pred a b ia ib =>
    exact ⟨ia fun n hn => refs n (List.mem_append_left _ hn),
      ib fun n hn => refs n (List.mem_append_right _ hn)⟩
  | mux p c a b ic ia ib =>
    exact ⟨ic fun n hn => refs n (List.mem_append_left _ (List.mem_append_left _ hn)),
      ia fun n hn => refs n (List.mem_append_left _ (List.mem_append_right _ hn)),
      ib fun n hn => refs n (List.mem_append_right _ hn)⟩
  | extract p a lo count bound ih => exact ih refs
  | replicate p a count bound ih => exact ih refs
  | read p name found addr ih => exact ih refs

theorem expr_fresh_result (registers : List String) (e : Typed.Expr ctx (.bits w))
    (fresh : NotAliased e) (x : String) (s : Lower.State) :
    (Lower.expr registers e (some x) s).1 = x := by
  cases e with
  | ref => exact fresh.elim
  | const => exact emit_result (some x) _ s
  | un p op a =>
    cases op
    exact emit_result (some x) _ _
  | bin | concat | icmp | mux | extract | replicate => exact emit_result (some x) _ _
  | @read width depth p memory found addr =>
    have walk := expr_aliases registers addr (reserve s memory)
    let index := (s.readCounts.lookup memory).getD 0
    cases hw : Lower.expr registers addr none (reserve s memory) with
    | mk a walked =>
    have resultGuard := inRange_result depth a (record walked ⟨memory, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨memory, index, a⟩) with
    | mk guard state =>
    rw [hg] at resultGuard
    rw [read_eq registers p memory found addr (some x) s a walked hw guard state hg]
    cases guard with
    | none =>
      have full : depth = 2 ^ Typed.addressWidth depth := by
        by_cases hd : depth = 2 ^ Typed.addressWidth depth
        · exact hd
        · have e := (resultGuard.trans (ite_eq_right_of_eq_false _ _ (eq_false hd))).symm
          cases e
      exact absurd full fresh
    | some ok => exact emit_result (some x) _ _

theorem accounts_perm (image : Image) (t : Lower.State) (accounts : image.Accounts {} t) :
    (image.map Prod.fst).Perm (allocatedNames t) := by
  apply List.perm_iff_count.mpr
  intro name
  have := accounts name
  simpa [allocatedNames] using this

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)

include h hm in
/-- The image of all statements of a module. -/
theorem module_image (values : Valuation m.ctx) (memories : Memories m.ctx)
    (words : ModelMemories m.ctx)
    (models : ∀ name width depth found,
      MemModelProof.Agrees ⟨depth, width, 0, 0⟩ (words name width depth found)
        (memories name width depth found)) :
    ∃ image : Image, (image.map Prod.fst).Perm (allocatedNames (finalState m)) ∧
      (∀ env, image.Agrees env → GlobalInputs (Lower.registers m) values env →
        StmtFrame words env {} (finalState m)) ∧
      (∀ stmt ∈ Lower.statements m, ∃ s₀,
        Grows (Lower.statement (Lower.registers m) stmt s₀).2 (finalState m) ∧
        ∀ env, image.Agrees env → LetPost (Lower.registers m) values memories stmt s₀ env) ∧
      ∀ stmt ∈ Lower.statements m, ∀ b ∈ instBindings (coreAt m values) stmt, b ∈ image := by
  have legal := fun x hx => stmt_legal raw t h m hm x hx
  obtain ⟨image, accounts, frame, lets, insts⟩ := image_statements (Lower.registers m) values
    memories words models (Lower.statements m) legal (coreAt m values) {}
  exact ⟨image, accounts_perm image _ accounts, frame, lets, insts⟩

include h hm

theorem allocated_nodup : (allocatedNames (finalState m)).Nodup :=
  (List.nodup_append.mp (statement_names_fresh raw t h m hm)).1

theorem input_not_allocated (p : Port) (hp : p ∈ m.ports) (input : p.dir = .input) :
    p.name ∉ allocatedNames (finalState m) := by
  intro member
  have fresh := statement_names_fresh raw t h m hm
  exact (List.nodup_append.mp fresh).2.2 _ member _ (List.mem_append_left _
    (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [input]⟩, rfl⟩)) rfl

theorem register_not_allocated (i : Nat) (p : Pos) (n : String) (w : Nat) (clk : String)
    (target) (reset) (ni : Nat) (np : Pos) (next : Typed.Expr m.ctx (.bits w))
    (member : Typed.Equation.reg i p n w clk target reset ni np next ∈ m.body) :
    (regName n) ∉ allocatedNames (finalState m) := by
  intro alloc
  have fresh := statement_names_fresh raw t h m hm
  have stmt := typed_erase_member m (Typed.Stmt.reg p n w clk reset) _ member
    (i, Typed.Stmt.reg p n w clk reset) (by simp [Typed.Equation.parts]) rfl
  exact (List.nodup_append.mp fresh).2.2 _ alloc _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨_, stmt, by simp [Typed.Stmt.erase, rawRegisters]⟩)) rfl

omit h hm in
theorem source_not_allocated (x : String) (legal : Rules.invalidName x = false)
    (alloc : x ∈ allocatedNames (finalState m)) :
    ∃ stmt ∈ Lower.statements m, LetName stmt = some x ∧ StmtResult stmt [x] := by
  unfold allocatedNames at alloc
  rcases List.mem_append.mp alloc with body | reads
  · obtain ⟨entry, he, hx⟩ := List.mem_flatMap.mp body
    obtain ⟨stmt, hs, _, result⟩ := final_entries m entry he
    cases hi : isInstance entry.2 with
    | false =>
      rcases result hi with ⟨i, hi'⟩ | named
      · rw [hi'] at hx
        cases List.mem_singleton.mp hx
        rw [temporary_invalid] at legal
        cases legal
      · cases stmt <;> simp only at named
        case let_ p y w e =>
          rw [named.1] at hx
          cases List.mem_singleton.mp hx
          exact ⟨_, hs, rfl, Or.inr ⟨rfl, named.2⟩⟩
        case assign p y w target e =>
          rw [named.1] at hx
          cases List.mem_singleton.mp hx
          exact ⟨_, hs, rfl, Or.inr ⟨rfl, named.2⟩⟩
    | true =>
      obtain ⟨⟨tail, hb, _, shapes⟩, _⟩ :=
        statements_step (Lower.registers m) (Lower.statements m) {}
      rw [← run_state] at hb
      have tailEq : tail = (Lower.statementState m).body.toList := by simpa using hb.symm
      rw [← tailEq] at he
      obtain ⟨st, _, shape⟩ := shapes entry he hi
      cases st <;> simp only [InstShape] at shape
      case inst p n child inputs =>
        obtain ⟨_, _, rfl⟩ := shape
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
        rw [result_invalid] at legal
        cases legal
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp reads
    have := readName_invalid r
    rw [show readName r = s!"{r.memory}.r{r.index}_data" from rfl] at this
    rw [this] at legal
    cases legal

/-- The image environment agrees with the core solution at every source name. The proof
follows the checked ranks, because a named result has the value of its expression. -/
theorem image_global (sol : Valuation m.ctx) (memories : Memories m.ctx) (image : Image)
    (unique : (image.map Prod.fst).Nodup)
    (perm : (image.map Prod.fst).Perm (allocatedNames (finalState m)))
    (lets : ∀ stmt ∈ Lower.statements m, ∃ s₀,
      Grows (Lower.statement (Lower.registers m) stmt s₀).2 (finalState m) ∧
      ∀ env, image.Agrees env → LetPost (Lower.registers m) sol memories stmt s₀ env)
    (insts : ∀ stmt ∈ Lower.statements m, ∀ b ∈ instBindings (coreAt m sol) stmt, b ∈ image)
    (letSolves : ∀ index pos x w e, Typed.Equation.let_ index pos x w e ∈ m.body → ∀ found,
      sol (.name x) w found = evalExpr sol memories e)
    (assignSolves : ∀ index pos x w target e,
      Typed.Equation.assign index pos x w target e ∈ m.body → ∀ found,
      sol (.name x) w found = evalExpr sol memories e) :
    GlobalInputs (Lower.registers m) sol (imageEnv image (coreAt m sol)) := by
  let env := imageEnv image (coreAt m sol)
  have agree := imageEnv_agrees image (coreAt m sol) unique
  have outside (y : String) (absent : y ∉ allocatedNames (finalState m)) :
      env y = some (coreAt m sol y) :=
    imageEnv_outside image _ y (fun member => absent (perm.mem_iff.mp member))
  have clocks (name : String) (found : m.ctx.lookup (.name name) = some .clock) :
      env name = some .clock := by
    obtain ⟨p, hp, rfl, input, _⟩ := clock_port m name found
    rw [outside _ (input_not_allocated raw t h m hm p hp input),
      coreAt_clock raw t h m hm sol _ found]
  refine ⟨?_, clocks⟩
  have named (x : String) (stmt : Typed.Stmt m.ctx m.interfaces)
      (hs : stmt ∈ Lower.statements m) (letName : LetName stmt = some x)
      (aliased : ¬ match stmt with
        | .let_ _ _ _ e | .assign _ _ _ _ e => NotAliased e
        | _ => False) :
      x ∉ allocatedNames (finalState m) := by
    intro alloc
    obtain ⟨stmt', hs', named', result'⟩ := source_not_allocated m x
      (letName_legal raw t h m hm stmt hs x letName) alloc
    have same := filterMap_unique (letNames_nodup raw t h m hm) hs' hs x named' letName
    subst same
    rcases result' with ⟨i, hi⟩ | fresh'
    · have legal := letName_legal raw t h m hm stmt' hs x letName
      rw [List.singleton_inj.mp hi, temporary_invalid] at legal
      cases legal
    · apply aliased
      cases stmt' <;> simp_all
  have main : ∀ n node w found, valueRank m node = n →
      env (Lower.valueName (Lower.registers m) node) = some (.bits w (sol node w found)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    intro node w found rank
    have fallback (absent : Lower.valueName (Lower.registers m) node ∉
        allocatedNames (finalState m)) :
        env (Lower.valueName (Lower.registers m) node) = some (.bits w (sol node w found)) := by
      rw [outside _ absent, coreAt_node raw t h m hm sol node w found]
    obtain ⟨driver⟩ := valueDriver_exists t (certified raw t h).wellFormed m hm node w found
    cases driver with
    | input p member dir bits =>
      apply fallback
      rw [valueName_plain _ _ (port_not_register raw t h m hm p member)]
      exact input_not_allocated raw t h m hm p member dir
    | reg i p x _ clk target reset ni np next member =>
      apply fallback
      have inRegs : x ∈ Lower.registers m := List.mem_filterMap.mpr ⟨_, member, rfl⟩
      have contains : (Lower.registers m).contains x = true := by simpa using inRegs
      simp only [Lower.valueName, contains, ↓reduceIte]
      exact register_not_allocated raw t h m hm i p x w clk target reset ni np next member
    | inst i p x child conns member port portMember dir bits =>
      have hs := statement_of_part m _ member (i, .inst p x child conns) (by
        simp [Typed.Equation.parts])
      have binding := insts _ hs (s!"{x}.{port.name}", coreAt m sol s!"{x}.{port.name}") (by
        simp only [instBindings, instResults_filter, List.map_map, List.mem_map]
        exact ⟨port, List.mem_filter.mpr ⟨portMember, by simp [dir]⟩, rfl⟩)
      have value : env s!"{x}.{port.name}" = _ := agree _ binding
      simp only [Lower.valueName]
      rw [value]
      have := coreAt_node raw t h m hm sol (.port x port.name) w found
      simp only [Lower.valueName] at this
      rw [this]
    | let_ index pos x _ e member =>
      have hs := statement_of_part m _ member (index, .let_ pos x w e) (by
        simp [Typed.Equation.parts])
      rw [valueName_plain _ _ (letName_not_register raw t h m hm _ hs x rfl)]
      by_cases fresh : NotAliased e
      · obtain ⟨s₀, _, post⟩ := lets _ hs
        have inputs := expressionInputs_of_reads (Lower.registers m) sol env e
          (fun dep hdep w' found' => ih _ (rank ▸ let_read_rank m index pos x w e member dep hdep)
            dep w' found' rfl) clocks
        have value := post env agree inputs
        change env (Lower.expr (Lower.registers m) e (some x) s₀).1 = _ at value
        rw [expr_fresh_result _ e fresh x s₀] at value
        rw [value, letSolves index pos x w e member found]
        rfl
      · have absent := named x _ hs rfl fresh
        have := fallback (by
          rwa [valueName_plain _ _ (letName_not_register raw t h m hm _ hs x rfl)])
        rwa [valueName_plain _ _ (letName_not_register raw t h m hm _ hs x rfl)] at this
    | assign index pos x _ target e member =>
      have hs := statement_of_part m _ member (index, .assign pos x w target e) (by
        simp [Typed.Equation.parts])
      rw [valueName_plain _ _ (letName_not_register raw t h m hm _ hs x rfl)]
      by_cases fresh : NotAliased e
      · obtain ⟨s₀, _, post⟩ := lets _ hs
        have inputs := expressionInputs_of_reads (Lower.registers m) sol env e
          (fun dep hdep w' found' => ih _ (rank ▸ assign_read_rank m index pos x w target e member
            dep hdep) dep w' found' rfl) clocks
        have value := post env agree inputs
        change env (Lower.expr (Lower.registers m) e (some x) s₀).1 = _ at value
        rw [expr_fresh_result _ e fresh x s₀] at value
        rw [value, assignSolves index pos x w target e member found]
        rfl
      · have absent := named x _ hs rfl fresh
        have := fallback (by
          rwa [valueName_plain _ _ (letName_not_register raw t h m hm _ hs x rfl)])
        rwa [valueName_plain _ _ (letName_not_register raw t h m hm _ hs x rfl)] at this
  exact fun node w found => main _ node w found rfl

end

end Silicon.Core.LowerProof
