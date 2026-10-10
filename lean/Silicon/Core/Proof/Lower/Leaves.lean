import Silicon.Core.Proof.Lower.Context

/-!
Ports, registers, memory reads, and instance results have their declared types in the
lowered module, and each keeps its name.
-/
namespace Silicon.Core.LowerProof

theorem statement_of_eq (m : Typed.Module) (stmt : Typed.Stmt m.ctx m.interfaces) :
    stmt ∈ Lower.statements m ↔ ∃ eq ∈ m.body, ∃ part ∈ eq.parts, part.2 = stmt := by
  unfold Lower.statements
  rw [List.mem_map]
  constructor
  · rintro ⟨part, hp, rfl⟩
    obtain ⟨eq, he, hp⟩ := List.mem_flatMap.mp ((List.mergeSort_perm _ _).mem_iff.mp hp)
    exact ⟨eq, he, part, hp, rfl⟩
  · rintro ⟨eq, he, part, hp, rfl⟩
    exact ⟨part, (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_flatMap.mpr ⟨eq, he, hp⟩), rfl⟩

theorem eq_of_raw (m : Typed.Module) (stmt : Core.Stmt) (hs : stmt ∈ m.erase.body) :
    ∃ eq ∈ m.body, ∃ part ∈ eq.parts, part.2.erase = stmt := by
  obtain ⟨typed, ht, rfl⟩ := typed_of_raw m stmt hs
  obtain ⟨eq, he, part, hp, rfl⟩ := (statement_of_eq m typed).mp ht
  exact ⟨eq, he, part, hp, rfl⟩

theorem result_invalid (owner pin : String) :
    Rules.invalidName s!"{owner}.{pin}" = true := by
  by_cases legal : Rules.invalidName s!"{owner}.{pin}" = false
  · exact absurd rfl (source_ne_result _ owner pin legal)
  · simpa using legal

theorem lookup_some_of_mem {l : List (String × β)} {k : String} {v : β} (h : (k, v) ∈ l) :
    ∃ v', l.lookup k = some v' := by
  induction l with
  | nil => cases h
  | cons head tail ih =>
    obtain ⟨k', v''⟩ := head
    by_cases same : k = k'
    · exact ⟨v'', by simp [List.lookup, same]⟩
    · rcases List.mem_cons.mp h with eq | h
      · cases eq; exact absurd rfl same
      · obtain ⟨w, hw⟩ := ih h
        exact ⟨w, by simp [List.lookup, show (k == k') = false from beq_eq_false_iff_ne.mpr same,
          hw]⟩

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

theorem reads_has (r : Lower.ReadPort) (hr : r ∈ (Lower.statementState m).reads) (w depth : Nat)
    (found : m.ctx.lookup (.name r.memory) = some (.memory w depth)) :
    Has m (readName r) (.int w) := by
  apply has_of_mem raw t h m hm _ _ (rename_invalid raw t h m hm _ (readName_invalid r))
  have member := lookup_member _ _ _ found
  rw [m.context_eq] at member
  rcases context_member _ _ _ _ member with ⟨p, _, _, kind⟩ | ⟨stmt, hs, decl⟩
  · unfold portKind at kind
    split at kind <;> cases kind
  · cases stmt with
    | mem p' n w' depth' clk =>
      obtain ⟨same, kind⟩ := decl
      cases same
      cases kind
      obtain ⟨eq, he, part, hp, erased⟩ := eq_of_raw m _ hs
      cases eq with
      | mem i p'' n'' w'' depth'' clk'' target ws =>
        simp only [Typed.Equation.parts, List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨wr, _, rfl⟩
        · cases erased
          let sorted := ((Lower.statementState m).reads.filter (·.memory == r.memory)).mergeSort
            (·.index ≤ ·.index)
          have inSorted : r ∈ sorted := (List.mergeSort_perm _ _).mem_iff.mpr
            (List.mem_filter.mpr ⟨hr, by simp⟩)
          apply defs_body m _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨_, he, rfl⟩, rfl⟩)))
          simp only [Mlir.Op.resultTypes, List.map_map, List.zip_map', List.mem_map]
          exact ⟨r, inSorted, rfl⟩
        · cases erased
      | _ =>
        simp only [Typed.Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
        all_goals (rcases hp with rfl | rfl <;> cases erased)
    | let_ | reg => obtain ⟨_, kind⟩ := decl; cases kind
    | inst => obtain ⟨_, _, _, same, _⟩ := decl; cases same
    | _ => exact decl.elim

theorem clocks_has (n : String) (found : m.ctx.lookup (.name n) = some .clock) :
    Has m n .clock := by
  have member := lookup_member _ _ _ found
  rw [m.context_eq] at member
  rcases context_member _ _ _ _ member with ⟨p, hp, same, kind⟩ | ⟨stmt, hs, decl⟩
  · cases same
    unfold portKind at kind
    split at kind
    next hc =>
      have hc' : p.ty = .clock ∧ p.dir = .input := by simpa using hc
      have input := defs_input m p hp hc'.2
      rw [hc'.1] at input
      exact has_of_mem raw t h m hm _ _
        (rename_other raw t h m hm _ (input_not_letName raw t h m hm p hp hc'.2)) input
    next => cases kind
  · cases stmt with
    | let_ | reg => obtain ⟨_, kind⟩ := decl; cases kind
    | mem => obtain ⟨_, kind⟩ := decl; cases kind
    | inst => obtain ⟨_, _, _, same, _⟩ := decl; cases same
    | _ => exact decl.elim

omit h hm in
theorem run_state (m : Typed.Module) :
    Lower.statementState m =
      ((do for stmt in Lower.statements m do Lower.statement (Lower.registers m) stmt) {}).2 :=
  rfl

omit h hm in
theorem presence (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m) :
    ∃ s, Grows (Lower.statement (Lower.registers m) stmt s).2 (Lower.statementState m) := by
  rw [run_state]
  exact statements_presence _ _ _ stmt hs

theorem register_has (i : Nat) (p : Pos) (n : String) (w : Nat) (clk : String)
    (target : Typed.valueTy m.ctx n = some (.bits w)) (reset : Option (Typed.Reset m.ctx w))
    (ni : Nat) (np : Pos) (next : Typed.Expr m.ctx (.bits w))
    (he : .reg i p n w clk target reset ni np next ∈ m.body) :
    Has m s!"silicon_reg_{n}" (.int w) := by
  apply has_of_mem raw t h m hm _ _ (rename_invalid raw t h m hm _ (register_invalid n))
  have hs : Typed.Stmt.next np n w target next ∈ Lower.statements m :=
    (statement_of_eq m _).mpr ⟨_, he, (ni, .next np n w target next), by
      simp [Typed.Equation.parts], rfl⟩
  obtain ⟨s, grows⟩ := presence m _ hs
  have pushed : (n, (Lower.expr (Lower.registers m) next none s).1) ∈
      (Lower.statement (ports := m.interfaces) (Lower.registers m)
        (.next np n w target next) s).2.nexts :=
    List.mem_cons_self ..
  obtain ⟨x, hx⟩ := lookup_some_of_mem (grows.nexts.subset pushed)
  apply defs_body m _ (List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, he, by
    simp only [hx]; rfl⟩))
  exact List.mem_singleton_self _

omit h hm in
theorem instance_present (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m)
    (inst : String) (named : stmtInstances stmt = [inst]) :
    ∃ e ∈ (Lower.statementState m).body.toList, InstShape stmt e := by
  obtain ⟨s, grows⟩ := presence m stmt hs
  obtain ⟨⟨tail, body, insts, shapes⟩, _⟩ := statement_step (Lower.registers m) stmt s
  rw [named] at insts
  obtain ⟨e, he, found⟩ := List.mem_filterMap.mp (insts ▸ List.mem_singleton_self inst :
    inst ∈ tail.filterMap instName)
  have isInst : isInstance e.2 = true := by
    unfold instName at found
    unfold isInstance
    split at found <;> simp_all
  refine ⟨e, grows.body.subset ?_, shapes e he isInst⟩
  rw [body]
  exact List.mem_append_right _ he

theorem instport_has (p : Pos) (i child : String) (xs : List (String × Core.Expr))
    (hs : Core.Stmt.inst p i child xs ∈ m.erase.body) (port : Port)
    (hp : port ∈ m.interfaces child) (output : port.dir = .output) (w : Nat)
    (ty : port.ty = .bits w) : Has m s!"{i}.{port.name}" (.int w) := by
  apply has_of_mem raw t h m hm _ _ (rename_invalid raw t h m hm _ (result_invalid i port.name))
  obtain ⟨typed, ht, erased⟩ := typed_of_raw m _ hs
  cases typed <;> simp only [Typed.Stmt.erase, reduceCtorEq] at erased
  case inst p' i' child' inputs =>
    obtain ⟨_, rfl, rfl, _⟩ := Core.Stmt.inst.inj erased
    obtain ⟨e, he, args, _, rfl⟩ := instance_present m _ ht i' rfl
    apply defs_body m _ (List.mem_append_left _ (List.mem_append_left _ he))
    simp only [Mlir.Op.resultTypes, List.zip_map', List.mem_map]
    refine ⟨(port.name, Lower.type port.ty), List.mem_filterMap.mpr ⟨port, hp, ?_⟩, ?_⟩
    · simp [output]
    · simp [ty, Lower.type]

end

end Silicon.Core.LowerProof
