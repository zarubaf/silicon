import Silicon.Core.Proof.Lower.Emission
import Std.Data.String.ToNat

/-! Definition counts connect the emission image to fresh result names. -/
namespace Silicon.Core.LowerProof

theorem accounts_nodup (image : Image) (before after : Lower.State)
    (accounts : image.Accounts before after)
    (fresh : (image.map Prod.fst ++ allocatedNames before).Nodup) :
    (allocatedNames after).Nodup := by
  apply List.nodup_iff_count.mpr
  intro name
  rw [← accounts name]
  have bound := List.nodup_iff_count.mp fresh name
  simpa only [List.count_append] using bound

theorem temporary_name_injective {i j : Nat}
    (h : s!"silicon_t{i}" = s!"silicon_t{j}") : i = j := by
  apply Nat.repr_injective
  exact String.append_right_inj "silicon_t" |>.mp h

theorem register_name_injective {a b : String}
    (h : s!"silicon_reg_{a}" = s!"silicon_reg_{b}") : a = b :=
  String.append_right_inj "silicon_reg_" |>.mp h

theorem source_ne_internal (name suffix : String)
    (legal : Rules.reservedName name = false) : name ≠ "silicon_" ++ suffix := by
  intro same
  subst name
  simp [Rules.reservedName, String.toList_append] at legal

theorem source_ne_result (name owner pin : String)
    (legal : Rules.reservedName name = false) : name ≠ s!"{owner}.{pin}" := by
  intro same
  change name = owner ++ "." ++ pin at same
  subst name
  simp [Rules.reservedName, String.contains_char_eq, String.toList_append] at legal

private theorem separated_append_injective {a b c d : List Char}
    (ha : '.' ∉ a) (hb : '.' ∉ b) (h : a ++ '.' :: c = b ++ '.' :: d) :
    a = b ∧ c = d := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons x xs =>
      have hx : x = '.' := (List.cons.inj h).1.symm
      subst x
      simp at hb
  | cons x xs ih =>
    cases b with
    | nil =>
      have hx : x = '.' := (List.cons.inj h).1
      subst x
      simp at ha
    | cons y ys =>
      obtain ⟨rfl, ht⟩ := List.cons.inj h
      obtain ⟨rfl, rfl⟩ := ih (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h)) ht
      exact ⟨rfl, rfl⟩

theorem result_name_injective {a b p q : String}
    (ha : Rules.reservedName a = false) (hb : Rules.reservedName b = false)
    (h : s!"{a}.{p}" = s!"{b}.{q}") : a = b ∧ p = q := by
  have na : '.' ∉ a.toList := by
    simpa [Rules.reservedName, String.contains_char_eq] using (Bool.or_eq_false_iff.mp ha).2
  have nb : '.' ∉ b.toList := by
    simpa [Rules.reservedName, String.contains_char_eq] using (Bool.or_eq_false_iff.mp hb).2
  have chars := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at chars
  have pairs := separated_append_injective na nb chars
  exact ⟨String.toList_inj.mp pairs.1, String.toList_inj.mp pairs.2⟩

theorem read_name_injective {a b : String} {i j : Nat}
    (ha : Rules.reservedName a = false) (hb : Rules.reservedName b = false)
    (h : s!"{a}.r{i}_data" = s!"{b}.r{j}_data") : a = b ∧ i = j := by
  have pair := result_name_injective ha hb (p := s!"r{i}_data") (q := s!"r{j}_data") (by
    change a ++ "." ++ ("r" ++ i.repr ++ "_data") =
      b ++ "." ++ ("r" ++ j.repr ++ "_data")
    change a ++ ("." ++ "r") ++ i.repr ++ "_data" =
      b ++ ("." ++ "r") ++ j.repr ++ "_data" at h
    simpa only [String.append_assoc] using h)
  refine ⟨pair.1, Nat.repr_injective ?_⟩
  exact String.append_right_inj "r" |>.mp
    (String.append_left_inj "_data" |>.mp pair.2)

private theorem temporary_no_dot (i : Nat) : '.' ∉ (s!"silicon_t{i}").toList := by
  change '.' ∉ ("silicon_t" ++ i.repr).toList
  simp only [String.toList_append, List.mem_append, not_or]
  refine ⟨by decide, ?_⟩
  intro member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10)
    (by decide : 10 ≤ 10)
    (show '.' ∈ Nat.toDigits 10 i from by simpa only [Nat.toList_repr] using member)
  contradiction

private theorem temporary_ne_result (i : Nat) (owner pin : String) :
    s!"silicon_t{i}" ≠ s!"{owner}.{pin}" := by
  intro same
  have absent := temporary_no_dot i
  rw [same] at absent
  change '.' ∉ (owner ++ "." ++ pin).toList at absent
  simp [String.toList_append] at absent

private def readCount (s : Lower.State) (name : String) : Nat :=
  (s.readCounts.lookup name).getD 0

private def Future (memories : String → Prop) (s : Lower.State) (name : String) : Prop :=
  (∃ i, s.nextTemp ≤ i ∧ name = s!"silicon_t{i}") ∨
  (∃ memory i, Rules.reservedName memory = false ∧
    memories memory ∧ readCount s memory ≤ i ∧ name = s!"{memory}.r{i}_data")

private def Fresh (memories : String → Prop) (s : Lower.State) (pending : List String) : Prop :=
  (allocatedNames s ++ pending).Nodup ∧
    ∀ name, Future memories s name → name ∉ allocatedNames s ++ pending

variable {memories : String → Prop}

private theorem fresh_drop (s : Lower.State) (a b : List String)
    (h : Fresh memories s (a ++ b)) : Fresh memories s b := by
  have sub : (allocatedNames s ++ b).Sublist (allocatedNames s ++ (a ++ b)) :=
    (List.sublist_append_right a b).append_left _
  exact ⟨h.1.sublist sub, fun name future member => h.2 name future (sub.subset member)⟩

private theorem fresh_named (s : Lower.State) (pending : List String)
    (dest : Option String) (value : String) (h : Fresh memories s (dest.toList ++ pending)) :
    Fresh memories (Lower.named dest value s).2 pending := by
  cases dest with
  | none => exact h
  | some name => exact fresh_drop s [name] pending h

private theorem fresh_transfer (s t : Lower.State) (pending rest : List String)
    (h : Fresh memories s pending)
    (perm : (allocatedNames t ++ rest).Perm (allocatedNames s ++ pending))
    (future : ∀ name, Future memories t name → Future memories s name) : Fresh memories t rest := by
  exact ⟨perm.nodup_iff.mpr h.1,
    fun name hn hm => h.2 name (future name hn) (perm.mem_iff.mp hm)⟩

private theorem fresh_push (s : Lower.State) (names pending : List String) (op : Mlir.Op)
    (h : Fresh memories s (names ++ pending)) :
    Fresh memories { s with body := s.body.push (names, op) } pending := by
  apply fresh_transfer s _ _ _ h
  · simp only [allocatedNames, Array.toList_push, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simpa only [List.append_assoc] using
      ((List.perm_append_comm : (names ++ s.reads.map
        (fun r => s!"{r.memory}.r{r.index}_data")).Perm
        (s.reads.map (fun r => s!"{r.memory}.r{r.index}_data") ++ names)).append_right
          pending).append_left (s.body.toList.flatMap Prod.fst)
  · exact fun _ hn => hn

private theorem fresh_temp (s : Lower.State) (pending : List String)
    (h : Fresh memories s pending) :
    Fresh memories { s with nextTemp := s.nextTemp + 1 }
      (s!"silicon_t{s.nextTemp}" :: pending) := by
  let name := s!"silicon_t{s.nextTemp}"
  have absent := h.2 name (Or.inl ⟨s.nextTemp, Nat.le_refl _, rfl⟩)
  have perm : (allocatedNames s ++ name :: pending).Perm
      (name :: (allocatedNames s ++ pending)) := List.perm_middle
  refine ⟨perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨absent, h.1⟩), ?_⟩
  intro other future member
  have old : Future memories s other := by
    rcases future with ⟨i, hi, rfl⟩ | ⟨memory, i, legal, allowed, hi, rfl⟩
    · exact Or.inl ⟨i, by dsimp at hi; omega, rfl⟩
    · exact Or.inr ⟨memory, i, legal, allowed, hi, rfl⟩
  have ne : other ≠ name := by
    rcases future with ⟨i, hi, rfl⟩ | ⟨memory, i, _, _, _, rfl⟩
    · intro eq
      have same := temporary_name_injective eq
      dsimp at hi
      omega
    · exact fun eq => temporary_ne_result s.nextTemp memory s!"r{i}_data" (by
        change "silicon_t" ++ s.nextTemp.repr = memory ++ "." ++ ("r" ++ i.repr ++ "_data")
        change memory ++ ("." ++ "r") ++ i.repr ++ "_data" =
          "silicon_t" ++ s.nextTemp.repr at eq
        simpa only [String.append_assoc] using eq.symm)
  rcases List.mem_cons.mp (perm.mem_iff.mp member) with same | member
  · exact ne same
  · exact h.2 other old member

private theorem fresh_emit (s : Lower.State) (pending : List String)
    (dest : Option String) (op : Mlir.Op) (h : Fresh memories s (dest.toList ++ pending)) :
    Fresh memories (Lower.emit dest op s).2 pending := by
  cases dest with
  | none => exact fresh_push _ _ _ op (fresh_temp s pending h)
  | some name => exact fresh_push s [name] pending op h

private theorem fresh_reserve (s : Lower.State) (pending : List String) (memory : String)
    (legal : Rules.reservedName memory = false) (allowed : memories memory)
    (h : Fresh memories s pending) :
    Fresh memories { s with readCounts := (memory, readCount s memory + 1) :: s.readCounts }
      (s!"{memory}.r{readCount s memory}_data" :: pending) := by
  let name := s!"{memory}.r{readCount s memory}_data"
  have absent := h.2 name (Or.inr ⟨memory, readCount s memory, legal, allowed, Nat.le_refl _, rfl⟩)
  have perm : (allocatedNames s ++ name :: pending).Perm
      (name :: (allocatedNames s ++ pending)) := List.perm_middle
  refine ⟨perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨absent, h.1⟩), ?_⟩
  intro other future member
  have old : Future memories s other := by
    rcases future with ⟨i, hi, rfl⟩ | ⟨mem, i, valid, allowed, hi, rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · refine Or.inr ⟨mem, i, valid, allowed, ?_, rfl⟩
      by_cases eq : memory = mem
      · subst mem
        simp [readCount] at hi ⊢
        omega
      · simpa [readCount, List.lookup, show (mem == memory) = false from
          beq_eq_false_iff_ne.mpr (Ne.symm eq)] using hi
  have ne : other ≠ name := by
    rcases future with ⟨i, _, rfl⟩ | ⟨mem, i, valid, allowed, hi, rfl⟩
    · exact fun eq => temporary_ne_result i memory s!"r{readCount s memory}_data" (by
        change "silicon_t" ++ i.repr =
          memory ++ "." ++ ("r" ++ (readCount s memory).repr ++ "_data")
        change "silicon_t" ++ i.repr =
          memory ++ ("." ++ "r") ++ (readCount s memory).repr ++ "_data" at eq
        simpa only [String.append_assoc] using eq)
    · intro eq
      obtain ⟨rfl, same⟩ := read_name_injective valid legal eq
      simp [readCount] at hi
      dsimp [readCount] at same
      omega
  rcases List.mem_cons.mp (perm.mem_iff.mp member) with same | member
  · exact ne same
  · exact h.2 other old member

private theorem fresh_read (s : Lower.State) (pending : List String) (r : Lower.ReadPort)
    (h : Fresh memories s (s!"{r.memory}.r{r.index}_data" :: pending)) :
    Fresh memories { s with reads := r :: s.reads } pending := by
  apply fresh_transfer s _ _ _ h
  · simp only [allocatedNames, List.map_cons, List.append_assoc]
    exact (List.perm_middle (a := s!"{r.memory}.r{r.index}_data")).symm.append_left _
  · exact fun _ hn => hn

private theorem fresh_inRange (s : Lower.State) (pending : List String) (depth : Nat)
    (addr : String) (h : Fresh memories s pending) :
    Fresh memories (Lower.inRange depth addr s).2 pending := by
  unfold Lower.inRange
  split
  · exact h
  · exact fresh_emit _ pending none _ (fresh_emit s pending none _ h)

private def ReadNamesLegal (memories : String → Prop) : Typed.Expr ctx ty → Prop
  | .read _ name _ addr =>
      Rules.reservedName name = false ∧ memories name ∧ ReadNamesLegal memories addr
  | .un _ _ a | .extract _ a .. | .replicate _ a .. => ReadNamesLegal memories a
  | .bin _ _ _ a b | .concat _ a b _ | .icmp _ _ a b =>
      ReadNamesLegal memories a ∧ ReadNamesLegal memories b
  | .mux _ c a b =>
      ReadNamesLegal memories c ∧ ReadNamesLegal memories a ∧ ReadNamesLegal memories b
  | _ => True

private theorem fresh_expr (registers : List String) (e : Typed.Expr ctx ty)
    (legal : ReadNamesLegal memories e) (s : Lower.State)
    (pending : List String) (dest : Option String)
    (h : Fresh memories s (dest.toList ++ pending)) :
    Fresh memories (Lower.expr registers e dest s).2 pending := by
  induction e generalizing s pending dest with
  | ref p node found => exact fresh_named s pending dest _ h
  | clock p name found => exact fresh_drop s dest.toList pending h
  | const p w v => exact fresh_emit s pending dest _ h
  | un p op a ih =>
    cases op
    exact fresh_emit _ pending dest _ (fresh_emit _ _ none _ (ih legal s _ none h))
  | bin p op ordinary a b ia ib =>
    exact fresh_emit _ pending dest _ (ib legal.2 _ _ none (ia legal.1 s _ none h))
  | concat p a b bound ia ib =>
    exact fresh_emit _ pending dest _ (ib legal.2 _ _ none (ia legal.1 s _ none h))
  | icmp p pred a b ia ib =>
    exact fresh_emit _ pending dest _ (ib legal.2 _ _ none (ia legal.1 s _ none h))
  | mux p c a b ic ia ib =>
    exact fresh_emit _ pending dest _
      (ib legal.2.2 _ _ none (ia legal.2.1 _ _ none (ic legal.1 s _ none h)))
  | extract p a lo count bound ih => exact fresh_emit _ pending dest _ (ih legal s _ none h)
  | replicate p a count bound ih => exact fresh_emit _ pending dest _ (ih legal s _ none h)
  | @read width depth p name found addr ih =>
    let index := readCount s name
    let reserved := { s with readCounts := (name, index + 1) :: s.readCounts }
    let walked := Lower.expr registers addr none reserved
    let recorded := { walked.2 with reads := ⟨name, index, walked.1⟩ :: walked.2.reads }
    have hx := ih legal.2.2 reserved _ none (fresh_reserve s _ name legal.1 legal.2.1 h)
    have hr := fresh_read walked.2 _ ⟨name, index, walked.1⟩ hx
    have hg := fresh_inRange recorded _ depth walked.1 hr
    change Fresh memories ((match (Lower.inRange depth walked.1 recorded).1 with
      | none => Lower.named dest s!"{name}.r{index}_data"
      | some ok => (do
          let zero ← Lower.emit none (.constant width 0)
          Lower.emit dest (.mux ok s!"{name}.r{index}_data" zero (.int width))))
        (Lower.inRange depth walked.1 recorded).2).2 pending
    cases eq : Lower.inRange depth walked.1 recorded with
    | mk result state =>
      rw [eq] at hg
      cases result with
      | none => exact fresh_named state pending dest _ hg
      | some ok => exact fresh_emit _ pending dest _ (fresh_emit state _ none _ hg)

private theorem fresh_mapM (xs : List α) (f : α → Lower.Build β)
    (s : Lower.State) (pending : List String)
    (preserves : ∀ x ∈ xs, ∀ state, Fresh memories state pending →
      Fresh memories (f x state).2 pending)
    (h : Fresh memories s pending) : Fresh memories (xs.mapM f s).2 pending := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact ih _ (fun a ha => preserves a (List.mem_cons_of_mem _ ha))
      (preserves x (List.mem_cons_self ..) s h)

private def statementNames : Typed.Stmt ctx ports → List String
  | .let_ _ name .. | .assign _ name .. => [name]
  | .inst _ name child _ => ((ports child).filterMap fun p =>
      if p.dir == .output then some (p.name, Lower.type p.ty) else none).map
        fun p => s!"{name}.{p.1}"
  | _ => []

private def StatementReadsLegal (memories : String → Prop) : Typed.Stmt ctx ports → Prop
  | .let_ _ _ _ e | .assign _ _ _ _ e | .next _ _ _ _ e => ReadNamesLegal memories e
  | .reg _ _ _ _ reset => ∀ r ∈ reset.toList,
      ReadNamesLegal memories r.signal ∧ ReadNamesLegal memories r.value
  | .write _ _ _ _ _ _ a d e =>
      ReadNamesLegal memories a ∧ ReadNamesLegal memories d ∧ ReadNamesLegal memories e
  | .inst _ _ _ inputs => ∀ i ∈ inputs, ReadNamesLegal memories i.2
  | _ => True

set_option maxHeartbeats 1000000 in
private theorem fresh_statement (registers : List String) (stmt : Typed.Stmt ctx ports)
    (legal : StatementReadsLegal memories stmt) (s : Lower.State) (pending : List String)
    (h : Fresh memories s (statementNames stmt ++ pending)) :
    Fresh memories (Lower.statement registers stmt s).2 pending := by
  cases stmt with
  | let_ p name w e | assign p name w target e =>
    exact fresh_expr registers e legal s pending (some name) h
  | next p name w target e => exact fresh_expr registers e legal s pending none h
  | mem => exact h
  | reg p name w clk reset =>
    cases reset with
    | none => exact h
    | some r =>
      have hr := legal r (List.mem_singleton_self r)
      exact fresh_expr registers r.value hr.2 _ pending none
        (fresh_expr registers r.signal hr.1 s pending none h)
  | write p name index w depth target addr data enable =>
    let a := Lower.expr registers addr none s
    let d := Lower.expr registers data none a.2
    let e := Lower.expr registers enable none d.2
    have hx := fresh_expr registers enable legal.2.2 _ pending none
      (fresh_expr registers data legal.2.1 _ pending none
        (fresh_expr registers addr legal.1 s pending none h))
    have hg := fresh_inRange e.2 pending depth a.1 hx
    let finish : String → Lower.Build Unit := fun enable =>
      modify fun state => { state with
        writes := ⟨name, index, a.1, d.1, enable⟩ :: state.writes }
    change Fresh memories ((match (Lower.inRange depth a.1 e.2).1 with
      | none => (pure e.1 >>= finish)
      | some ok => (Lower.emit none (.comb .and e.1 ok 1) >>= finish))
        (Lower.inRange depth a.1 e.2).2).2 pending
    cases eq : Lower.inRange depth a.1 e.2 with
    | mk result state =>
      rw [eq] at hg
      cases result with
      | none => exact hg
      | some ok => exact fresh_emit state pending none _ hg
  | inst p name child inputs =>
    apply fresh_push
    exact fresh_mapM inputs _ s _
      (fun i hi state hs => fresh_expr registers i.2 (legal i hi) state _ none hs) h

private def Owned (owner name : String) : Prop :=
  name = owner ∨ name = s!"silicon_reg_{owner}" ∨ ∃ pin : String, name = s!"{owner}.{pin}"

private theorem register_no_dot (owner : String) (legal : Rules.reservedName owner = false) :
    '.' ∉ (s!"silicon_reg_{owner}").toList := by
  change '.' ∉ ("silicon_reg_" ++ owner).toList
  have absent := (Bool.or_eq_false_iff.mp legal).2
  simp only [String.contains_char_eq, decide_eq_false_iff_not] at absent
  simpa [String.toList_append] using absent

private theorem register_ne_result (owner inst pin : String)
    (legal : Rules.reservedName owner = false) :
    s!"silicon_reg_{owner}" ≠ s!"{inst}.{pin}" := by
  intro eq
  have absent := register_no_dot owner legal
  rw [eq] at absent
  change '.' ∉ (inst ++ "." ++ pin).toList at absent
  simp [String.toList_append] at absent

private theorem owned_injective (a b name : String)
    (ha : Rules.reservedName a = false) (hb : Rules.reservedName b = false)
    (oa : Owned a name) (ob : Owned b name) : a = b := by
  rcases oa with oa | oa | ⟨p, oa⟩
  · subst name
    rcases ob with eq | eq | ⟨q, eq⟩
    · exact eq
    · exact False.elim (source_ne_internal a ("reg_" ++ b) ha (by
        change a = "silicon_" ++ ("reg_" ++ b)
        change a = ("silicon_" ++ "reg_") ++ b at eq
        simpa only [String.append_assoc] using eq))
    · exact False.elim (source_ne_result a b q ha eq)
  · subst name
    rcases ob with eq | eq | ⟨q, eq⟩
    · exact False.elim (source_ne_internal b ("reg_" ++ a) hb (by
        change b = "silicon_" ++ ("reg_" ++ a)
        change ("silicon_" ++ "reg_") ++ a = b at eq
        simpa only [String.append_assoc] using eq.symm))
    · exact register_name_injective eq
    · exact False.elim (register_ne_result a b q ha eq)
  · subst name
    rcases ob with eq | eq | ⟨q, eq⟩
    · exact False.elim (source_ne_result b a p hb eq.symm)
    · exact False.elim (register_ne_result b a p hb eq.symm)
    · exact (result_name_injective ha hb eq).1

private theorem owned_groups_nodup (groups : List (String × List String))
    (owners : (groups.map Prod.fst).Nodup)
    (valid : ∀ g ∈ groups, Rules.reservedName g.1 = false ∧ g.2.Nodup ∧
      ∀ name ∈ g.2, Owned g.1 name) : (groups.flatMap Prod.snd).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun g hg => (valid g hg).2.1, ?_⟩
  have pair := List.pairwise_map.mp owners
  apply (List.Pairwise.and_mem.mp pair).imp
  intro a b ⟨ha, hb, different⟩ x hx y hy eq
  subst y
  exact different (owned_injective a.1 b.1 x (valid a ha).1 (valid b hb).1
    ((valid a ha).2.2 x hx) ((valid b hb).2.2 x hy))

private theorem fresh_statements (registers : List String) (stmts : List (Typed.Stmt ctx ports))
    (legal : ∀ stmt ∈ stmts, StatementReadsLegal memories stmt)
    (s : Lower.State) (pending : List String)
    (h : Fresh memories s (stmts.flatMap statementNames ++ pending)) :
    Fresh memories ((do for stmt in stmts do Lower.statement registers stmt) s).2 pending := by
  induction stmts generalizing s with
  | nil => exact h
  | cons stmt stmts ih =>
    simp only [List.forIn_cons, bind_assoc, pure_bind]
    exact ih (fun st hs => legal st (List.mem_cons_of_mem _ hs)) _
      (fresh_statement registers stmt (legal stmt (List.mem_cons_self ..)) s _
        (by simpa only [List.flatMap_cons, List.append_assoc] using h))

private def rawNames (ports : String → List Port) : Core.Stmt → List String
  | .let_ _ name .. | .assign _ name .. => [name]
  | .reg _ name .. => [s!"silicon_reg_{name}"]
  | .inst _ name child _ => (ports child).filterMap fun p =>
      if p.dir == .output then some s!"{name}.{p.name}" else none
  | _ => []

private def rawGroups (ports : String → List Port) (body : List Core.Stmt) :=
  body.filterMap fun stmt => stmt.driverName.map fun name => (name, rawNames ports stmt)

private theorem rawGroups_owners (ports : String → List Port) (body : List Core.Stmt) :
    (rawGroups ports body).map Prod.fst = body.filterMap Stmt.driverName := by
  simp only [rawGroups, List.map_filterMap]
  congr 1
  funext stmt
  cases stmt <;> rfl

private theorem rawGroups_names (ports : String → List Port) (body : List Core.Stmt) :
    (rawGroups ports body).flatMap Prod.snd = body.flatMap (rawNames ports) := by
  induction body with
  | nil => rfl
  | cons stmt body ih => cases stmt <;> simp [rawGroups, Stmt.driverName, rawNames] at ih ⊢ <;>
      exact ih

private theorem rawNames_valid (ports : String → List Port)
    (unique : ∀ child, ((ports child).map Port.name).Nodup)
    (stmt : Core.Stmt) (name : String) (driver : stmt.driverName = some name) :
    (rawNames ports stmt).Nodup ∧ ∀ n ∈ rawNames ports stmt, Owned name n := by
  cases stmt <;> simp only [Stmt.driverName, Option.some.injEq] at driver
  all_goals try contradiction
  all_goals subst name
  case inst p name child inputs =>
    constructor
    · apply List.pairwise_filterMap.mpr
      apply (List.pairwise_map.mp (unique child)).imp
      intro a b ne x hx y hy eq
      split at hx <;> simp only [Option.some.injEq, reduceCtorEq] at hx
      rw [← hx] at eq
      split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hy
      rw [← hy] at eq
      exact ne (String.append_right_inj (name ++ ".") |>.mp eq)
    · intro n hn
      obtain ⟨port, _, hp⟩ := List.mem_filterMap.mp hn
      split at hp
      · cases hp
        exact Or.inr (Or.inr ⟨port.name, rfl⟩)
      · contradiction
  all_goals simp [rawNames, Owned]

theorem checked_driver_legal (d : Core.Design) (m : Core.Module)
    (wf : WellFormed d) (hm : m ∈ Typed.modules d) (stmt : Core.Stmt) (hs : stmt ∈ m.body)
    (name : String) (driver : stmt.driverName = some name) : Rules.reservedName name = false := by
  have mi : Core.Item.module m ∈ d.items := by
    obtain ⟨item, hi, he⟩ := List.mem_filterMap.mp hm
    cases item <;> simp_all [Typed.modules]
  have scope := (wf.1.2 (.module m) mi).2
  by_cases hd : Rules.definition stmt = some name
  · exact scope name (List.mem_append_right _ (List.mem_filterMap.mpr ⟨stmt, hs, hd⟩))
  cases stmt with
  | assign p n expr =>
    have same : n = name := Option.some.inj driver
    subst name
    have resolved := (wf.2.1.2 m hm (.assign p n expr) hs).1
    change ((Rules.findPort m n).any fun port => port.dir == .output) = true at resolved
    obtain ⟨port, found, _⟩ := (Option.any_eq_true _ _).mp resolved
    have member := List.mem_of_find?_eq_some found
    have named := (List.find?_some found)
    exact scope n (List.mem_append_left _
      (List.mem_map.mpr ⟨port, member, by simpa using named⟩))
  | _ => simp_all [Stmt.driverName, Rules.definition]

theorem interfaces_nodup (d : Core.Design) (wf : WellFormed d) (child : String) :
    ((Typed.portsOf d child).map Port.name).Nodup := by
  unfold Typed.portsOf
  cases found : d.items.find? (fun i => i.name == child) with
  | none => simp
  | some item => exact Check.ports_nodup d item wf.1 (List.mem_of_find?_eq_some found)

theorem context_memory_declaration (d : Core.Design) (m : Core.Module)
    (name : String) (width depth : Nat)
    (found : (Typed.context d m).lookup (.name name) = some (.memory width depth)) :
    ∃ p clk, Core.Stmt.mem p name width depth clk ∈ m.body := by
  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (Deps.Node.name name, Typed.Kind.memory width depth) ∈ Typed.context d m := by
    rw [eq]
    simp
  unfold Typed.context Typed.contextFromPorts at member
  rcases List.mem_append.mp member with hp | hs
  · obtain ⟨p, _, he⟩ := List.mem_map.mp hp
    split at he <;> cases he
  · obtain ⟨stmt, hs, he⟩ := List.mem_flatMap.mp hs
    cases stmt <;> simp only [List.mem_singleton] at he
    all_goals try contradiction
    case let_ => cases he
    case reg => cases he
    case mem p n w size clk =>
      cases he
      exact ⟨p, clk, hs⟩
    case inst p n child xs =>
      obtain ⟨port, _, he⟩ := List.mem_filterMap.mp he
      split at he <;> cases he

def inputNames (ports : List Port) : List String :=
  (ports.filter (·.dir == .input)).map Port.name

theorem input_drivers_nodup (d : Core.Design) (m : Core.Module)
    (wf : WellFormed d) (hm : m ∈ Typed.modules d) :
    (inputNames m.ports ++ m.body.filterMap Stmt.driverName).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(Check.module_ports_nodup d m wf hm).sublist (List.filter_sublist.map _),
    Check.module_driver_names_nodup d m wf hm, ?_⟩
  intro a ha b hb same
  subst b
  obtain ⟨port, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hp, hi⟩ := List.mem_filter.mp hp
  obtain ⟨stmt, hs, hd⟩ := List.mem_filterMap.mp hb
  exact Check.input_not_driver d wf m hm port hp (by simpa using hi) stmt hs hd

private theorem static_names_nodup (d : Core.Design) (m : Core.Module)
    (wf : WellFormed d) (hm : m ∈ Typed.modules d) :
    (inputNames m.ports ++ m.body.flatMap (rawNames (Typed.portsOf d))).Nodup := by
  let inputs := (m.ports.filter (·.dir == .input)).map fun p => (p.name, [p.name])
  have owners : ((inputs ++ rawGroups (Typed.portsOf d) m.body).map Prod.fst).Nodup := by
    simpa only [List.map_append, rawGroups_owners, inputs, inputNames,
      List.map_map, Function.comp_def]
      using input_drivers_nodup d m wf hm
  have result := owned_groups_nodup _ owners (by
    intro g hg
    rcases List.mem_append.mp hg with hp | hs
    · dsimp only [inputs] at hp
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp hp
      have mi : Core.Item.module m ∈ d.items := by
        obtain ⟨item, hi, he⟩ := List.mem_filterMap.mp hm
        cases item <;> simp_all [Typed.modules]
      refine ⟨(wf.1.2 (.module m) mi).2 port.name ?_, by simp, ?_⟩
      · exact List.mem_append_left _
          (List.mem_map.mpr ⟨port, (List.mem_filter.mp portMember).1, rfl⟩)
      · intro name hn
        exact Or.inl (List.mem_singleton.mp hn)
    · unfold rawGroups at hs
      obtain ⟨stmt, stmtMember, hd⟩ := List.mem_filterMap.mp hs
      obtain ⟨name, driver, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact ⟨checked_driver_legal d m wf hm stmt stmtMember name driver,
        rawNames_valid _ (interfaces_nodup d wf) stmt name driver⟩)
  simpa [List.flatMap_append, rawGroups_names, inputs, List.flatMap_map,
    Function.comp_def, ← List.map_eq_flatMap, inputNames] using result

private def rawRegisters : Core.Stmt → List String
  | .reg _ name .. => [s!"silicon_reg_{name}"]
  | _ => []

private def rawStatementNames (ports : String → List Port) : Core.Stmt → List String
  | .reg .. => []
  | stmt => rawNames ports stmt

theorem flatMap_split_perm (xs : List α) (f g : α → List β) :
    (xs.flatMap fun x => f x ++ g x).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    exact ((List.Perm.refl (f x)).append
      ((List.Perm.refl (g x)).append ih)).trans (by
        simpa only [List.append_assoc] using
          ((List.perm_append_comm (l₁ := g x) (l₂ := xs.flatMap f)).append_right
            (xs.flatMap g)).append_left (f x))

private theorem raw_names_split (ports : String → List Port) (body : List Core.Stmt) :
    (body.flatMap (rawNames ports)).Perm
      (body.flatMap rawRegisters ++ body.flatMap (rawStatementNames ports)) := by
  have same : rawNames ports = fun stmt => rawRegisters stmt ++ rawStatementNames ports stmt := by
    funext stmt
    cases stmt <;> rfl
  rw [same]
  exact flatMap_split_perm body _ _

theorem statements_erase (m : Typed.Module) :
    (Lower.statements m).map Typed.Stmt.erase = m.erase.body := by
  simp only [Lower.statements, List.map_map, Function.comp_def]
  rfl

private theorem statement_names_erase (stmt : Typed.Stmt ctx ports) :
    statementNames stmt = rawStatementNames ports stmt.erase := by
  cases stmt <;> try rfl
  simp only [statementNames, Typed.Stmt.erase, rawStatementNames, rawNames, List.map_filterMap]
  congr 1
  funext p
  split <;> rfl

private theorem statement_names (m : Typed.Module) :
    (Lower.statements m).flatMap statementNames =
      m.erase.body.flatMap (rawStatementNames m.interfaces) := by
  rw [← statements_erase m, List.flatMap_map]
  congr 1
  funext stmt
  exact statement_names_erase stmt

def MemoryName (m : Core.Module) (name : String) : Prop :=
  ∃ p w depth clk, Core.Stmt.mem p name w depth clk ∈ m.body

private theorem checked_read_names (d : Core.Design) (m : Typed.Module) (wf : WellFormed d)
    (hm : m.erase ∈ Typed.modules d) (context : m.ctx = Typed.context d m.erase)
    (e : Typed.Expr m.ctx ty) : ReadNamesLegal (MemoryName m.erase) e := by
  induction e with
  | read p name found addr ih =>
    have found' := found
    rw [context] at found'
    obtain ⟨p, clk, member⟩ := context_memory_declaration d m.erase name _ _ found'
    exact ⟨checked_driver_legal d m.erase wf hm _ member name rfl,
      ⟨p, _, _, clk, member⟩, ih⟩
  | ref | clock | const => trivial
  | un _ _ _ ih | extract _ _ _ _ _ ih | replicate _ _ _ _ ih => exact ih
  | bin _ _ _ _ _ ia ib | concat _ _ _ _ ia ib | icmp _ _ _ _ ia ib => exact ⟨ia, ib⟩
  | mux _ _ _ _ ic ia ib => exact ⟨ic, ia, ib⟩

private theorem checked_statement_reads (d : Core.Design) (m : Typed.Module)
    (wf : WellFormed d) (hm : m.erase ∈ Typed.modules d)
    (context : m.ctx = Typed.context d m.erase) (stmt : Typed.Stmt m.ctx m.interfaces) :
    StatementReadsLegal (MemoryName m.erase) stmt := by
  have legal : ∀ {ty}, ∀ e : Typed.Expr m.ctx ty,
      ReadNamesLegal (MemoryName m.erase) e := checked_read_names d m wf hm context
  cases stmt with
  | let_ | assign | next => exact legal _
  | reg => exact fun r _ => ⟨legal r.signal, legal r.value⟩
  | write => exact ⟨legal _, legal _, legal _⟩
  | inst => exact fun i _ => legal i.2
  | mem => trivial

private theorem temporary_ne_register (i : Nat) (name : String) :
    s!"silicon_t{i}" ≠ s!"silicon_reg_{name}" := by
  intro eq
  change "silicon_t" ++ i.repr = "silicon_reg_" ++ name at eq
  have chars := congrArg String.toList eq
  simp [String.toList_append] at chars

private theorem source_not_future (m : Core.Module) (name : String)
    (legal : Rules.reservedName name = false) : ¬ Future (MemoryName m) {} name := by
  rintro (⟨i, _, eq⟩ | ⟨owner, i, _, _, _, eq⟩)
  · exact source_ne_internal name ("t" ++ i.repr) legal (by
      change name = ("silicon_" ++ "t") ++ i.repr at eq
      simpa only [String.append_assoc] using eq)
  · exact source_ne_result name owner s!"r{i}_data" legal (by
      change name = owner ++ "." ++ ("r" ++ i.repr ++ "_data")
      change name = owner ++ ("." ++ "r") ++ i.repr ++ "_data" at eq
      simpa only [String.append_assoc] using eq)

private theorem static_name_not_future (d : Core.Design) (m : Core.Module)
    (wf : WellFormed d) (hm : m ∈ Typed.modules d) (stmt : Core.Stmt) (hs : stmt ∈ m.body)
    (name : String) (hn : name ∈ rawNames (Typed.portsOf d) stmt) :
    ¬ Future (MemoryName m) {} name := by
  have legal : ∀ owner, stmt.driverName = some owner → Rules.reservedName owner = false :=
    checked_driver_legal d m wf hm stmt hs
  cases stmt with
  | let_ p owner w e | assign p owner e =>
    have same := List.mem_singleton.mp hn
    subst name
    exact source_not_future m owner (legal owner rfl)
  | reg p owner w clk reset =>
    have same := List.mem_singleton.mp hn
    subst name
    rintro (⟨i, _, eq⟩ | ⟨memory, i, _, _, _, eq⟩)
    · exact temporary_ne_register i owner eq.symm
    · exact register_ne_result owner memory s!"r{i}_data" (legal owner rfl) (by
        change "silicon_reg_" ++ owner = memory ++ "." ++ ("r" ++ i.repr ++ "_data")
        change "silicon_reg_" ++ owner = memory ++ ("." ++ "r") ++ i.repr ++ "_data" at eq
        simpa only [String.append_assoc] using eq)
  | inst p owner child inputs =>
    obtain ⟨port, _, hp⟩ := List.mem_filterMap.mp hn
    split at hp
    next =>
      have same := Option.some.inj hp
      subst name
      rintro (⟨i, _, eq⟩ | ⟨memory, i, valid, allowed, _, eq⟩)
      · exact temporary_ne_result i owner port.name eq.symm
      · have pair := result_name_injective (legal owner rfl) valid
          (p := port.name) (q := s!"r{i}_data") (by
            change owner ++ "." ++ port.name = memory ++ "." ++ ("r" ++ i.repr ++ "_data")
            change owner ++ "." ++ port.name =
              memory ++ ("." ++ "r") ++ i.repr ++ "_data" at eq
            simpa only [String.append_assoc] using eq)
        obtain ⟨mp, mw, md, clk, member⟩ := allowed
        have mi : Core.Item.module m ∈ d.items := by
          obtain ⟨item, hi, he⟩ := List.mem_filterMap.mp hm
          cases item <;> simp_all [Typed.modules]
        have unique := (List.nodup_append.mp (wf.1.2 (.module m) mi).1).2.1
        have a := Check.find_definition m.body (.inst p owner child inputs) owner unique hs rfl
        have b := Check.find_definition m.body (.mem mp memory mw md clk) owner unique member
          (by simp [Rules.definition, pair.1])
        rw [a] at b
        cases b
    next => contradiction
  | _ => simp [rawNames] at hn

private theorem static_names_fresh (d : Core.Design) (m : Core.Module)
    (wf : WellFormed d) (hm : m ∈ Typed.modules d) :
    Fresh (MemoryName m) {}
      (inputNames m.ports ++ m.body.flatMap (rawNames (Typed.portsOf d))) := by
  refine ⟨static_names_nodup d m wf hm, ?_⟩
  intro name future member
  change name ∈ inputNames m.ports ++ m.body.flatMap (rawNames (Typed.portsOf d)) at member
  rcases List.mem_append.mp member with hp | hs
  · obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp hp
    have mi : Core.Item.module m ∈ d.items := by
      obtain ⟨item, hi, he⟩ := List.mem_filterMap.mp hm
      cases item <;> simp_all [Typed.modules]
    have legal := (wf.1.2 (.module m) mi).2 port.name
      (List.mem_append_left _ (List.mem_map.mpr ⟨port, (List.mem_filter.mp portMember).1, rfl⟩))
    exact source_not_future m port.name legal future
  · obtain ⟨stmt, hs, hn⟩ := List.mem_flatMap.mp hs
    exact static_name_not_future d m wf hm stmt hs name hn future

private theorem checked_statements_fresh (raw : Core.Design) (t : Typed.Design)
    (h : check raw = .ok t) (m : Typed.Module) (hm : m ∈ t.bodies)
    (registers : List String) :
    Fresh (MemoryName m.erase)
      ((do for stmt in Lower.statements m do Lower.statement registers stmt) {}).2
      (inputNames m.ports ++ m.erase.body.flatMap rawRegisters) := by
  have erase := check_sound_erase raw t h
  have wf := (check_sound raw t h).1
  have member : m.erase ∈ Typed.modules raw := by
    apply List.mem_filterMap.mpr
    exact ⟨.module m.erase, erase ▸ (t.environments m hm).2.2, rfl⟩
  have interfaces : m.interfaces = Typed.portsOf raw := by
    rw [← erase]
    exact (t.environments m hm).1
  have context : m.ctx = Typed.context raw m.erase := by
    rw [← erase]
    exact t.module_context m hm
  apply fresh_statements registers (Lower.statements m)
    (fun stmt _ => checked_statement_reads raw m wf member context stmt)
  have initial := static_names_fresh raw m.erase wf member
  apply fresh_transfer _ _ _ _ initial
  · change ((Lower.statements m).flatMap statementNames ++
      (inputNames m.ports ++ m.erase.body.flatMap rawRegisters)).Perm
        (inputNames m.ports ++ m.erase.body.flatMap (rawNames (Typed.portsOf raw)))
    rw [statement_names, interfaces]
    exact (List.perm_append_comm.trans (by
      simpa only [List.append_assoc] using
        (raw_names_split (Typed.portsOf raw) m.erase.body).symm.append_left (inputNames m.ports)))
  · exact fun _ hn => hn

private theorem flatMap_perm_congr (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, (f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    exact (h x (List.mem_cons_self ..)).append
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

private theorem filter_partition (keys : List String) (unique : keys.Nodup)
    (xs : List α) (key : α → String) :
    (keys.flatMap fun k => xs.filter (fun x => key x == k)).Perm
      (xs.filter fun x => keys.contains (key x)) := by
  have singleton (x : α) :
      (keys.flatMap fun k => if key x == k then [x] else []) =
        if key x ∈ keys then [x] else [] := by
    induction keys with
    | nil => simp
    | cons k keys ih =>
      have hn := List.nodup_cons.mp unique
      simp only [List.flatMap_cons, ih hn.2]
      by_cases same : key x = k <;> simp [same, hn.1]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have shape : (fun k => (x :: xs).filter (fun x => key x == k)) =
        (fun k => (if key x == k then [x] else []) ++ xs.filter (fun x => key x == k)) := by
      funext k
      by_cases same : key x = k <;> simp [same]
    rw [shape]
    have perm := flatMap_split_perm keys (fun k => if key x == k then [x] else [])
      (fun k => xs.filter (fun x => key x == k))
    rw [singleton] at perm
    exact perm.trans (by
      by_cases member : key x ∈ keys <;> simp only [member, ↓reduceIte]
      · simpa [List.filter_cons, member] using (List.Perm.refl [x]).append ih
      · simpa [List.filter_cons, member] using ih)

private def eqRegisters : Typed.Equation ctx ports → List String
  | .reg _ _ name .. => [s!"silicon_reg_{name}"]
  | _ => []

def rawMemories : Core.Stmt → List String
  | .mem _ name .. => [name]
  | _ => []

def eqMemories : Typed.Equation ctx ports → List String
  | .mem _ _ name .. => [name]
  | _ => []

private theorem parts_registers (eq : Typed.Equation ctx ports) :
    (eq.parts.flatMap fun part => rawRegisters part.2.erase) = eqRegisters eq := by
  cases eq <;> simp [Typed.Equation.parts, Typed.Stmt.erase, rawRegisters, eqRegisters,
    List.flatMap_map]

theorem parts_memories (eq : Typed.Equation ctx ports) :
    (eq.parts.flatMap fun part => rawMemories part.2.erase) = eqMemories eq := by
  cases eq <;> simp [Typed.Equation.parts, Typed.Stmt.erase, rawMemories, eqMemories,
    List.flatMap_map]

theorem parts_perm (m : Typed.Module) (f : Core.Stmt → List String) :
    (m.erase.body.flatMap f).Perm
      (m.body.flatMap fun eq => eq.parts.flatMap fun part => f part.2.erase) := by
  have perm := (List.mergeSort_perm (m.body.flatMap Typed.Equation.parts)
    (fun a b => a.1 ≤ b.1)).flatMap_right (fun part => f part.2.erase)
  simpa only [Typed.Module.erase, Typed.equationsErase, List.flatMap_map,
    List.flatMap_assoc] using perm

private theorem register_names_perm (m : Typed.Module) :
    (m.erase.body.flatMap rawRegisters).Perm (m.body.flatMap eqRegisters) := by
  simpa only [parts_registers] using parts_perm m rawRegisters

theorem memory_names_nodup (d : Core.Design) (m : Typed.Module)
    (wf : WellFormed d) (hm : m.erase ∈ Typed.modules d) :
    (m.body.flatMap eqMemories).Nodup := by
  have sub : (m.erase.body.flatMap rawMemories).Sublist
      (m.erase.body.filterMap Stmt.driverName) := by
    generalize m.erase.body = body
    induction body with
    | nil => exact List.Sublist.refl _
    | cons stmt body ih =>
      cases stmt <;> simp only [rawMemories, Stmt.driverName, List.flatMap_cons,
        List.filterMap_cons, List.nil_append, List.singleton_append]
      all_goals first | exact ih.cons _ | exact ih.cons_cons _ | exact ih
  have unique := (Check.module_driver_names_nodup d m.erase wf hm).sublist sub
  have perm : (m.erase.body.flatMap rawMemories).Perm (m.body.flatMap eqMemories) := by
    simpa only [parts_memories] using parts_perm m rawMemories
  exact perm.nodup_iff.mp unique

private def readName (r : Lower.ReadPort) : String := s!"{r.memory}.r{r.index}_data"

private theorem memory_entries_names (m : Typed.Module) (s : Lower.State) :
    ((Lower.memoryEntries m s).map Prod.fst).flatMap Prod.fst =
      ((m.body.flatMap eqMemories).flatMap fun name =>
        (s.reads.filter (·.memory == name)).mergeSort (·.index ≤ ·.index)).map readName := by
  have row (name : String) :
      ((s.reads.filter (·.memory == name)).mergeSort (·.index ≤ ·.index)).map
          (fun r => s!"{name}.r{r.index}_data") =
        ((s.reads.filter (·.memory == name)).mergeSort (·.index ≤ ·.index)).map readName := by
    apply List.map_congr_left
    intro r hr
    have member := (List.mergeSort_perm _ _).mem_iff.mp hr
    have same : r.memory = name := by simpa using (List.mem_filter.mp member).2
    simp only [readName, same]
  unfold Lower.memoryEntries
  generalize m.body = body
  induction body with
  | nil => rfl
  | cons eq body ih =>
    cases eq <;> simp only [List.filterMap_cons, List.map_cons, List.flatMap_cons,
      eqMemories, List.nil_append, List.singleton_append,
      List.map_append] <;> try exact ih
    rw [row]
    exact congrArg (List.append _) ih

private theorem memory_entries_count (m : Typed.Module) (s : Lower.State)
    (unique : (m.body.flatMap eqMemories).Nodup) (name : String) :
    (((Lower.memoryEntries m s).map Prod.fst).flatMap Prod.fst).count name ≤
      (s.reads.map readName).count name := by
  rw [memory_entries_names]
  have sorted := flatMap_perm_congr (m.body.flatMap eqMemories)
    (fun n => (s.reads.filter (·.memory == n)).mergeSort (·.index ≤ ·.index))
    (fun n => s.reads.filter (·.memory == n)) (fun n _ => List.mergeSort_perm _ _)
  have partition := filter_partition (m.body.flatMap eqMemories) unique s.reads
    Lower.ReadPort.memory
  rw [((sorted.trans partition).map readName).count_eq name]
  exact (List.filter_sublist.map readName).count_le name

private theorem register_entries_sublist (m : Typed.Module) (s : Lower.State) :
    ((Lower.registerEntries m s).flatMap Prod.fst).Sublist (m.body.flatMap eqRegisters) := by
  unfold Lower.registerEntries
  generalize m.body = body
  induction body with
  | nil => exact List.Sublist.refl _
  | cons eq body ih =>
    cases eq <;> simp only [List.filterMap_cons, List.flatMap_cons, eqRegisters,
      List.nil_append] <;> try exact ih
    rename_i index p name w clk target reset ni np next
    cases found : s.nexts.lookup name with
    | none => simpa [found] using ih.cons s!"silicon_reg_{name}"
    | some value => simpa [found] using ih.cons_cons s!"silicon_reg_{name}"

private theorem zip_names_sublist (names : List String) (types : List Mlir.Ty) :
    ((names.zip types).map Prod.fst).Sublist names := by
  induction names generalizing types with
  | nil => simp
  | cons name names ih =>
    cases types with
    | nil => simp
    | cons ty types => exact (ih types).cons_cons name

private theorem definitions_names_sublist (m : Mlir.Module) :
    (m.definitions.map Prod.fst).Sublist
      (m.inputPorts.map Mlir.Port.name ++ m.body.flatMap Prod.fst) := by
  simp only [Mlir.Module.definitions, List.map_append, List.map_map, List.map_flatMap,
    Function.comp_def]
  apply List.Sublist.append_left
  induction m.body with
  | nil => exact List.Sublist.refl _
  | cons entry body ih => exact (zip_names_sublist entry.1 entry.2.resultTypes).append ih

private theorem lowered_inputs (ports : List Port) :
    (((ports.map Lower.port).filter (·.dir == .input)).map Mlir.Port.name) = inputNames ports := by
  induction ports with
  | nil => rfl
  | cons port ports ih =>
    cases dir : port.dir <;> simp [Lower.port, inputNames, dir] at ih ⊢ <;> exact ih

private theorem module_names (m : Typed.Module) :
    (Lower.module m).1.inputPorts.map Mlir.Port.name ++
        (Lower.module m).1.body.flatMap Prod.fst =
      inputNames m.ports ++ (Lower.statementState m).body.toList.flatMap Prod.fst ++
        ((Lower.memoryEntries m (Lower.statementState m)).map Prod.fst).flatMap Prod.fst ++
        (Lower.registerEntries m (Lower.statementState m)).flatMap Prod.fst := by
  let s := Lower.statementState m
  let state := { s with body := s.body ++ ((Lower.memoryEntries m s).map Prod.fst).toArray }
  change (((m.ports.map Lower.port).filter (·.dir == .input)).map Mlir.Port.name) ++
    ((state.body.toList ++ Lower.registerEntries m state).map
      (fun entry => (entry.1, Lower.substitute
        (Lower.resolve state.aliases state.aliases.size) entry.2))).flatMap Prod.fst = _
  simp only [lowered_inputs, List.flatMap_map]
  change inputNames m.ports ++
    ((s.body ++ ((Lower.memoryEntries m s).map Prod.fst).toArray).toList ++
      Lower.registerEntries m s).flatMap Prod.fst = _
  simp only [Array.toList_append, List.flatMap_append, List.flatMap_map, List.append_assoc]
  rfl

/-- Each definition in a checked module has a unique name. -/
theorem lower_module_defs_nodup (raw : Core.Design) (t : Typed.Design)
    (h : check raw = .ok t) (m : Typed.Module) (hm : m ∈ t.bodies) :
    ((Lower.module m).1.definitions.map Prod.fst).Nodup := by
  have erase := check_sound_erase raw t h
  have wf := (check_sound raw t h).1
  have member : m.erase ∈ Typed.modules raw := by
    apply List.mem_filterMap.mpr
    exact ⟨.module m.erase, erase ▸ (t.environments m hm).2.2, rfl⟩
  have fresh := checked_statements_fresh raw t h m hm (Lower.registers m)
  change Fresh (MemoryName m.erase) (Lower.statementState m)
    (inputNames m.ports ++ m.erase.body.flatMap rawRegisters) at fresh
  have unique := memory_names_nodup raw m wf member
  apply List.nodup_iff_count.mpr
  intro name
  have bound := List.nodup_iff_count.mp fresh.1 name
  have memBound := memory_entries_count m (Lower.statementState m) unique name
  have regBound := (register_entries_sublist m (Lower.statementState m)).count_le name
  rw [← (register_names_perm m).count_eq name] at regBound
  have defsBound := (definitions_names_sublist (Lower.module m).1).count_le name
  rw [module_names] at defsBound
  simp only [allocatedNames, List.count_append] at bound defsBound
  change (((Lower.memoryEntries m (Lower.statementState m)).map Prod.fst).flatMap Prod.fst).count
      name ≤ ((Lower.statementState m).reads.map
        (fun r => s!"{r.memory}.r{r.index}_data")).count name at memBound
  omega

end Silicon.Core.LowerProof
