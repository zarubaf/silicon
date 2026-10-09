import Silicon.Core.Proof.Lower.ModuleEntries

/-!
Each memory instance numbers its read and write ports from zero without gaps, as the
memory model ports do.
-/
namespace Silicon.Core.LowerProof

private theorem length_le_of_bounded (n : Nat) :
    ∀ l : List Nat, l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n := by
  induction n with
  | zero =>
    intro l _ bound
    cases l with
    | nil => exact Nat.le_refl _
    | cons x xs => exact absurd (bound x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro l unique bound
    by_cases member : n ∈ l
    · have erased := ih (l.erase n) (unique.erase n) (fun x hx => by
        have ne : x ≠ n := fun eq => by
          subst eq
          exact (List.Nodup.mem_erase_iff unique).mp hx |>.1 rfl
        have := bound x (List.mem_of_mem_erase hx)
        omega)
      rw [List.length_erase_of_mem member] at erased
      have := List.length_pos_of_mem member
      omega
    · have := ih l unique (fun x hx => by
        have ne : x ≠ n := fun eq => member (eq ▸ hx)
        have := bound x hx
        omega)
      omega

theorem perm_range_of_bounded (n : Nat) :
    ∀ l : List Nat, l.Nodup → (∀ x ∈ l, x < n) → l.length = n → l.Perm (List.range n) := by
  induction n with
  | zero =>
    intro l _ _ length
    rw [List.length_eq_zero_iff.mp length]
    exact List.Perm.refl _
  | succ n ih =>
    intro l unique bound length
    have member : n ∈ l := by
      apply Classical.byContradiction
      intro absent
      have := length_le_of_bounded n l unique (fun x hx => by
        have ne : x ≠ n := fun eq => absent (eq ▸ hx)
        have := bound x hx
        omega)
      omega
    have rest := ih (l.erase n) (unique.erase n) (fun x hx => by
        have ne : x ≠ n := fun eq => by
          subst eq
          exact (List.Nodup.mem_erase_iff unique).mp hx |>.1 rfl
        have := bound x (List.mem_of_mem_erase hx)
        omega) (by rw [List.length_erase_of_mem member]; omega)
    rw [List.range_succ]
    exact (List.perm_cons_erase member).trans
      ((rest.cons n).trans (List.perm_append_comm (l₁ := [n])))

theorem sorted_range {α : Type} (l : List α) (key : α → Nat)
    (sorted : l.Pairwise fun a b => key a ≤ key b) (perm : (l.map key).Perm (List.range l.length)) :
    l.map key = List.range l.length := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
    (List.pairwise_map.mpr sorted) List.pairwise_le_range perm

theorem mergeSort_sorted {α : Type} (l : List α) (key : α → Nat) :
    (l.mergeSort (fun a b => key a ≤ key b)).Pairwise fun a b => key a ≤ key b := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
    (fun a b c hab hbc => by simp at hab hbc ⊢; omega)
    (fun a b => by simp; omega) l
  exact h.imp (fun hab => by simpa using hab)

theorem reads_indices (m : Typed.Module) (memory : String) :
    (memReads (Lower.statementState m) memory).map (·.index) =
      List.range (memReads (Lower.statementState m) memory).length := by
  obtain ⟨_, ⟨new, hreads, counts⟩, _⟩ :=
    statements_step (Lower.registers m) (Lower.statements m) {}
  obtain ⟨_, perm⟩ := counts memory
  rw [← run_state] at hreads perm
  have zero : readCount {} memory = 0 := rfl
  rw [zero, Nat.sub_zero, ← List.range_eq_range'] at perm
  have filtered : indicesOf (Lower.statementState m).reads memory = indicesOf new memory := by
    rw [hreads]
    simp [indicesOf]
  rw [← filtered] at perm
  have sortedPerm : ((memReads (Lower.statementState m) memory).map (·.index)).Perm
      (List.range (readCount (Lower.statementState m) memory)) :=
    ((List.mergeSort_perm _ _).map _).trans perm
  have length : (memReads (Lower.statementState m) memory).length =
      readCount (Lower.statementState m) memory := by
    simpa using sortedPerm.length_eq
  exact sorted_range _ _ (mergeSort_sorted _ _) (by rw [length]; exact sortedPerm)

def rawWrites : Core.Stmt → List (String × Nat)
  | .write _ name index .. => [(name, index)]
  | _ => []

private theorem stmtWrites_erase (stmt : Typed.Stmt ctx ports) :
    stmtWrites stmt = rawWrites stmt.erase := by
  cases stmt <;> rfl

private theorem raw_write_indices (body : List Core.Stmt) (memory : String) :
    ((body.flatMap rawWrites).filter (·.1 == memory)).map (·.2) =
      (Rules.writes ⟨⟨0, 0, []⟩, "", [], body⟩ memory).map (·.1) := by
  induction body with
  | nil => rfl
  | cons s body ih =>
    cases s <;> simp only [rawWrites, List.flatMap_cons, List.nil_append] <;>
      simp only [Rules.writes, List.filterMap_cons] at ih ⊢ <;> try exact ih
    case write p n index a v e =>
      by_cases same : n = memory
      · subst same
        simp [ih]
      · simp [same, ih]

theorem writes_indices (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (memory : String) (p : Pos) (w depth : Nat)
    (clk : String) (hs : Core.Stmt.mem p memory w depth clk ∈ m.erase.body) :
    (memWrites (Lower.statementState m) memory).map (·.index) =
      List.range (memWrites (Lower.statementState m) memory).length := by
  obtain ⟨_, _, new, hwrites, keys⟩ :=
    statements_step (Lower.registers m) (Lower.statements m) {}
  rw [← run_state] at hwrites
  have rule := (module_wf raw t h).2.2.2.2.2.2.2.2.2.2.1 m.erase
    (checked_erase_member raw t h m hm) _ hs
  simp only at rule
  let indices := (Rules.writes m.erase memory).map (·.1)
  have source : ((Lower.statements m).flatMap stmtWrites |>.filter (·.1 == memory)).map (·.2) =
      indices := by
    have same : (Lower.statements m).flatMap stmtWrites = m.erase.body.flatMap rawWrites := by
      rw [← statements_erase m, List.flatMap_map]
      congr 1
      funext stmt
      exact stmtWrites_erase stmt
    rw [same]
    exact raw_write_indices m.erase.body memory
  have filtered : ((Lower.statementState m).writes.filter (·.memory == memory)).map (·.index) =
      ((new.map fun w => (w.memory, w.index)).filter (·.1 == memory)).map (·.2) := by
    rw [hwrites]
    simp [List.filter_map, Function.comp_def]
  have perm : ((memWrites (Lower.statementState m) memory).map (·.index)).Perm indices := by
    refine ((List.mergeSort_perm _ _).map _).trans ?_
    rw [filtered, ← source]
    exact (keys.filter _).map _
  have range := perm_range_of_bounded indices.length indices rule.1
    (fun x hx => by simpa [indices] using rule.2 x hx) rfl
  have length : (memWrites (Lower.statementState m) memory).length = indices.length := by
    simpa using perm.length_eq
  exact sorted_range _ _ (mergeSort_sorted _ _) (by rw [length]; exact perm.trans range)

/-- The instance clause of `Mlir.Module.WellFormed` for a callee with these ports. -/
def SigOk (ports : List Mlir.Port) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty)) : Prop :=
  args.map (fun (pin, _, ty) => (pin, ty)) =
    ((ports.filter (·.dir == .input)).map fun p => (p.name, p.ty)) ∧
  results = ((ports.filter (·.dir == .output)).map fun p => (p.name, p.ty))

private theorem map_index {α β : Type} (l : List α) (index : α → Nat) (f : Nat → β) :
    l.map (fun x => f (index x)) = (l.map index).map f := by
  rw [List.map_map]
  rfl

private theorem flatMap_index {α β : Type} (l : List α) (index : α → Nat) (f : Nat → List β) :
    l.flatMap (fun x => f (index x)) = (l.map index).flatMap f := by
  rw [List.flatMap_map]

private theorem flatMap_single {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

private theorem flatMap_empty {α β : Type} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l <;> simp_all

theorem memory_sig (s : Lower.State) (memory : String) (w depth : Nat) (clk : String)
    (reads : (memReads s memory).map (·.index) = List.range (memReads s memory).length)
    (writes : (memWrites s memory).map (·.index) = List.range (memWrites s memory).length) :
    SigOk (memConfig s memory w depth).ports (memArgs s memory w depth clk)
      (memResults s memory w) := by
  have readNames (f : Nat → String × Mlir.Ty) :
      (memReads s memory).map (fun r => f r.index) =
        (List.range (memReads s memory).length).map f := by
    rw [← reads, List.map_map]
    rfl
  have writeNames (f : Nat → List (String × Mlir.Ty)) :
      (memWrites s memory).flatMap (fun r => f r.index) =
        (List.range (memWrites s memory).length).flatMap f := by
    rw [← writes, List.flatMap_map]
  constructor
  · simp only [memArgs, memConfig, MemConfig.ports, List.map_append, List.filter_append,
      List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, List.map_map,
      List.map_flatMap, List.filter_flatMap, Function.comp_def]
    simp only [show ∀ x : Mlir.Dir, (x == Mlir.Dir.input) = decide (x = .input) from fun _ => rfl]
    simp only [decide_true, decide_false, ↓reduceIte, reduceCtorEq]
    rw [readNames (fun n => (s!"r{n}_addr", Mlir.Ty.int (Typed.addressWidth depth))),
      writeNames (fun n => [(s!"w{n}_addr", Mlir.Ty.int (Typed.addressWidth depth)),
        (s!"w{n}_data", Mlir.Ty.int w), (s!"w{n}_en", Mlir.Ty.int 1)])]
    simp [flatMap_single]
  · simp only [memResults, memConfig, MemConfig.ports, List.filter_append,
      List.map_append, List.filter_cons, List.filter_nil, List.filter_flatMap]
    simp only [show ∀ x : Mlir.Dir, (x == Mlir.Dir.output) = decide (x = .output) from fun _ => rfl]
    simp only [decide_true, decide_false, ↓reduceIte, reduceCtorEq]
    rw [readNames (fun n => (s!"r{n}_data", Mlir.Ty.int w))]
    simp [flatMap_single, flatMap_empty]

end Silicon.Core.LowerProof
