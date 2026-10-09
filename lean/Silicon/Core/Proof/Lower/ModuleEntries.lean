import Silicon.Core.Proof.Lower.ModuleTyping

/-!
Memory instances and registers use typed ports and typed state updates.
-/
namespace Silicon.Core.LowerProof

def memReads (s : Lower.State) (memory : String) : List Lower.ReadPort :=
  (s.reads.filter (·.memory == memory)).mergeSort (·.index ≤ ·.index)

def memWrites (s : Lower.State) (memory : String) : List Lower.WritePort :=
  (s.writes.filter (·.memory == memory)).mergeSort (·.index ≤ ·.index)

def memConfig (s : Lower.State) (memory : String) (w depth : Nat) : MemConfig :=
  ⟨depth, w, (memReads s memory).length, (memWrites s memory).length⟩

def memArgs (s : Lower.State) (memory : String) (w depth : Nat) (clk : String) :
    List (String × String × Mlir.Ty) :=
  [("clk", clk, Mlir.Ty.clock)] ++
    (memReads s memory).map (fun r => (s!"r{r.index}_addr", r.addr,
      Mlir.Ty.int (Typed.addressWidth depth))) ++
    (memWrites s memory).flatMap (fun wr =>
      [(s!"w{wr.index}_addr", wr.addr, Mlir.Ty.int (Typed.addressWidth depth)),
       (s!"w{wr.index}_data", wr.data, .int w), (s!"w{wr.index}_en", wr.enable, .int 1)])

def memResults (s : Lower.State) (memory : String) (w : Nat) : List (String × Mlir.Ty) :=
  (memReads s memory).map fun r => (s!"r{r.index}_data", Mlir.Ty.int w)

def memEntry (s : Lower.State) (memory : String) (w depth : Nat) (clk : String) :
    (List String × Mlir.Op) × MemConfig :=
  (((memReads s memory).map fun r => s!"{memory}.r{r.index}_data",
    .instance memory (memConfig s memory w depth).moduleName (memArgs s memory w depth clk)
      (memResults s memory w)), memConfig s memory w depth)

theorem memoryEntries_mem (m : Typed.Module) (s : Lower.State)
    (x : (List String × Mlir.Op) × MemConfig) (hx : x ∈ Lower.memoryEntries m s) :
    ∃ i p memory w depth clk target ws, Typed.Equation.mem i p memory w depth clk target ws ∈
      m.body ∧ x = memEntry s memory w depth clk := by
  obtain ⟨eq, he, found⟩ := List.mem_filterMap.mp hx
  cases eq <;> simp only [reduceCtorEq] at found
  case mem i p memory w depth clk target ws =>
    exact ⟨i, p, memory, w, depth, clk, target, ws, he, (Option.some.inj found).symm⟩

theorem registerEntries_mem (m : Typed.Module) (s : Lower.State)
    (x : List String × Mlir.Op) (hx : x ∈ Lower.registerEntries m s) :
    ∃ i p n w clk target reset ni np next nextName,
      Typed.Equation.reg i p n w clk target reset ni np next ∈ m.body ∧
      s.nexts.lookup n = some nextName ∧
      x = ([s!"silicon_reg_{n}"],
        .compreg nextName clk ((s.resets.lookup n).getD none) (.int w)) := by
  obtain ⟨eq, he, found⟩ := List.mem_filterMap.mp hx
  cases eq <;> simp only [reduceCtorEq] at found
  case reg i p n w clk target reset ni np next =>
    cases hn : s.nexts.lookup n with
    | none => simp [hn] at found
    | some nextName =>
      simp only [hn] at found
      have found : some ([s!"silicon_reg_{n}"], Mlir.Op.compreg nextName clk
          ((s.resets.lookup n).getD none) (.int w)) = some x := found
      exact ⟨i, p, n, w, clk, target, reset, ni, np, next, nextName, he, hn,
        (Option.some.inj found).symm⟩

theorem mem_of_lookup {l : List (String × β)} {k : String} {v : β} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons head tail ih =>
    obtain ⟨k', v'⟩ := head
    by_cases same : k = k'
    · subst same
      simp [List.lookup] at h
      subst h
      exact List.mem_cons_self ..
    · simp [List.lookup, show (k == k') = false from beq_eq_false_iff_ne.mpr same] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem port_in_context (m : Typed.Module) (p : Port) (hp : p ∈ m.ports) :
    (.name p.name, portKind p) ∈ m.ctx := by
  rw [m.context_eq]
  unfold Typed.contextFromPorts
  exact List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

theorem clock_has (c : String) (hc : Rules.clockName m.erase c = true) : Has m c .clock := by
  unfold Rules.clockName at hc
  obtain ⟨port, found, ok⟩ := (Option.any_eq_true _ _).mp hc
  have member := List.mem_of_find?_eq_some found
  have named : port.name = c := by simpa using List.find?_some found
  have ok : port.dir = .input ∧ port.ty = .clock := by simpa using ok
  apply clocks_has raw t h m hm
  apply lookup_name raw t h m hm
  have entry := port_in_context m port member
  rw [named] at entry
  simpa [portKind, ok.1, ok.2] using entry

theorem resolved_target (stmt : Core.Stmt) (hs : stmt ∈ m.erase.body) :
    Rules.ResolvedTarget raw m.erase stmt :=
  ((module_wf raw t h).2.1.2 m.erase (checked_erase_member raw t h m hm) stmt hs).1

omit h hm in
theorem typed_erase_member (stmt : Typed.Stmt m.ctx m.interfaces)
    (eq : Typed.Equation m.ctx m.interfaces) (he : eq ∈ m.body) (part : Nat × _)
    (hp : part ∈ eq.parts) (same : part.2 = stmt) : stmt.erase ∈ m.erase.body :=
  stmt_erase_member m stmt ((statement_of_eq m stmt).mpr ⟨eq, he, part, hp, same⟩)

theorem memory_good (x : (List String × Mlir.Op) × MemConfig)
    (hx : x ∈ Lower.memoryEntries m (Lower.statementState m)) :
    (moduleTyping raw t h m hm).Good x.1 := by
  obtain ⟨i, p, memory, w, depth, clk, target, ws, he, rfl⟩ := memoryEntries_mem m _ x hx
  have good := final_good raw t h m hm
  have clock : Has m clk .clock := by
    have member := typed_erase_member m (Typed.Stmt.mem p memory w depth clk) _ he
      (i, Typed.Stmt.mem p memory w depth clk) (by simp [Typed.Equation.parts]) rfl
    exact clock_has raw t h m hm clk (resolved_target raw t h m hm _ member)
  refine ⟨by simp [memEntry, memResults, Mlir.Op.resultTypes], trivial, ?_⟩
  intro o ho
  obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp ho
  simp only [memArgs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_flatMap] at harg
  rcases harg with (rfl | ⟨r, hr, rfl⟩) | ⟨wr, hw, harg⟩
  · exact clock
  · have hr' := (List.mergeSort_perm _ _).mem_iff.mp hr
    obtain ⟨hr', same⟩ := List.mem_filter.mp hr'
    rcases good.2.1 r hr' with absent | ⟨w', depth', found, typed⟩
    · cases absent
    · have same : r.memory = memory := by simpa using same
      rw [same, target] at found
      cases found
      exact typed
  · have hw' := (List.mergeSort_perm _ _).mem_iff.mp hw
    obtain ⟨hw', same⟩ := List.mem_filter.mp hw'
    rcases good.2.2.1 wr hw' with absent | ⟨w', depth', found, ta, td, te⟩
    · cases absent
    · have same : wr.memory = memory := by simpa using same
      rw [same, target] at found
      cases found
      rcases harg with rfl | rfl | rfl
      · exact ta
      · exact td
      · exact te

theorem register_good (x : List String × Mlir.Op)
    (hx : x ∈ Lower.registerEntries m (Lower.statementState m)) :
    (moduleTyping raw t h m hm).Good x := by
  obtain ⟨i, p, n, w, clk, target, reset, ni, np, next, nextName, he, hn, rfl⟩ :=
    registerEntries_mem m _ x hx
  have good := final_good raw t h m hm
  have clock : Has m clk .clock := by
    have member := typed_erase_member m (Typed.Stmt.reg p n w clk reset) _ he
      (i, Typed.Stmt.reg p n w clk reset) (by simp [Typed.Equation.parts]) rfl
    exact clock_has raw t h m hm clk (resolved_target raw t h m hm _ member)
  have width := valueTy_lookup _ _ _ target
  refine ⟨rfl, trivial, ?_⟩
  intro o ho
  simp only [Mlir.Op.operands, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  rcases ho with (rfl | rfl) | ho
  · rcases good.2.2.2.1 _ (mem_of_lookup hn) with absent | ⟨w', found, typed⟩
    · cases absent
    · have same := found.symm.trans target
      cases same
      exact typed
  · exact clock
  · cases hr : (Lower.statementState m).resets.lookup n with
    | none => simp [hr] at ho
    | some opt =>
      cases opt with
      | none => simp [hr] at ho
      | some pair =>
        rw [hr] at ho
        rcases good.2.2.2.2 _ (mem_of_lookup hr) with absent | ⟨w', found, typed⟩
        · cases absent
        · rw [width] at found
          cases found
          have typed := typed pair (List.mem_singleton_self _)
          simp only [Option.getD_some, Option.toList_some, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
            or_false] at ho
          rcases ho with rfl | rfl
          · exact typed.1
          · exact typed.2

end

end Silicon.Core.LowerProof
