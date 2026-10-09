import Silicon.Core.Proof.Lower.InstanceSig

/-!
Instance ops take their names from source instances and memories, which are distinct
source names. Outputs follow the output ports and have the port types.
-/
namespace Silicon.Core.LowerProof

def rawInstances : Core.Stmt → List String
  | .inst _ name .. => [name]
  | _ => []

private theorem stmtInstances_erase (stmt : Typed.Stmt ctx ports) :
    stmtInstances stmt = rawInstances stmt.erase := by
  cases stmt <;> rfl

private theorem memory_names (m : Typed.Module) (s : Lower.State) :
    ((Lower.memoryEntries m s).map Prod.fst).filterMap instName = m.body.flatMap eqMemories := by
  unfold Lower.memoryEntries
  generalize m.body = body
  induction body with
  | nil => rfl
  | cons eq body ih =>
    cases eq <;> simp only [List.filterMap_cons, List.map_cons, List.flatMap_cons, eqMemories,
      List.nil_append] <;> try exact ih
    simp only [instName, List.singleton_append]
    exact congrArg _ ih

private theorem register_names (m : Typed.Module) (s : Lower.State) :
    (Lower.registerEntries m s).filterMap instName = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro x hx
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := registerEntries_mem m s x hx
  rfl

private theorem drivers_sublist (body : List Core.Stmt) :
    (body.flatMap fun s => rawInstances s ++ rawMemories s).Sublist
      (body.filterMap Stmt.driverName) := by
  induction body with
  | nil => exact List.Sublist.refl _
  | cons s body ih =>
    cases s <;> simp only [rawInstances, rawMemories, List.flatMap_cons, List.filterMap_cons,
      Stmt.driverName, List.nil_append, List.append_nil, List.singleton_append]
    all_goals first | exact ih.cons_cons _ | exact ih.cons _ | exact ih

theorem instance_names (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) :
    ((rawBody m).filterMap instName).Nodup := by
  obtain ⟨⟨tail, body, insts, _⟩, _⟩ :=
    statements_step (Lower.registers m) (Lower.statements m) {}
  rw [← run_state] at body
  have tailEq : tail = (Lower.statementState m).body.toList := by simpa using body.symm
  unfold rawBody
  rw [List.filterMap_append, List.filterMap_append, ← tailEq, insts, memory_names,
    register_names, List.append_nil]
  have source : (Lower.statements m).flatMap stmtInstances = m.erase.body.flatMap rawInstances := by
    rw [← statements_erase m, List.flatMap_map]
    congr 1
    funext stmt
    exact stmtInstances_erase stmt
  rw [source]
  have memories : (m.body.flatMap eqMemories).Perm (m.erase.body.flatMap rawMemories) := by
    simpa only [parts_memories] using (parts_perm m rawMemories).symm
  have unique := Check.module_driver_names_nodup raw m.erase (module_wf raw t h)
    (checked_erase_member raw t h m hm)
  apply (((List.Perm.refl _).append memories).trans
    (flatMap_split_perm _ _ _).symm).nodup_iff.mpr
  exact unique.sublist (drivers_sublist _)

theorem outputs_length (ports : List Port) (f : String → String) :
    (ports.filterMap fun p => if p.dir == .output then some (f p.name) else none).length =
      ((ports.map Lower.port).filter (·.dir == .output)).length := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    cases dir : p.dir <;> simp [Lower.port, dir] <;> simpa using ih

theorem outputs_zip (ports : List Port) (f : String → String) :
    ∀ pair ∈ (ports.filterMap fun p => if p.dir == .output then some (f p.name) else none).zip
      ((ports.map Lower.port).filter (·.dir == .output)),
      ∃ p ∈ ports, p.dir = .output ∧ pair = (f p.name, Lower.port p) := by
  induction ports with
  | nil => intro pair hp; cases hp
  | cons p ports ih =>
    intro pair hp
    cases dir : p.dir with
    | input =>
      simp only [List.filterMap_cons, List.map_cons, List.filter_cons, dir] at hp
      simp [Lower.port, dir] at hp
      obtain ⟨q, hq, out, rfl⟩ := ih pair (by simpa using hp)
      exact ⟨q, List.mem_cons_of_mem _ hq, out, rfl⟩
    | output =>
      simp only [List.filterMap_cons, List.map_cons, List.filter_cons, dir] at hp
      simp only [Lower.port, dir, beq_self_eq_true, ↓reduceIte, List.zip_cons_cons,
        List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨p, List.mem_cons_self .., dir, by simp [Lower.port, dir]⟩
      · obtain ⟨q, hq, out, rfl⟩ := ih pair hp
        exact ⟨q, List.mem_cons_of_mem _ hq, out, rfl⟩

end Silicon.Core.LowerProof
