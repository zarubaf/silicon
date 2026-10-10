import Silicon.Core.Proof.Lower.ModuleOps

/-!
An MLIR solution of a lowered module, read through the final renaming, satisfies every plain
op and every memory read of the statement state.
-/
namespace Silicon.Core.LowerProof

open Semantics

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)

include h hm in
theorem read_ops {d : Mlir.Design} {state inputs V : Mlir.Env} {children : String → Mlir.Env}
    (hv : Mlir.LocalSolution d (Lower.module m).1 state inputs V children) :
    ∀ names op, (names, op) ∈ (finalState m).body.toList → isInstance op = false →
      isCompreg op = false →
      ∃ name v, names = [name] ∧ (V ∘ rename m) name = some v ∧
        op.eval (V ∘ rename m) = some v := by
  intro names op he plain stateless
  have member : (names, Lower.substitute (rename m) op) ∈ (Lower.module m).1.body := by
    rw [module_body]
    exact List.mem_map.mpr ⟨(names, op), List.mem_append_left _ (List.mem_append_left _ he), rfl⟩
  have equation := hv.2.1 _ member
  obtain ⟨n, hn, fixed⟩ := result_renamed raw t h m hm (names, op) he plain
  have eval := substitute_eval (rename m) op V
  cases op
  case «instance» => cases plain
  case compreg => cases stateless
  all_goals
    obtain ⟨name, v, same, hop, hval⟩ := equation
    refine ⟨name, v, same, ?_, eval.symm.trans hop⟩
    have : name = n := List.singleton_inj.mp (same.symm.trans hn)
    subst this
    simpa [Function.comp_def, fixed] using hval

include h noExterns hm in
theorem memory_solution (σ : Mlir.ModuleState) (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (i : Nat) (p : Pos) (memory : String) (w depth : Nat) (clk : String)
    (target) (ws) (he : Typed.Equation.mem i p memory w depth clk target ws ∈ m.body) :
    Mlir.LocalSolution ((lower t).withModels (memoryConfigs t)) (memModel (memConfig (finalState m)
      memory w depth))
      (σ.cells [memory])
      (Mlir.instanceInputs ((memArgs (finalState m) memory w depth clk).map
        (renameArg (rename m))) (all [])) (all [memory]) (fun n => all [memory, n]) ∧
    ∀ k < (memReads (finalState m) memory).length,
      all [] s!"{memory}.r{k}_data" = all [memory] s!"r{k}_data" := by
  have entry := memory_entry_body m i p memory w depth clk target ws he
  have hc := memory_config t m hm i p memory w depth clk target ws he
  obtain ⟨child, found, _, _, _, outputs⟩ := hv.1.2.1 _ entry
  have same := memory_child raw t h noExterns _ hc child found
  subst same
  have fi := findInstance_mem _ (module_instNames raw t h noExterns m hm _ rfl) _ _ _ _ _ entry
  obtain ⟨child', found', solved⟩ := hv.2 [] _ rfl memory _ _ fi
  rw [found] at found'
  cases found'
  refine ⟨solved, fun k hk => ?_⟩
  obtain ⟨v, hv₁, ⟨source, hs, hv₂⟩, _⟩ := outputs ⟨k, by simpa using hk⟩
  obtain ⟨n₁, n₂⟩ := memory_outputs m memory w depth k hk
  have hv₁' : all [] s!"{memory}.r{k}_data" = some v := by
    rw [← n₁]
    exact hv₁
  rw [n₂] at hs
  cases hs
  exact hv₁'.trans hv₂.symm

theorem read_port_input (c : MemConfig) (k : Nat) (hk : k < c.reads) :
    (⟨.input, s!"r{k}_addr", .int (Typed.addressWidth c.depth)⟩ : Mlir.Port) ∈
      (memModel c).inputPorts := by
  simp only [Mlir.Module.inputPorts, memModel, MemConfig.ports, List.mem_filter,
    List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil]
  exact ⟨Or.inl (Or.inr ⟨k, hk, Or.inl rfl⟩), rfl⟩

theorem typed_value {env : Mlir.Env} {name : String} {ty : Mlir.Ty} {v : Mlir.Value}
    (h : env.typed name ty = some v) : env name = some v ∧ v.ty = ty := by
  simp only [Mlir.Env.typed, bind, Option.bind_eq_some_iff] at h
  obtain ⟨v', hv', h⟩ := h
  split at h
  · cases h
    exact ⟨hv', by assumption⟩
  · cases h

theorem bits_of_ty {v : Mlir.Value} {w : Nat} (h : v.ty = .int w) : ∃ x, v = .bits w x := by
  cases v with
  | bits w' x =>
    cases h
    exact ⟨x, rfl⟩
  | array => cases h
  | clock => cases h

include h noExterns hm in
theorem read_reads (σ : Mlir.ModuleState) (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (words : ModelMemories m.ctx)
    (state : ∀ name w depth found, (σ.instance name).regs "reg$$mem" =
      some (.array _ _ (words name w depth found))) :
    ∀ r ∈ (finalState m).reads, ReadEquation words (all [] ∘ rename m) r := by
  intro r hr
  rcases (final_good raw t h m hm).2.1 r hr with absent | ⟨w, depth, found, _⟩
  · cases absent
  obtain ⟨i, p, clk, target, ws, he⟩ := Ownership.memory_equation m r.memory w depth found
  obtain ⟨k, hk, hr'⟩ := memReads_member m r hr
  have index : r.index = k := by
    rw [← hr']
    exact memReads_index m r.memory k hk
  obtain ⟨solved, outs⟩ := memory_solution raw t h noExterns m hm σ inputs all hv i p r.memory w
    depth clk target ws he
  let c := memConfig (finalState m) r.memory w depth
  let args := (memArgs (finalState m) r.memory w depth clk).map (renameArg (rename m))
  have hp := read_port_input c k hk
  obtain ⟨v, hi, ht, _⟩ := solved.1 _ hp
  have arg : (s!"r{k}_addr", r.addr, Mlir.Ty.int (Typed.addressWidth depth)) ∈
      memArgs (finalState m) r.memory w depth clk := by
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨r, ?_, by rw [index]⟩
    have := List.getElem_mem hk
    rwa [hr'] at this
  have find := memArgs_find raw t h m hm i p r.memory w depth clk target ws he (rename m) _ arg
  have inputAt := instanceInputs_find args (all []) (renameArg (rename m)
    (s!"r{k}_addr", r.addr, Mlir.Ty.int (Typed.addressWidth depth))) find
  simp only [renameArg] at inputAt
  rw [inputAt] at hi
  obtain ⟨addr, ht'⟩ := typed_value hi
  obtain ⟨x, rfl⟩ := bits_of_ty ht'
  have local' := localSolution_inputs (MemModelProof.ofEnv_agrees c _ (fun q hq => by
    obtain ⟨v, hv, ty, _⟩ := solved.1 q hq
    exact ⟨v, hv, ty⟩)) solved
  have read := MemModelProof.reads_value c (words r.memory w depth found) _ local'
    (state r.memory w depth found) k hk
  have addrValue : (MemModelProof.Inputs.ofEnv c (Mlir.instanceInputs args (all []))).readAddr k =
      x := by
    simp only [MemModelProof.Inputs.ofEnv, Mlir.Env.bits]
    change ((Mlir.instanceInputs args (all []) (renameArg (rename m)
      (s!"r{k}_addr", r.addr, Mlir.Ty.int (Typed.addressWidth depth))).1 >>= _).getD 0) = x
    rw [instanceInputs_find args (all []) (renameArg (rename m)
      (s!"r{k}_addr", r.addr, Mlir.Ty.int (Typed.addressWidth depth))) find]
    simp only [renameArg, Mlir.Env.typed, addr]
    show ((if (Mlir.Value.bits (Typed.addressWidth depth) x).ty =
      Mlir.Ty.int (Typed.addressWidth depth) then some (Mlir.Value.bits _ x) else none).bind
      (Mlir.Value.asBits (Typed.addressWidth depth))).getD 0 = x
    simp [Mlir.Value.ty, Mlir.Value.asBits]
  rw [addrValue] at read
  refine ⟨w, depth, found, x, addr, ?_⟩
  have reserved := rename_invalid raw t h m hm _ (readName_invalid r)
  change all [] (rename m (readName r)) = _
  rw [reserved]
  change all [] s!"{r.memory}.r{r.index}_data" = _
  rw [index, outs k hk]
  exact read

end

end Silicon.Core.LowerProof
