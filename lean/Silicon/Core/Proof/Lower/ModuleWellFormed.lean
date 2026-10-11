-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleNames

/-!
A lowered checked module is well formed in any design that gives its children and memory
models their lowered ports.
-/
namespace Silicon.Core.LowerProof

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

theorem output_assign (p : Port) (hp : p ∈ m.ports) (dir : p.dir = .output) :
    ∃ stmt ∈ Lower.statements m, LetName stmt = some p.name := by
  have once := (module_wf raw t h).2.2.2.2.2.1 m.erase (checked_erase_member raw t h m hm)
    p hp dir
  obtain ⟨pos, assigned⟩ :=
    List.exists_mem_of_length_pos (l := Rules.assignments m.erase p.name) (by omega)
  obtain ⟨s, hs, hsome⟩ := List.mem_filterMap.mp assigned
  cases s <;> simp only [reduceCtorEq] at hsome
  case assign p' n e =>
    split at hsome
    next same =>
      have same : n = p.name := by simpa using same
      subst same
      obtain ⟨typed, ht, erased⟩ := typed_of_raw m _ hs
      cases typed <;> simp only [Typed.Stmt.erase, reduceCtorEq] at erased
      case assign p'' n'' w'' target'' e'' =>
        obtain ⟨_, rfl, _⟩ := Core.Stmt.assign.inj erased
        exact ⟨_, ht, rfl⟩
    next => cases hsome

theorem output_has (p : Port) (hp : p ∈ m.ports) (dir : p.dir = .output) :
    Has m p.name (Lower.type p.ty) := by
  have clocks := ((module_wf raw t h).2.2.2.2.2.2.2.1 (.module m.erase)
    (module_item raw t h m hm)).2.1 p hp dir
  cases ty : p.ty with
  | clock => exact absurd ty clocks
  | bits w =>
    obtain ⟨stmt, hs, named⟩ := output_assign raw t h m hm p hp dir
    have typed := let_has_aux raw t h m hm _ stmt hs p.name named (Nat.lt_succ_self _)
    have entry := lookup_name raw t h m hm _ _ (port_in_context m p hp)
    have width := (letName_lookup raw t h m hm stmt hs p.name named).symm.trans entry
    simp only [portKind, ty, dir] at width
    have width : stmtWidth stmt = w := by
      simpa using width
    rw [← width]
    exact typed

theorem good_entry (e : List String × Mlir.Op) (good : (moduleTyping raw t h m hm).Good e) :
    e.1.length = (Lower.substitute (rename m) e.2).resultTypes.length ∧
      (Lower.substitute (rename m) e.2).Valid ∧
      ∀ operand ∈ (Lower.substitute (rename m) e.2).operands,
        (Lower.module m).1.definitions.lookup operand.1 = some operand.2 := by
  obtain ⟨length, valid, operands⟩ := good
  refine ⟨by rw [substitute_resultTypes]; exact length, (substitute_valid _ _).mpr valid, ?_⟩
  intro o ho
  rw [substitute_operands] at ho
  obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
  exact operands o' ho'

theorem raw_good (e : List String × Mlir.Op) (he : e ∈ rawBody m) :
    (moduleTyping raw t h m hm).Good e := by
  unfold rawBody at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · rcases (final_good raw t h m hm).1 e he with absent | good
      · cases absent
      · exact good
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      exact memory_good raw t h m hm x hx
  · exact register_good raw t h m hm e he

def InstClause (d : Mlir.Design) : Mlir.Op → Prop
  | .instance _ callee args results => ∃ ports, d.signature callee = some ports ∧
      SigOk ports args results
  | _ => True

omit h hm in
theorem instClause_substitute (d : Mlir.Design) (f : String → String) (op : Mlir.Op)
    (clause : InstClause d op) : InstClause d (Lower.substitute f op) := by
  cases op with
  | «instance» inst callee args results =>
    obtain ⟨ports, sig, pins, outs⟩ := clause
    refine ⟨ports, sig, ?_, outs⟩
    simp only [List.map_map, Function.comp_def] at pins ⊢
    exact pins
  | _ => trivial

theorem raw_clause (d : Mlir.Design)
    (sources : ∀ p i child inputs, Typed.Stmt.inst p i child inputs ∈ Lower.statements m →
      d.signature child = some ((m.interfaces child).map Lower.port))
    (memories : ∀ i p memory w depth clk target ws,
      Typed.Equation.mem i p memory w depth clk target ws ∈ m.body →
      d.signature (memConfig (Lower.statementState m) memory w depth).moduleName =
        some (memConfig (Lower.statementState m) memory w depth).ports)
    (e : List String × Mlir.Op) (he : e ∈ rawBody m) : InstClause d e.2 := by
  unfold rawBody at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨⟨tail, body, _, shapes⟩, _⟩ :=
        statements_step (Lower.registers m) (Lower.statements m) {}
      rw [← run_state] at body
      have tailEq : tail = (Lower.statementState m).body.toList := by simpa using body.symm
      rw [← tailEq] at he
      cases hi : isInstance e.2 with
      | false =>
        obtain ⟨names, op⟩ := e
        cases op <;> simp_all [isInstance, InstClause]
      | true =>
        obtain ⟨stmt, hs, shape⟩ := shapes e he hi
        cases stmt <;> simp only [InstShape] at shape
        case inst p i child inputs =>
          obtain ⟨args, pins, rfl⟩ := shape
          exact ⟨_, sources p i child inputs hs, instance_sig raw t h m hm p i child inputs hs
            args pins⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      obtain ⟨i, p, memory, w, depth, clk, target, ws, hmem, rfl⟩ := memoryEntries_mem m _ x hx
      have member := typed_erase_member m (Typed.Stmt.mem p memory w depth clk) _ hmem
        (i, Typed.Stmt.mem p memory w depth clk) (by simp [Typed.Equation.parts]) rfl
      exact ⟨_, memories i p memory w depth clk target ws hmem,
        memory_sig _ memory w depth clk (reads_indices m memory)
          (writes_indices raw t h m hm memory p w depth clk member)⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := registerEntries_mem m _ e he
    trivial

theorem lower_module_wellFormed (d : Mlir.Design)
    (sources : ∀ p i child inputs, Typed.Stmt.inst p i child inputs ∈ Lower.statements m →
      d.signature child = some ((m.interfaces child).map Lower.port))
    (memories : ∀ i p memory w depth clk target ws,
      Typed.Equation.mem i p memory w depth clk target ws ∈ m.body →
      d.signature (memConfig (Lower.statementState m) memory w depth).moduleName =
        some (memConfig (Lower.statementState m) memory w depth).ports) :
    (Lower.module m).1.WellFormed d := by
  refine ⟨?_, lower_module_defs_nodup raw t h m hm, ?_, ?_, ?_, ?_⟩
  · rw [module_ports, List.map_map]
    have same : Mlir.Port.name ∘ Lower.port = Port.name := by
      funext p
      rfl
    rw [same]
    exact Check.module_ports_nodup raw m.erase (module_wf raw t h)
      (checked_erase_member raw t h m hm)
  · rw [module_body, List.filterMap_map, filterMap_pointwise (g := instName) (fun x _ => by
      obtain ⟨names, op⟩ := x
      cases op <;> rfl)]
    exact instance_names raw t h m hm
  · intro entry he
    rw [module_body] at he
    obtain ⟨⟨names, op⟩, hraw, rfl⟩ := List.mem_map.mp he
    obtain ⟨length, valid, operands⟩ := good_entry raw t h m hm (names, op)
      (raw_good raw t h m hm _ hraw)
    exact ⟨length, valid, operands, instClause_substitute d _ op
      (raw_clause raw t h m hm d sources memories _ hraw)⟩
  · rw [module_outputs]
    exact outputs_length m.ports (rename m)
  · intro pair hp
    rw [module_outputs] at hp
    obtain ⟨p, hport, dir, rfl⟩ := outputs_zip m.ports (rename m) pair hp
    exact output_has raw t h m hm p hport dir

end

end Silicon.Core.LowerProof
