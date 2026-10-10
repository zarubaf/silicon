import Silicon.Core.Proof.Lower.Correct

namespace Silicon.Core.Test.LowerCorrect

open LowerProof
open MemModelProof

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def extendMemory (c : MemConfig) (memory : Fin c.depth → BitVec c.width)
    (padding : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) :
    Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width :=
  fun i => if h : i.val < c.depth then memory ⟨i.val, h⟩ else padding i

private theorem extendMemory_agrees (c : MemConfig) (memory) (padding) :
    MemModelProof.Agrees c (extendMemory c memory padding) memory := by
  intro i
  simp [extendMemory, i.isLt]

example (memory : Fin 12 → BitVec 8) (padding : BitVec 8) :
    MemModelProof.Agrees ⟨12, 8, 1, 1⟩
      (extendMemory ⟨12, 8, 1, 1⟩ memory (fun _ => padding)) memory :=
  extendMemory_agrees _ _ _

example (memory : Fin 1 → BitVec 4) (padding : BitVec 4) :
    MemModelProof.Agrees ⟨1, 4, 1, 1⟩
      (extendMemory ⟨1, 4, 1, 1⟩ memory (fun _ => padding)) memory :=
  extendMemory_agrees _ _ _

example (memory : Fin 16 → BitVec 8) (address : BitVec 4) :
    Semantics.memoryRead (extendMemory ⟨16, 8, 1, 1⟩ memory (fun _ => 99)) address.toNat =
      Semantics.memoryRead memory address.toNat :=
  full_depth_read ⟨16, 8, 1, 1⟩ _ _ (extendMemory_agrees _ _ _) (by decide) address

private def noOutputRaw : Core.Design :=
  ⟨"top", [.module ⟨⟨1, 1, []⟩, "top", [], []⟩], ⟨1, 1, []⟩⟩

private def noOutputBody : Typed.Module where
  pos := ⟨1, 1, []⟩
  name := "top"
  ports := []
  ctx := []
  interfaces := Typed.portsOf noOutputRaw
  body := []
  children := Typed.designDeps noOutputRaw noOutputRaw.depsFuel
  ranks := []
  acyclic := by simp [Typed.equationsErase, Deps.graph, Typed.Ranked]
  context_eq := by simp [Typed.equationsErase, Typed.contextFromPorts]

private def noOutputTyped : Typed.Design where
  top := "top"
  itemNames := ["top"]
  externs := []
  bodies := [noOutputBody]
  topPos := ⟨1, 1, []⟩
  hierarchy := by
    simp [Typed.ordered, Typed.childNames, noOutputBody, Typed.Module.erase, Typed.equationsErase]
  environments := by
    intro m hm
    have same := List.mem_singleton.mp hm
    subst m
    have assembled : Typed.assembleDesign "top" ["top"] [] [noOutputBody] ⟨1, 1, []⟩ =
        noOutputRaw := by
      simp [Typed.assembleDesign, noOutputBody, Typed.Module.erase,
        Typed.equationsErase, noOutputRaw]
    rw [assembled]
    exact ⟨rfl, rfl, by simp [noOutputRaw, noOutputBody, Typed.Module.erase,
      Typed.equationsErase]⟩

private theorem noOutput_wf : WellFormed noOutputTyped.erase :=
  (Check.no_errors _).mp (by cbv)

example : ∃ t, check noOutputTyped.erase = .ok t :=
  check_complete noOutputTyped.erase noOutput_wf

private def noOutputModule : Mlir.Module := ⟨"top", [], [], []⟩

private theorem noOutput_lower : ((lower noOutputTyped).withModels (memoryConfigs noOutputTyped)) =
    ⟨[.module noOutputModule]⟩ := by cbv

example : Mlir.WellFormed ((lower noOutputTyped).withModels (memoryConfigs noOutputTyped)) := by
  rw [noOutput_lower]
  refine ⟨by simp [Mlir.Item.name], ?_, ?_, ⟨fun _ => 0, ?_⟩⟩
  · simp [Mlir.Item.ports, noOutputModule]
  · intro m hm
    simp only [List.mem_singleton, Mlir.Item.module.injEq] at hm
    subst m
    simp [Mlir.Module.WellFormed, Mlir.Module.definitions, Mlir.Module.inputPorts,
      Mlir.Module.outputPorts, noOutputModule]
  · intro m hm
    simp only [List.mem_singleton, Mlir.Item.module.injEq] at hm
    subst m
    simp [noOutputModule]

private theorem noOutput_solution (σ : Mlir.ModuleState) (inputs : Mlir.Env) :
    ∃ vals, Mlir.IsSolution ((lower noOutputTyped).withModels (memoryConfigs noOutputTyped))
      noOutputModule σ inputs vals := by
  refine ⟨fun _ => none, fun _ _ => none, rfl, ?_, ?_⟩
  · simp [Mlir.LocalSolution, noOutputModule, Mlir.Module.inputPorts, Mlir.Module.outputPorts]
  · intro path parent found inst callee args member
    cases path with
    | nil =>
      simp [Mlir.Module.atPath] at found
      subst parent
      simp [noOutputModule, Mlir.Module.findInstance] at member
    | cons name path =>
      simp [Mlir.Module.atPath, noOutputModule, Mlir.Module.findInstance] at found

private def noOutputCertified : Semantics.CertifiedDesign := ⟨noOutputTyped, noOutput_wf⟩
private def noOutputEnv : Semantics.Env noOutputCertified.design :=
  fun _ member => nomatch member
private theorem noOutput_member : noOutputBody ∈ noOutputCertified.design.bodies :=
  List.mem_cons_self ..
private theorem noOutput_noExterns : noOutputCertified.design.externs = [] := rfl

private def noOutputState :
    Semantics.State noOutputCertified noOutputEnv noOutputBody noOutput_member :=
  fun eq => nomatch eq.property

private def noOutputInput : Semantics.Input noOutputBody :=
  fun port => nomatch port.property.1

private theorem noOutput_corresponds
    (s : Semantics.State noOutputCertified noOutputEnv noOutputBody noOutput_member)
    (σ : Mlir.ModuleState) :
    Corresponds noOutputCertified noOutputEnv noOutput_noExterns
      noOutputBody noOutput_member s σ := by
  intro path name cell found
  cases path <;> simp only [List.nil_append, List.cons_append] at found <;>
    rw [Semantics.namedState.eq_def] at found <;> contradiction

example (σ : Mlir.ModuleState) (inputs : Mlir.Env) :
    Corresponds noOutputCertified noOutputEnv noOutput_noExterns
      noOutputBody noOutput_member noOutputState σ ∧
    (∃ vals, Mlir.IsSolution ((lower noOutputTyped).withModels (memoryConfigs noOutputTyped))
      noOutputModule σ inputs vals) ∧
    ∀ vals, Mlir.IsSolution ((lower noOutputTyped).withModels (memoryConfigs noOutputTyped))
      noOutputModule σ inputs vals →
      Corresponds noOutputCertified noOutputEnv noOutput_noExterns noOutputBody noOutput_member
        (Semantics.step noOutputCertified noOutputEnv noOutputBody noOutput_member
          noOutputState noOutputInput).1
        (Mlir.nextState ((lower noOutputTyped).withModels (memoryConfigs noOutputTyped))
          noOutputModule σ vals) :=
  ⟨noOutput_corresponds _ _, noOutput_solution σ inputs, fun _ _ => noOutput_corresponds _ _⟩

private def resetMemories (memory : Fin 12 → BitVec 8) :
    Semantics.Memories [(.name "m", .memory 8 12)] := fun _ _ _ found => by
  simp only [List.lookup] at found
  split at found
  · cases found
    exact memory
  · contradiction

private def memoryReset : Typed.Reset [(.name "m", .memory 8 12)] 8 :=
  ⟨.sync, .const ⟨1, 1, []⟩ 1 1, .read ⟨1, 1, []⟩ "m" rfl (.const ⟨1, 1, []⟩ _ 3)⟩

private def resetOperands (memory : Fin 12 → BitVec 8) : Mlir.Env
  | "clk" => some .clock
  | "rst" => some (.bits 1 1)
  | "value" => some (.bits 8 (memory ⟨3, by decide⟩))
  | "next" => some (.bits 8 7)
  | _ => none

example (memory : Fin 12 → BitVec 8) :
    (Mlir.Op.compreg "next" "clk" (some ("rst", "value")) (.int 8)).nextValue
      (resetOperands memory) = some (.bits 8 (memory ⟨3, by decide⟩)) :=
  next_register_reset (resetOperands memory) (fun _ _ _ => 0) (resetMemories memory)
    (.const ⟨1, 1, []⟩ 8 7) memoryReset "next" "clk" "rst" "value" rfl rfl rfl rfl

/-! The checker must separate source names from generated instance result names. -/
private def collisionRaw : Core.Design :=
  let p : Pos := ⟨1, 1, []⟩
  ⟨"top", [
    .module ⟨p, "child", [⟨p, .output, "q", .bits 1⟩],
      [.assign p "q" (.const p 1 1)]⟩,
    .module ⟨p, "top", [⟨p, .input, "u.q", .bits 1⟩],
      [.inst p "u" "child" []]⟩], p⟩

#guard (check collisionRaw).toOption.isNone

/-! Erasure can hide duplicate typed bodies, so its certificate does not prove unique items. -/
private def duplicateBodiesTyped : Typed.Design where
  top := "top"
  itemNames := ["top"]
  externs := []
  bodies := [noOutputBody, noOutputBody]
  topPos := ⟨1, 1, []⟩
  hierarchy := by
    simp [Typed.ordered, Typed.childNames, noOutputBody, Typed.Module.erase, Typed.equationsErase]
  environments := by
    intro m hm
    have same : m = noOutputBody := by simpa using hm
    subst m
    have assembled : Typed.assembleDesign "top" ["top"] []
        [noOutputBody, noOutputBody] ⟨1, 1, []⟩ = noOutputRaw := by
      simp [Typed.assembleDesign, noOutputBody, Typed.Module.erase,
        Typed.equationsErase, noOutputRaw]
    rw [assembled]
    exact ⟨rfl, rfl, by simp [noOutputRaw, noOutputBody, Typed.Module.erase,
      Typed.equationsErase]⟩

private theorem duplicateBodies_erase : duplicateBodiesTyped.erase = noOutputTyped.erase := by
  rfl

private theorem duplicateBodies_wf : WellFormed duplicateBodiesTyped.erase := by
  rw [duplicateBodies_erase]
  exact noOutput_wf

example : ∃ t, check duplicateBodiesTyped.erase = .ok t :=
  check_complete duplicateBodiesTyped.erase duplicateBodies_wf

private theorem duplicateBodies_lower :
    (lower duplicateBodiesTyped).withModels (memoryConfigs duplicateBodiesTyped) =
      ⟨[.module noOutputModule, .module noOutputModule]⟩ := by cbv

private theorem duplicateBodies_not_wellFormed :
    ¬ Mlir.WellFormed
      ((lower duplicateBodiesTyped).withModels (memoryConfigs duplicateBodiesTyped)) := by
  rw [duplicateBodies_lower]
  intro h
  have names := h.1
  simp [Mlir.Item.name, noOutputModule] at names

theorem certificate_does_not_imply_lower_wellFormed :
    ¬ (∀ d : Semantics.CertifiedDesign, d.design.externs = [] →
      Mlir.WellFormed ((lower d.design).withModels (memoryConfigs d.design))) := by
  intro claim
  exact duplicateBodies_not_wellFormed (claim ⟨duplicateBodiesTyped, duplicateBodies_wf⟩ rfl)

/-!
The instances below apply `lower_correct` to five checked designs. Each instance discharges the
check, the absence of externs, and a corresponding pair of states, so the theorem is not vacuous.
A memory word above the core depth starts at zero in the witness MLIR state.
-/
section Instances

open Semantics

/-- A path that names a cell has no longer path below it. -/
theorem namedState_extend (d : CertifiedDesign) (env : Env d.design)
    (ne : d.design.externs = []) :
    ∀ (m : Typed.Module) (hm : m ∈ d.design.bodies) (s : State d env m hm)
      (path : List String) (cell : NamedCell) (a : String) (rest : List String),
      namedState d env ne m hm s path = some cell →
        namedState d env ne m hm s (path ++ a :: rest) = none
  | _, _, _, [], _, _, _, h => by rw [namedState] at h; contradiction
  | m, hm, s, name :: path, cell, a, rest, h => by
    rw [namedState] at h
    have nonempty : (path ++ a :: rest).isEmpty = false := by simp
    rw [List.cons_append, namedState]
    simp only [nonempty, Bool.false_eq_true, ite_false]
    split
    · rfl
    · rename_i eq he
      split <;> try rfl
      rename_i i p n child inputs member
      split
      · rename_i c childFound
        split at h
        · contradiction
        · rename_i eq₂ he₂
          rw [he] at he₂
          cases he₂
          dsimp only at h
          split at h
          · rename_i c₂ childFound₂
            rw [childFound] at childFound₂
            cases childFound₂
            exact namedState_extend d env ne c _ _ path cell a rest h
          · rename_i absent
            rw [childFound] at absent
            contradiction
      · rename_i absent
        obtain ⟨c, hc⟩ := instance_child_exists d ne m hm i p n child inputs member
        rw [hc] at absent
        contradiction

theorem externs_of_check (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t) :
    t.externs = raw.items.filterMap fun i => match i with | .extern e => some e | _ => none := by
  have he := check_elaborate raw t h
  simp only [Typed.elaborateDesign, bind, Option.bind_eq_some_iff] at he
  obtain ⟨sorted, _, he⟩ := he
  split at he <;> try contradiction
  split at he <;> try contradiction
  split at he <;> try contradiction
  split at he <;> try contradiction
  cases he
  rfl

theorem reg_name_inj {x y : String} (h : regName x = regName y) : x = y :=
  regName_injective h

theorem nodup_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | a :: l, unique, x, y, hx, hy, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at unique
    cases List.mem_cons.mp hx with
    | inl ex =>
      cases List.mem_cons.mp hy with
      | inl ey => exact ex.trans ey.symm
      | inr ty => subst ex; exact absurd ⟨y, ty, e.symm⟩ unique.1
    | inr tx =>
      cases List.mem_cons.mp hy with
      | inl ey => subst ey; exact absurd ⟨x, tx, e⟩ unique.1
      | inr ty => exact nodup_inj unique.2 tx ty e

noncomputable def witnessState (d : CertifiedDesign) (env : Env d.design)
    (ne : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (s : State d env m hm) : Mlir.ModuleState := by
  classical
  exact ⟨fun path n =>
    if h : ∃ x, n = (regName x) ∧
        ∃ w v, namedState d env ne m hm s (path ++ [x]) = some (.register w v) then
      match namedState d env ne m hm s (path ++ [h.choose]) with
      | some (.register w v) => some (.bits w v)
      | _ => none
    else if n = "reg$$mem" then
      match namedState d env ne m hm s path with
      | some (.memory w depth memory) =>
        some (.array _ _ (extendMemory ⟨depth, w, 0, 0⟩ memory (fun _ => 0)))
      | _ => none
    else none⟩

theorem witness_corresponds (d : CertifiedDesign) (env : Env d.design)
    (ne : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (s : State d env m hm) : Corresponds d env ne m hm s (witnessState d env ne m hm s) := by
  classical
  intro path name cell found
  cases cell with
  | register w v =>
    have ex : ∃ x, (regName name) = (regName x) ∧
        ∃ w v, namedState d env ne m hm s (path ++ [x]) = some (.register w v) :=
      ⟨name, rfl, w, v, found⟩
    show (witnessState d env ne m hm s).cells path (regName name) = _
    simp only [witnessState, dite_eq_left ex]
    have same : ex.choose = name := (reg_name_inj ex.choose_spec.1).symm
    rw [same, found]
  | memory w depth memory =>
    refine ⟨extendMemory ⟨depth, w, 0, 0⟩ memory (fun _ => 0), ?_, extendMemory_agrees _ _ _⟩
    have nex : ¬ ∃ x, "reg$$mem" = (regName x) ∧
        ∃ w v, namedState d env ne m hm s ((path ++ [name]) ++ [x]) = some (.register w v) := by
      rintro ⟨x, _, w', v', hx⟩
      rw [namedState_extend d env ne m hm s (path ++ [name]) _ x [] found] at hx
      contradiction
    simp only [witnessState, dite_eq_right nex, found]
    rfl

noncomputable def witnessInputs (ports : List Port) (input : PortValues ports .input) :
    Mlir.Env := by
  classical
  exact fun n => if h : ∃ p : PortRef ports .input, p.val.name = n then
    some (coreValue _ (input h.choose)) else none

theorem witness_inputs (ports : List Port) (unique : (ports.map Port.name).Nodup)
    (input : PortValues ports .input) : InputsAgree ports input (witnessInputs ports input) := by
  classical
  intro p
  have ex : ∃ q : PortRef ports .input, q.val.name = p.val.name := ⟨p, rfl⟩
  simp only [witnessInputs, dite_eq_left ex]
  have same : ex.choose = p :=
    Subtype.ext (nodup_inj unique ex.choose.property.1 p.property.1 ex.choose_spec)
  generalize ex.choose = q at same ⊢
  subst same
  rfl


def zeroValue : (ty : Ty) → TyValue ty
  | .clock => ()
  | .bits _ => 0

def LowerCorrectInstance (raw : Core.Design) : Prop :=
  ∃ t, ∃ h : check raw = .ok t, ∃ noExterns : t.externs = [], ∃ top,
    ∃ found : t.bodies.find? (·.name == t.top) = some top,
    let core := CertifiedDesign.ofCheck raw t h
    let env := NamedRun.emptyEnv core noExterns
    let hm := List.mem_of_find?_eq_some found
    let d := (lower t).withModels (memoryConfigs t)
    let s := Interp.zeroState core env noExterns top hm
    let input : Input top := fun p => zeroValue p.val.ty
    ∃ σ inputs, Corresponds core env noExterns top hm s σ ∧ InputsAgree top.ports input inputs ∧
      ∃ vals, Mlir.IsSolution d (Lower.module top).1 σ inputs vals ∧
        LoweredOutputsAgree top (Semantics.step core env top hm s input).2 vals ∧
        Corresponds core env noExterns top hm (Semantics.step core env top hm s input).1
          (Mlir.nextState d (Lower.module top).1 σ vals)

theorem lowerCorrect_instance (raw : Core.Design) (wf : WellFormed raw)
    (modulesOnly : (raw.items.filterMap fun i => match i with
      | .extern e => some e | _ => none) = []) :
    LowerCorrectInstance raw := by
  obtain ⟨t, h⟩ := check_complete raw wf
  have noExterns : t.externs = [] := (externs_of_check raw t h).trans modulesOnly
  obtain ⟨top, found⟩ := NamedRun.top_exists (CertifiedDesign.ofCheck raw t h) noExterns
  refine ⟨t, h, noExterns, top, found, ?_⟩
  intro core env hm d s input
  have unique := (List.nodup_append.mp (scope_nodup raw t h top hm)).1
  have corr := witness_corresponds core env noExterns top hm s
  have agree := witness_inputs top.ports unique input
  refine ⟨_, _, corr, agree, ?_⟩
  obtain ⟨_, correct⟩ := lower_correct raw t h noExterns env top found
  obtain ⟨⟨vals, solved⟩, every⟩ := correct s _ corr input _ agree
  exact ⟨vals, solved, every vals solved⟩

private def o : Pos := ⟨1, 1, []⟩

private def counterRaw : Core.Design :=
  ⟨"counter", [.module ⟨o, "counter",
    [⟨o, .input, "clk", .clock⟩, ⟨o, .input, "rst", .bits 1⟩, ⟨o, .input, "en", .bits 1⟩,
      ⟨o, .output, "q", .bits 8⟩],
    [.reg o "r" 8 "clk" (some ⟨.sync, .ref o "rst", .const o 8 0⟩),
      .let_ o "inc" 8 (.bin o .add (.ref o "r") (.const o 8 1)),
      .next o "r" (.mux o (.ref o "en") (.ref o "inc") (.ref o "r")),
      .assign o "q" (.ref o "r")]⟩], o⟩

example : LowerCorrectInstance counterRaw :=
  lowerCorrect_instance _ ((Check.no_errors _).mp (by cbv)) rfl

private def memoryRaw : Core.Design :=
  ⟨"top", [.module ⟨o, "top",
    [⟨o, .input, "clk", .clock⟩, ⟨o, .input, "x", .bits 4⟩, ⟨o, .input, "d", .bits 8⟩,
      ⟨o, .input, "we", .bits 1⟩, ⟨o, .output, "p", .bits 8⟩],
    [.mem o "m" 8 12 "clk",
      .write o "m" 0 (.ref o "x") (.ref o "d") (.ref o "we"),
      .assign o "p" (.read o "m" (.ref o "x"))]⟩], o⟩

example : LowerCorrectInstance memoryRaw :=
  lowerCorrect_instance _ ((Check.no_errors _).mp (by cbv)) rfl

private def hierarchyRaw : Core.Design :=
  ⟨"top", [
    .module ⟨o, "inner",
      [⟨o, .input, "clk", .clock⟩, ⟨o, .input, "a", .bits 8⟩, ⟨o, .output, "b", .bits 8⟩],
      [.reg o "r" 8 "clk" none, .next o "r" (.ref o "a"),
        .assign o "b" (.bin o .add (.ref o "r") (.ref o "a"))]⟩,
    .module ⟨o, "top",
      [⟨o, .input, "clk", .clock⟩, ⟨o, .input, "x", .bits 8⟩, ⟨o, .output, "y", .bits 8⟩],
      [.inst o "u" "inner" [("clk", .ref o "clk"), ("a", .ref o "x")],
        .assign o "y" (.port o "u" "b")]⟩], o⟩

example : LowerCorrectInstance hierarchyRaw :=
  lowerCorrect_instance _ ((Check.no_errors _).mp (by cbv)) rfl

private def handshakeRaw : Core.Design :=
  ⟨"top", [
    .module ⟨o, "stage",
      [⟨o, .input, "x", .bits 8⟩, ⟨o, .input, "ack", .bits 1⟩,
        ⟨o, .output, "y", .bits 8⟩, ⟨o, .output, "ready", .bits 1⟩],
      [.assign o "y" (.ref o "x"), .assign o "ready" (.ref o "ack")]⟩,
    .module ⟨o, "top",
      [⟨o, .input, "x", .bits 8⟩, ⟨o, .input, "ack", .bits 1⟩,
        ⟨o, .output, "y", .bits 8⟩, ⟨o, .output, "ready", .bits 1⟩],
      [.inst o "a" "stage" [("x", .ref o "x"), ("ack", .port o "b" "ready")],
        .inst o "b" "stage" [("x", .port o "a" "y"), ("ack", .ref o "ack")],
        .assign o "y" (.port o "b" "y"), .assign o "ready" (.port o "a" "ready")]⟩], o⟩

example : LowerCorrectInstance handshakeRaw :=
  lowerCorrect_instance _ ((Check.no_errors _).mp (by cbv)) rfl

example : LowerCorrectInstance noOutputRaw :=
  lowerCorrect_instance _ ((Check.no_errors _).mp (by cbv)) rfl

end Instances

end Silicon.Core.Test.LowerCorrect
