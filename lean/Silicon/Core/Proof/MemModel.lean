import Silicon.Core.MemModel
import Silicon.Core.Mlir.WellFormed
import Silicon.Core.Semantics.Expression

/-!
The model and the core memory agree only on words below the declared depth.
-/
namespace Silicon.Core
namespace MemModelProof

private theorem decimal_injective {i j : Nat} (h : toString i = toString j) : i = j := by
  have h := congrArg (fun s : String => Nat.ofDigitChars 10 s.toList 0) h
  simpa [toString, Nat.repr_eq_ofList_toDigits, Nat.ofDigitChars_ten_toDigits] using h

inductive Name where
  | clk | reg
  | ra (i : Nat) | rd (i : Nat)
  | wa (i : Nat) | wd (i : Nat) | we (i : Nat) | ws (i : Nat) | wn (i : Nat)
  deriving DecidableEq

def Name.text : Name → String
  | .clk => "clk" | .reg => "reg$$mem"
  | .ra i => s!"r{i}_addr" | .rd i => s!"r{i}_data"
  | .wa i => s!"w{i}_addr" | .wd i => s!"w{i}_data"
  | .we i => s!"w{i}_en" | .ws i => s!"w{i}_set" | .wn i => s!"w{i}_next"

theorem Name.text_injective : Function.Injective Name.text := by
  intro x y h
  cases x <;> cases y <;> simp only [Name.text] at h
  all_goals try rfl
  all_goals try
    simp only [String.append_left_inj, String.append_right_inj] at h
    exact congrArg _ (decimal_injective h)
  all_goals
    have hr := congrArg (fun s : String => s.toList.reverse) h
    try simp [toString, String.toList_append, List.reverse_append] at hr
  all_goals
    have hf := congrArg (fun s : String => s.toList) h
    simp [toString, String.toList_append] at hf

open Mlir

def Name.ty (c : MemConfig) : Name → Mlir.Ty
  | .clk => .clock
  | .reg | .ws _ | .wn _ => .array (2 ^ Typed.addressWidth c.depth) c.width
  | .ra _ | .wa _ => .int (Typed.addressWidth c.depth)
  | .rd _ | .wd _ => .int c.width
  | .we _ => .int 1

def portKeys (c : MemConfig) : List Name :=
  [.clk] ++ (List.range c.reads).flatMap (fun i => [.ra i, .rd i]) ++
    (List.range c.writes).flatMap (fun i => [.wa i, .wd i, .we i])

def defKeys (c : MemConfig) : List Name :=
  [.clk] ++ (List.range c.reads).map .ra ++
    (List.range c.writes).flatMap (fun i => [.wa i, .wd i, .we i]) ++
    (List.range c.reads).map .rd ++
    (List.range c.writes).flatMap (fun i => [.ws i, .wn i]) ++ [.reg]

private theorem flat_nodup (l : List α) (f : α → List Name) (hl : l.Nodup)
    (hf : ∀ i ∈ l, (f i).Nodup)
    (hd : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, a ≠ b) :
    (l.flatMap f).Nodup := by
  rw [List.Nodup, List.pairwise_flatMap]
  refine ⟨hf, ?_⟩
  exact List.Pairwise.imp_of_mem (fun hi hj hij => hd _ hi _ hj hij) hl

private theorem portKeys_nodup (c : MemConfig) : (portKeys c).Nodup := by
  have hr := flat_nodup (List.range c.reads) (fun i => [Name.ra i, .rd i])
    (List.nodup_range) (by simp) (by simp_all)
  have hw := flat_nodup (List.range c.writes) (fun i => [Name.wa i, .wd i, .we i])
    (List.nodup_range) (by simp) (by simp_all)
  simp_all [portKeys, List.nodup_append, List.mem_flatMap]
  grind

private theorem defKeys_nodup (c : MemConfig) : (defKeys c).Nodup := by
  have hw := flat_nodup (List.range c.writes) (fun i => [Name.wa i, .wd i, .we i])
    (List.nodup_range) (by simp) (by simp_all)
  have hn := flat_nodup (List.range c.writes) (fun i => [Name.ws i, .wn i])
    (List.nodup_range) (by simp) (by simp_all)
  have hr : ((List.range c.reads).map Name.ra).Nodup := by
    simpa [List.Nodup, List.pairwise_map] using (List.nodup_range (n := c.reads))
  have hd : ((List.range c.reads).map Name.rd).Nodup := by
    simpa [List.Nodup, List.pairwise_map] using (List.nodup_range (n := c.reads))
  simp_all [defKeys, List.nodup_append, List.mem_flatMap, List.mem_map]
  grind

private theorem ports_names (c : MemConfig) :
    ((memModel c).ports.map Mlir.Port.name) = (portKeys c).map Name.text := by
  simp [memModel, MemConfig.ports, portKeys, List.map_flatMap, Name.text]

private theorem definitions (c : MemConfig) :
    (memModel c).definitions = (defKeys c).map (fun k => (k.text, k.ty c)) := by
  simp [Module.definitions, Module.inputPorts, memModel, MemConfig.ports, defKeys,
    List.filter_append, List.filter_flatMap, List.map_flatMap, List.flatMap_append,
    List.flatMap_assoc, List.flatMap_map, Function.comp_def, Op.resultTypes, Name.text,
    Name.ty, ← List.map_eq_flatMap]

private theorem lookup_key (l : List Name) (f : Name → α) (k : Name) (hk : k ∈ l) :
    (l.map (fun k => (k.text, f k))).lookup k.text = some (f k) := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    by_cases h : k = a
    · subst k; simp
    · have ht : k.text ≠ a.text := fun he => h (Name.text_injective he)
      simp only [List.mem_cons] at hk
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr ht, ih (hk.resolve_left h)]

private theorem lookup_def (c : MemConfig) (k : Name) (hk : k ∈ defKeys c) :
    (memModel c).definitions.lookup k.text = some (k.ty c) := by
  rw [definitions]
  exact lookup_key _ (Name.ty c) k hk

private def before (w : Nat) : Name := if w = 0 then .reg else .wn (w - 1)

private theorem before_text (w : Nat) :
    (before w).text = if w == 0 then "reg$$mem" else s!"w{w - 1}_next" := by
  by_cases h : w = 0 <;> simp [before, Name.text, h]

private theorem before_type (c : MemConfig) (w : Nat) :
    (before w).ty c = .array (2 ^ Typed.addressWidth c.depth) c.width := by
  by_cases h : w = 0 <;> simp [before, Name.ty, h]

private theorem before_mem (c : MemConfig) (w : Nat) (hw : w ≤ c.writes) :
    before w ∈ defKeys c := by
  by_cases h : w = 0
  · simp [before, h, defKeys]
  · simp only [before, ite_eq_right h]
    simp [defKeys, List.mem_flatMap, List.mem_map]
    omega

private theorem body_valid (c : MemConfig) (entry : List String × Mlir.Op)
    (he : entry ∈ (memModel c).body) :
    entry.1.length = entry.2.resultTypes.length ∧ entry.2.Valid ∧
    (∀ operand ∈ entry.2.operands,
      (memModel c).definitions.lookup operand.1 = some operand.2) ∧
    (match entry.2 with
    | .instance _ callee args results => ∃ ports,
        (Mlir.Design.mk [.module (memModel c)]).signature callee = some ports ∧
        args.map (fun (pin, _, ty) => (pin, ty)) =
          ((ports.filter (·.dir == .input)).map fun p => (p.name, p.ty)) ∧
        results = ((ports.filter (·.dir == .output)).map fun p => (p.name, p.ty))
    | _ => True) := by
  have lk := lookup_def c
  have lb (w) (hw : w ≤ c.writes) := lookup_def c (before w) (before_mem c w hw)
  simp only [before_text, before_type] at lb
  simp only [memModel, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (⟨r, hr, rfl⟩ | ⟨w, hw, rfl | rfl⟩) | rfl
  all_goals simp only [Op.resultTypes, Op.Valid, Op.operands, List.length_cons,
    List.length_nil, List.mem_cons, List.not_mem_nil,
    Option.toList_none, List.flatMap_nil, List.append_nil,
    or_false, true_and, and_true]
  all_goals intro operand ho
  all_goals rcases ho with rfl | rfl | rfl
  all_goals first
    | exact lb _ (by omega)
    | (apply lk (Name.reg); simp [defKeys])
    | (apply lk (Name.clk); simp [defKeys])
    | (apply lk (Name.ra _); simp [defKeys, List.mem_map]; assumption)
    | (apply lk (Name.wa _); simp [defKeys, List.mem_flatMap]; grind)
    | (apply lk (Name.wd _); simp [defKeys, List.mem_flatMap]; grind)
    | (apply lk (Name.we _); simp [defKeys, List.mem_flatMap]; grind)
    | (apply lk (Name.ws _); simp [defKeys, List.mem_flatMap]; grind)

private theorem outputs_ports (c : MemConfig) :
    (memModel c).outputPorts = (List.range c.reads).map
      (fun i => Mlir.Port.mk .output (Name.rd i).text (.int c.width)) := by
  simp [Module.outputPorts, memModel, MemConfig.ports, List.filter_flatMap,
    ← List.map_eq_flatMap, Name.text]

private theorem module_wellFormed (c : MemConfig) :
    (memModel c).WellFormed ⟨[.module (memModel c)]⟩ := by
  refine ⟨?_, ?_, ?_, body_valid c, ?_, ?_⟩
  · rw [ports_names, List.Nodup, List.pairwise_map]
    exact (portKeys_nodup c).imp (fun h he => h (Name.text_injective he))
  · rw [definitions, List.map_map, List.Nodup, List.pairwise_map]
    exact (defKeys_nodup c).imp (fun h he => h (Name.text_injective he))
  · have hn : (List.range c.reads).filterMap (fun _ => (none : Option String)) = [] :=
      List.filterMap_eq_nil_iff.mpr (by simp)
    have he : (List.range c.writes).flatMap (fun _ => ([] : List String)) = [] :=
      List.flatMap_eq_nil_iff.mpr (by simp)
    simpa [memModel, List.filterMap_append, List.filterMap_flatMap,
      List.filterMap_map, Function.comp_def] using
      (show ((List.range c.reads).filterMap (fun _ => (none : Option String)) ++
        (List.range c.writes).flatMap (fun _ => ([] : List String))).Nodup by
          rw [hn, he]; simp)
  · rw [outputs_ports]; simp [memModel]
  · rw [outputs_ports]
    change ∀ pair ∈ ((List.range c.reads).map fun i => (Name.rd i).text).zip _, _
    have hz (l : List Nat) : l.zip l = l.map (fun i => (i, i)) := by
      induction l <;> simp_all
    rw [List.zip_map, hz]
    simp only [List.map_map]
    intro pair hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    apply lookup_def c (.rd i)
    simp [defKeys, List.mem_map]
    simpa using hi

end MemModelProof

theorem memModel_wellFormed (c : MemConfig) :
    Mlir.WellFormed ⟨[.module (memModel c)]⟩ := by
  refine ⟨by simp, ?_, ?_, ⟨fun _ => 0, ?_⟩⟩
  · intro item hi
    simp only [List.mem_singleton] at hi
    subst item
    exact (MemModelProof.module_wellFormed c).1
  · intro m hm
    simp only [List.mem_singleton, Mlir.Item.module.injEq] at hm
    subst m
    exact MemModelProof.module_wellFormed c
  · intro m hm names inst callee args results he
    simp only [List.mem_singleton, Mlir.Item.module.injEq] at hm
    subst m
    simp [memModel, List.mem_flatMap] at he

namespace MemModelProof

open Mlir

/-! Each port carries its value at the current clock edge. -/
structure Inputs (c : MemConfig) where
  readAddr : Nat → BitVec (Typed.addressWidth c.depth)
  writeAddr : Nat → BitVec (Typed.addressWidth c.depth)
  writeData : Nat → BitVec c.width
  writeEnable : Nat → BitVec 1

def stages (input : Inputs c) (words : Fin n → BitVec c.width) :
    Nat → Fin n → BitVec c.width
  | 0 => words
  | w + 1 => Semantics.memoryWrite (stages input words w)
      (input.writeAddr w).toNat (input.writeData w) (input.writeEnable w)

def keyValue (c : MemConfig) (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (input : Inputs c) : Name → Mlir.Value
  | .clk => .clock
  | .reg => .array _ _ words
  | .ra r => .bits _ (input.readAddr r)
  | .rd r => .bits _ (Semantics.memoryRead words (input.readAddr r).toNat)
  | .wa w => .bits _ (input.writeAddr w)
  | .wd w => .bits _ (input.writeData w)
  | .we w => .bits _ (input.writeEnable w)
  | .ws w => .array _ _ (Semantics.memoryWrite (stages input words w)
      (input.writeAddr w).toNat (input.writeData w) 1)
  | .wn w => .array _ _ (stages input words (w + 1))

def values (c : MemConfig) (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (input : Inputs c) : Mlir.Env :=
  fun name => ((defKeys c).map (fun k => (k.text, keyValue c words input k))).lookup name

private theorem values_key (c : MemConfig) (words) (input : Inputs c)
    (k : Name) (hk : k ∈ defKeys c) :
    values c words input k.text = some (keyValue c words input k) :=
  lookup_key _ _ k hk

private theorem key_type (c : MemConfig) (words) (input : Inputs c) (k : Name) :
    (keyValue c words input k).ty = k.ty c := by cases k <;> rfl

@[simp] private theorem mem_defKeys (c : MemConfig) (k : Name) :
    k ∈ defKeys c ↔ match k with
      | .clk | .reg => True
      | .ra r | .rd r => r < c.reads
      | .wa w | .wd w | .we w | .ws w | .wn w => w < c.writes := by
  cases k <;> simp [defKeys, List.mem_flatMap, List.mem_map]

private theorem eval_get (env : Env) (arr idx : String)
    (words : Fin (2 ^ a) → BitVec w) (address : BitVec a)
    (ha : env arr = some (.array _ _ words)) (hi : env idx = some (.bits _ address)) :
    (Mlir.Op.arrayGet arr idx (2 ^ a) w a).eval env =
      some (.bits w (Semantics.memoryRead words address.toNat)) := by
  simp [Op.eval, Env.bits, ha, hi, Value.asArray, Value.asBits, address.isLt]

private theorem eval_inject (env : Env) (arr idx dat : String)
    (words : Fin (2 ^ a) → BitVec w) (address : BitVec a) (data : BitVec w)
    (ha : env arr = some (.array _ _ words)) (hi : env idx = some (.bits _ address))
    (hd : env dat = some (.bits _ data)) :
    (Mlir.Op.arrayInject arr idx dat (2 ^ a) w a).eval env =
      some (.array _ _ (Semantics.memoryWrite words address.toNat data 1)) := by
  simp [Op.eval, Env.bits, ha, hi, hd, Value.asArray, Value.asBits, address.isLt]

private theorem eval_mux (env : Env) (en yes no : String)
    (enable : BitVec 1) (a b : Mlir.Value) (ty : Mlir.Ty)
    (he : env en = some (.bits 1 enable)) (ha : env yes = some a)
    (hb : env no = some b) (hta : a.ty = ty) (htb : b.ty = ty) :
    (Mlir.Op.mux en yes no ty).eval env = some (Semantics.evalMux enable a b) := by
  simp [Op.eval, Env.bits, Env.typed, he, ha, hb, Value.asBits, hta, htb]

private theorem values_before (c : MemConfig) (words) (input : Inputs c) (w : Nat)
    (hw : w ≤ c.writes) :
    values c words input (before w).text = some (.array _ _ (stages input words w)) := by
  rw [values_key c words input _ (before_mem c w hw)]
  cases w with
  | zero => rfl
  | succ w => simp [before, keyValue]

private theorem memory_mux (words : Fin n → BitVec width) (addr : Nat)
    (data : BitVec width) (en : BitVec 1) :
    Semantics.evalMux en (Mlir.Value.array n width (Semantics.memoryWrite words addr data 1))
      (.array n width words) = .array n width (Semantics.memoryWrite words addr data en) := by
  unfold Semantics.evalMux
  split
  · rename_i h
    rw [h]
  · rename_i h
    congr 1
    funext i
    simp only [Semantics.memoryWrite, h, decide_false, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]

private theorem input_member (c : MemConfig) (p : Mlir.Port)
    (hp : p ∈ (memModel c).inputPorts) :
    ∃ k ∈ defKeys c, p.name = k.text ∧ p.ty = k.ty c ∧
      (k = .clk ∨ (∃ r, k = .ra r) ∨
        (∃ w, k = .wa w ∨ k = .wd w ∨ k = .we w)) := by
  simp only [Module.inputPorts, List.mem_filter] at hp
  simp [memModel, MemConfig.ports, List.mem_flatMap] at hp
  rcases hp with ⟨rfl | ⟨r, hr, rfl | rfl⟩ | ⟨w, hw, rfl | rfl | rfl⟩, h⟩
  all_goals first
    | (exact ⟨.clk, by simp [defKeys], rfl, rfl, Or.inl rfl⟩)
    | (exact ⟨.ra _, by simp [defKeys, List.mem_map, hr], rfl, rfl,
        Or.inr (Or.inl ⟨_, rfl⟩)⟩)
    | (exact ⟨.wa _, by simp [defKeys, List.mem_flatMap, hw], rfl, rfl,
        Or.inr (Or.inr ⟨_, Or.inl rfl⟩)⟩)
    | (exact ⟨.wd _, by simp [defKeys, List.mem_flatMap, hw], rfl, rfl,
        Or.inr (Or.inr ⟨_, Or.inr (Or.inl rfl)⟩)⟩)
    | (exact ⟨.we _, by simp [defKeys, List.mem_flatMap, hw], rfl, rfl,
        Or.inr (Or.inr ⟨_, Or.inr (Or.inr rfl)⟩)⟩)
    | contradiction

/-! Input values do not depend on memory contents. -/
def inputEnv (c : MemConfig) (input : Inputs c) : Mlir.Env := values c (fun _ => 0) input

private theorem inputs_value (c : MemConfig) (words) (input : Inputs c)
    (p : Mlir.Port) (hp : p ∈ (memModel c).inputPorts) :
    ∃ v, inputEnv c input p.name = some v ∧ v.ty = p.ty ∧
      values c words input p.name = some v := by
  obtain ⟨k, hk, hn, ht, hc⟩ := input_member c p hp
  rw [hn, ht]
  refine ⟨keyValue c words input k, ?_, key_type c words input k, values_key c words input k hk⟩
  unfold inputEnv
  rw [values_key c _ input k hk]
  rcases hc with rfl | ⟨r, rfl⟩ | ⟨w, rfl | rfl | rfl⟩ <;> rfl

private theorem body_solution (c : MemConfig) (words) (input : Inputs c) (σ : ModuleState)
    (hs : σ.regs "reg$$mem" = some (.array _ _ words)) :
    ∀ entry ∈ (memModel c).body, match entry with
    | (_, .instance ..) => False
    | (names, .compreg _ _ _ ty) => ∃ name v,
        names = [name] ∧ σ.regs name = some v ∧ v.ty = ty ∧
        values c words input name = some v
    | (names, op) => ∃ name v, names = [name] ∧
        op.eval (values c words input) = some v ∧ values c words input name = some v := by
  intro entry he
  have vk := values_key c words input
  have vb := values_before c words input
  simp only [before_text] at vb
  simp only [memModel, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (⟨r, hr, rfl⟩ | ⟨w, hw, rfl | rfl⟩) | rfl
  · refine ⟨(Name.rd r).text, keyValue c words input (.rd r), rfl, ?_,
      vk _ (by simp [hr])⟩
    exact eval_get _ _ _ _ _ (vk .reg (by simp)) (vk (.ra r) (by simp [hr]))
  · refine ⟨(Name.ws w).text, keyValue c words input (.ws w), rfl, ?_,
      vk _ (by simp [hw])⟩
    exact eval_inject _ _ _ _ _ _ _ (vb w (by omega))
      (vk (.wa w) (by simp [hw])) (vk (.wd w) (by simp [hw]))
  · refine ⟨(Name.wn w).text, keyValue c words input (.wn w), rfl, ?_,
      vk _ (by simp [hw])⟩
    exact (eval_mux _ _ _ _ _ _ _ _ (vk (.we w) (by simp [hw]))
      (vk (.ws w) (by simp [hw])) (vb w (by omega)) rfl rfl).trans
        (congrArg some (memory_mux _ _ _ _))
  · exact ⟨"reg$$mem", .array _ _ words, rfl, hs, rfl, vk .reg (by simp)⟩

private theorem no_instance (c : MemConfig) (name : String) :
    (memModel c).findInstance name = none := by
  simp [Module.findInstance, memModel, List.findSome?_append, List.findSome?_map,
    List.mem_flatMap]
  rintro a b x hx (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

private theorem at_path (c : MemConfig) (d : Mlir.Design) (path : Mlir.Path) :
    (memModel c).atPath d path = if path = [] then some (memModel c) else none := by
  cases path <;> simp [Module.atPath, no_instance]

theorem solution (c : MemConfig) (words) (input : Inputs c) (σ : ModuleState)
    (hs : σ.regs "reg$$mem" = some (.array _ _ words)) :
    IsSolution ⟨[.module (memModel c)]⟩ (memModel c) σ (inputEnv c input)
      (values c words input) := by
  refine ⟨fun _ => values c words input, rfl, ⟨?_, ?_⟩⟩
  · refine ⟨inputs_value c words input, ?_, (module_wellFormed c).2.2.2.2.1, ?_⟩
    · intro entry he
      have h := body_solution c words input σ hs entry he
      cases entry with
      | mk names op => cases op <;> first | exact h | exact False.elim h
    · intro i
      have hi : i.val < c.reads := by simpa [memModel] using i.isLt
      refine ⟨keyValue c words input (.rd i.val), ?_, ?_⟩
      · change values c words input ((memModel c).outputs[i.val]) = _
        simpa [memModel, Name.text] using
          values_key c words input (.rd i.val) (by simp [hi])
      · rw [outputs_ports]
        simp [List.getElem?_map, List.getElem?_range hi, keyValue, Value.ty]
  · intro path parent hp inst callee args hi
    rw [at_path] at hp
    split at hp
    · cases hp
      simp [no_instance] at hi
    · contradiction

private theorem local_solution (h : IsSolution d m σ inputs vals) :
    ∃ children, LocalSolution d m σ.regs inputs vals children := by
  obtain ⟨all, hr, hs⟩ := h
  exact ⟨fun name => all [name], hr ▸ hs.1⟩

private theorem reg_entry (c : MemConfig) :
    ([Name.reg.text], Mlir.Op.compreg (before c.writes).text Name.clk.text none
      (Name.reg.ty c)) ∈ (memModel c).body := by
  rw [before_text]
  simp [memModel, Name.text, Name.ty]

private theorem read_entry (c : MemConfig) (r : Nat) (hr : r < c.reads) :
    ([(Name.rd r).text], Mlir.Op.arrayGet Name.reg.text (Name.ra r).text
      (2 ^ Typed.addressWidth c.depth) c.width (Typed.addressWidth c.depth)) ∈
      (memModel c).body := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨r, List.mem_range.mpr hr, rfl⟩

private theorem inject_entry (c : MemConfig) (w : Nat) (hw : w < c.writes) :
    ([(Name.ws w).text], Mlir.Op.arrayInject (before w).text (Name.wa w).text
      (Name.wd w).text (2 ^ Typed.addressWidth c.depth) c.width
        (Typed.addressWidth c.depth)) ∈ (memModel c).body := by
  simp only [memModel, List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  exact ⟨w, List.mem_range.mpr hw, by rw [before_text]; simp [Name.text]⟩

private theorem mux_entry (c : MemConfig) (w : Nat) (hw : w < c.writes) :
    ([(Name.wn w).text], Mlir.Op.mux (Name.we w).text (Name.ws w).text
      (before w).text (Name.reg.ty c)) ∈ (memModel c).body := by
  simp only [memModel, List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  exact ⟨w, List.mem_range.mpr hw, by rw [before_text]; simp [Name.text, Name.ty]⟩

private theorem input_at (c : MemConfig) (input : Inputs c) (words)
    (h : LocalSolution d (memModel c) state (inputEnv c input) vals children)
    (k : Name) (hk : k ∈ defKeys c)
    (hp : Mlir.Port.mk .input k.text (k.ty c) ∈ (memModel c).inputPorts)
    (hv : keyValue c (fun _ => 0) input k = keyValue c words input k) :
    vals k.text = some (keyValue c words input k) := by
  obtain ⟨v, hi, _, he⟩ := h.1 _ hp
  have hc := values_key c (fun _ => 0) input k hk
  change inputEnv c input k.text = _ at hc
  rw [hv] at hc
  have : v = keyValue c words input k := Option.some.inj (hi.symm.trans hc)
  exact this ▸ he

private theorem input_port (c : MemConfig) (k : Name)
    (hk : match k with
      | .clk => True | .ra r => r < c.reads
      | .wa w | .wd w | .we w => w < c.writes | _ => False) :
    Mlir.Port.mk .input k.text (k.ty c) ∈ (memModel c).inputPorts := by
  cases k <;> simp_all [Module.inputPorts, memModel, MemConfig.ports,
    List.mem_flatMap, Name.text, Name.ty]
  all_goals apply Or.inr; exact ⟨_, hk, by simp⟩

private theorem equation_value (env : Env) (name : String) (op : Mlir.Op) (value : Mlir.Value)
    (h : ∃ n v, [name] = [n] ∧ op.eval env = some v ∧ env n = some v)
    (hv : op.eval env = some value) : env name = some value := by
  obtain ⟨n, v, hn, he, hv'⟩ := h
  cases List.singleton_inj.mp hn
  have := Option.some.inj (he.symm.trans hv)
  exact this ▸ hv'

private theorem current_value (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (h : LocalSolution d (memModel c) state inputs vals children)
    (hs : state Name.reg.text = some (.array _ _ words)) :
    vals Name.reg.text = some (.array _ _ words) := by
  obtain ⟨name, v, hn, he, _, hv⟩ := h.2.1 _ (reg_entry c)
  cases List.singleton_inj.mp hn
  have := Option.some.inj (he.symm.trans hs)
  exact this ▸ hv

private theorem stages_value (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) (input : Inputs c)
    (h : LocalSolution d (memModel c) state (inputEnv c input) vals children)
    (hs : state Name.reg.text = some (.array _ _ words)) (w : Nat) (hw : w ≤ c.writes) :
    vals (before w).text = some (.array _ _ (stages input words w)) := by
  induction w with
  | zero => exact current_value c words h hs
  | succ w ih =>
    have hw' : w < c.writes := by omega
    have prev := ih (by omega)
    have ha := input_at c input words h (.wa w) (by simp [hw'])
      (input_port c _ hw') rfl
    have hd := input_at c input words h (.wd w) (by simp [hw'])
      (input_port c _ hw') rfl
    have he := input_at c input words h (.we w) (by simp [hw'])
      (input_port c _ hw') rfl
    have set := equation_value _ _ _ _ (h.2.1 _ (inject_entry c w hw'))
      (eval_inject _ _ _ _ _ _ _ prev ha hd)
    have next := equation_value _ _ _ _ (h.2.1 _ (mux_entry c w hw'))
      ((eval_mux _ _ _ _ _ _ _ _ he set prev rfl rfl).trans
        (congrArg some (memory_mux _ _ _ _)))
    simpa [before, stages] using next

theorem reads_value (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) (input : Inputs c)
    (h : LocalSolution d (memModel c) state (inputEnv c input) vals children)
    (hs : state Name.reg.text = some (.array _ _ words)) (r : Nat) (hr : r < c.reads) :
    vals (Name.rd r).text = some (.bits _
      (Semantics.memoryRead words (input.readAddr r).toNat)) := by
  have ha := input_at c input words h (.ra r) (by simp [hr]) (input_port c _ hr) rfl
  exact equation_value _ _ _ _ (h.2.1 _ (read_entry c r hr))
    (eval_get _ _ _ _ _ (current_value c words h hs) ha)

private theorem find_register (c : MemConfig) :
    (memModel c).body.find? (fun entry => entry.1 == [Name.reg.text]) =
      some ([Name.reg.text], Mlir.Op.compreg (before c.writes).text Name.clk.text none
        (Name.reg.ty c)) := by
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨by simp, ?_⟩
  rw [before_text]
  simp only [memModel, Name.text, Name.ty]
  refine ⟨_, [], rfl, ?_⟩
  intro entry he
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ⟨r, _, rfl⟩ | ⟨w, _, rfl | rfl⟩
  all_goals simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
  all_goals intro hn; have hn := List.singleton_inj.mp hn
  all_goals first
    | exact Name.noConfusion (Name.text_injective (show (Name.rd _).text = Name.reg.text from hn))
    | exact Name.noConfusion (Name.text_injective (show (Name.ws _).text = Name.reg.text from hn))
    | exact Name.noConfusion (Name.text_injective (show (Name.wn _).text = Name.reg.text from hn))

theorem next_value (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (input : Inputs c) (σ : ModuleState)
    (vals : Env) (h : IsSolution ⟨[.module (memModel c)]⟩ (memModel c) σ
      (inputEnv c input) vals)
    (hs : σ.regs Name.reg.text = some (.array _ _ words)) :
    (nextState ⟨[.module (memModel c)]⟩ (memModel c) σ vals).regs Name.reg.text =
      some (.array _ _ (stages input words c.writes)) := by
  obtain ⟨children, hl⟩ := local_solution h
  have hc := input_at c input words hl .clk (by simp) (input_port c .clk trivial) rfl
  have hn := stages_value c words input hl hs c.writes (Nat.le_refl _)
  change ((memModel c).body.find? (fun entry => entry.1 == [Name.reg.text]) >>=
    fun entry => entry.2.nextValue vals) = _
  rw [find_register]
  simp [Op.nextValue, Env.typed, hc, hn, keyValue, Name.ty, Value.ty]

/-! The lemmas below hold in any design, because the model has no instance. -/

theorem local_values (c : MemConfig) (words) (input : Inputs c) (state : Env)
    (hs : state "reg$$mem" = some (.array _ _ words)) (d : Mlir.Design)
    (children : String → Env) :
    LocalSolution d (memModel c) state (inputEnv c input) (values c words input) children := by
  refine ⟨inputs_value c words input, ?_, (module_wellFormed c).2.2.2.2.1, ?_⟩
  · intro entry he
    have h := body_solution c words input ⟨fun _ => state⟩ hs entry he
    cases entry with
    | mk names op => cases op <;> first | exact h | exact False.elim h
  · intro i
    have hi : i.val < c.reads := by simpa [memModel] using i.isLt
    refine ⟨keyValue c words input (.rd i.val), ?_, ?_⟩
    · change values c words input ((memModel c).outputs[i.val]) = _
      simpa [memModel, Name.text] using
        values_key c words input (.rd i.val) (by simp [hi])
    · rw [outputs_ports]
      simp [List.getElem?_map, List.getElem?_range hi, keyValue, Value.ty]

theorem findInstance_none (c : MemConfig) (name : String) :
    (memModel c).findInstance name = none := no_instance c name

theorem atPath_cons (c : MemConfig) (d : Mlir.Design) (name : String) (path : Mlir.Path) :
    (memModel c).atPath d (name :: path) = none := by
  rw [at_path]
  simp

theorem local_next (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) (input : Inputs c)
    (h : LocalSolution d (memModel c) state (inputEnv c input) vals children)
    (hs : state "reg$$mem" = some (.array _ _ words)) :
    ((memModel c).body.find? (fun entry => entry.1 == ["reg$$mem"]) >>=
      fun entry => entry.2.nextValue vals) =
      some (.array _ _ (stages input words c.writes)) := by
  have hc := input_at c input words h .clk (by simp) (input_port c .clk trivial) rfl
  have hn := stages_value c words input h hs c.writes (Nat.le_refl _)
  change ((memModel c).body.find? (fun entry => entry.1 == [Name.reg.text]) >>=
    fun entry => entry.2.nextValue vals) = _
  rw [find_register]
  simp [Op.nextValue, Env.typed, hc, hn, keyValue, Name.ty, Value.ty]

/-- The model inputs are the clock, the read addresses, and the write ports. -/
theorem input_port_cases (c : MemConfig) (p : Mlir.Port) (hp : p ∈ (memModel c).inputPorts) :
    p = ⟨.input, "clk", .clock⟩ ∨
      (∃ r < c.reads, p = ⟨.input, s!"r{r}_addr", .int (Typed.addressWidth c.depth)⟩) ∨
      ∃ w < c.writes, p = ⟨.input, s!"w{w}_addr", .int (Typed.addressWidth c.depth)⟩ ∨
        p = ⟨.input, s!"w{w}_data", .int c.width⟩ ∨ p = ⟨.input, s!"w{w}_en", .int 1⟩ := by
  have input : p.dir = .input := by
    simp only [Module.inputPorts, List.mem_filter] at hp
    simpa using hp.2
  obtain ⟨k, hk, hn, ht, kind⟩ := input_member c p hp
  obtain ⟨dir, name, ty⟩ := p
  simp only at input hn ht
  subst input hn ht
  rcases kind with rfl | ⟨r, rfl⟩ | ⟨w, rfl | rfl | rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨r, by simpa [defKeys] using hk, rfl⟩)
  all_goals exact Or.inr (Or.inr ⟨w, by simpa [defKeys] using hk, by simp [Name.text, Name.ty]⟩)

/-- Port inputs read back from an environment that types every input port. -/
def Inputs.ofEnv (c : MemConfig) (env : Env) : Inputs c :=
  ⟨fun r => (env.bits s!"r{r}_addr" _).getD 0, fun w => (env.bits s!"w{w}_addr" _).getD 0,
    fun w => (env.bits s!"w{w}_data" _).getD 0, fun w => (env.bits s!"w{w}_en" _).getD 0⟩

private theorem bits_of_ty {v : Mlir.Value} {w : Nat} (h : v.ty = .int w) :
    ∃ x, v = .bits w x := by
  cases v with
  | bits w' x =>
    cases h
    exact ⟨x, rfl⟩
  | array => cases h
  | clock => cases h

theorem ofEnv_agrees (c : MemConfig) (env : Env)
    (typed : ∀ p ∈ (memModel c).inputPorts, ∃ v, env p.name = some v ∧ v.ty = p.ty) :
    ∀ p ∈ (memModel c).inputPorts, env p.name = inputEnv c (Inputs.ofEnv c env) p.name := by
  intro p hp
  obtain ⟨v, hv, ty⟩ := typed p hp
  obtain ⟨k, hk, hn, ht, kind⟩ := input_member c p hp
  have value := values_key c (fun _ => 0) (Inputs.ofEnv c env) k hk
  change inputEnv c _ k.text = _ at value
  rw [hn, value, ← hn, hv]
  rw [ht] at ty
  rcases kind with rfl | ⟨r, rfl⟩ | ⟨w, rfl | rfl | rfl⟩
  · cases v <;> simp_all [Name.ty, Value.ty, keyValue]
  all_goals
    obtain ⟨x, rfl⟩ := bits_of_ty ty
    rw [hn] at hv
    simp only [Name.text] at hv
    simp only [keyValue, Inputs.ofEnv, Env.bits, hv]
    simp [Value.asBits]

theorem depth_bound (c : MemConfig) : c.depth ≤ 2 ^ Typed.addressWidth c.depth := by
  have hpos := Nat.two_pow_pos (Typed.addressWidth c.depth)
  by_cases h : c.depth ≤ 1
  · omega
  · have hb : c.depth - 1 ≠ 0 := by omega
    have hx := (Nat.log2_lt hb).mp
      (show (c.depth - 1).log2 < Typed.addressWidth c.depth by
        unfold Typed.addressWidth; omega)
    omega

/-! The relation leaves all words outside the core memory free. -/
def Agrees (c : MemConfig) (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (memory : Fin c.depth → BitVec c.width) : Prop :=
  ∀ i : Fin c.depth, words ⟨i.val, Nat.lt_of_lt_of_le i.isLt (depth_bound c)⟩ = memory i

private theorem stages_agree (c : MemConfig) (input : Inputs c) (words) (memory)
    (h : Agrees c words memory) (w : Nat) :
    Agrees c (stages input words w) (stages input memory w) := by
  induction w with
  | zero => exact h
  | succ w ih =>
    intro i
    simp only [stages, Semantics.memoryWrite]
    split
    · rfl
    · exact ih i

private theorem reads_agree (c : MemConfig) (words) (memory) (h : Agrees c words memory)
    (address : Nat) (ha : address < c.depth) :
    Semantics.memoryRead words address = Semantics.memoryRead memory address := by
  simp only [Semantics.memoryRead, ha,
    Nat.lt_of_lt_of_le ha (depth_bound c), ↓reduceDIte]
  exact h ⟨address, ha⟩

/-! Constant expressions expose the core update for already evaluated port inputs. -/
def Inputs.coreWrites (input : Inputs c) : List (Typed.Write [] c.width c.depth) :=
  (List.range c.writes).map fun w =>
    ⟨w, ⟨0, 0, []⟩, w, .const ⟨0, 0, []⟩ _ (input.writeAddr w).toNat,
      .const ⟨0, 0, []⟩ _ (input.writeData w).toNat,
      .const ⟨0, 0, []⟩ 1 (input.writeEnable w).toNat⟩

def Inputs.coreNext (input : Inputs c) (memory : Fin c.depth → BitVec c.width) :=
  Semantics.nextMemory (fun _ _ _ => 0) (fun _ _ _ _ _ => 0) memory input.coreWrites

theorem coreNext_eq (c : MemConfig) (input : Inputs c) (memory) :
    input.coreNext memory = stages input memory c.writes := by
  have sorted : input.coreWrites.Pairwise (fun a b => decide (a.port ≤ b.port) = true) := by
    simpa [Inputs.coreWrites, List.pairwise_map] using
      (List.pairwise_le_range (n := c.writes))
  unfold Inputs.coreNext Semantics.nextMemory
  rw [List.mergeSort_of_pairwise sorted]
  simp only [Inputs.coreWrites, List.foldl_map, Semantics.evalExpr, BitVec.ofNat_toNat]
  have hf (n : Nat) : (List.range n).foldl
      (fun m w => Semantics.memoryWrite m (input.writeAddr w).toNat
        (input.writeData w) (input.writeEnable w)) memory = stages input memory n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.range_succ, List.foldl_append, stages, ih]
  simpa using hf c.writes

end MemModelProof

open MemModelProof in
theorem mem_model_correct (c : MemConfig)
    (memory : Fin c.depth → BitVec c.width)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (σ : Mlir.ModuleState) (input : Inputs c)
    (state : σ.regs "reg$$mem" = some (.array _ _ words))
    (agree : Agrees c words memory)
    (inRange : (∀ r < c.reads, (input.readAddr r).toNat < c.depth) ∧
      (∀ w < c.writes, (input.writeAddr w).toNat < c.depth)) :
    (∃ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) σ (inputEnv c input) vals) ∧
    ∀ vals, Mlir.IsSolution ⟨[.module (memModel c)]⟩ (memModel c) σ (inputEnv c input) vals →
      (∀ r < c.reads, vals s!"r{r}_data" = some (.bits c.width
        (Semantics.memoryRead memory (input.readAddr r).toNat))) ∧
      ∃ nextWords, (Mlir.nextState ⟨[.module (memModel c)]⟩ (memModel c) σ vals).regs
        "reg$$mem" = some (.array _ _ nextWords) ∧
        Agrees c nextWords (input.coreNext memory) := by
  refine ⟨⟨values c words input, solution c words input σ state⟩, ?_⟩
  intro vals hv
  obtain ⟨children, hl⟩ := local_solution hv
  constructor
  · intro r hr
    have h := reads_value c words input hl state r hr
    rw [reads_agree c words memory agree _ (inRange.1 r hr)] at h
    exact h
  · refine ⟨stages input words c.writes, next_value c words input σ vals hv state, ?_⟩
    rw [coreNext_eq]
    exact stages_agree c input words memory agree c.writes

end Silicon.Core
