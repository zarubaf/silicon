import Silicon.Core.Proof.Lower.StatementTyping
import Silicon.Core.Proof.Lower.Emission

/-!
An environment that satisfies every plain op and every read of the final build state gives
each emitted result the core value of its expression. The proof needs no order on names.
-/
namespace Silicon.Core.LowerProof

open Semantics

/-- `env` satisfies the plain ops and the memory reads of `final`, and has the core values at
the source names. -/
structure Meaning (ctx : Typed.Ctx) where
  registers : List String
  final : Lower.State
  env : Mlir.Env
  values : Valuation ctx
  memories : Memories ctx
  words : ModelMemories ctx
  models : ∀ name width depth found,
    MemModelProof.Agrees ⟨depth, width, 0, 0⟩ (words name width depth found)
      (memories name width depth found)
  ops : ∀ names op, (names, op) ∈ final.body.toList → isInstance op = false →
    isCompreg op = false → ∃ name v, names = [name] ∧ env name = some v ∧ op.eval env = some v
  reads : ∀ r ∈ final.reads, ReadEquation words env r
  refs : ∀ node w found,
    env (Lower.valueName registers node) = some (.bits w (values node w found))
  clocks : ∀ name, ctx.lookup (.name name) = some .clock → env name = some .clock

variable {ctx : Typed.Ctx} (M : Meaning ctx)

/-- A build step whose results have known values once the final state contains it. -/
def Meaning.Step (action : Lower.Build α) (pre : Prop) (post : α → Prop) : Prop :=
  ∀ s, Grows s (action s).2 ∧ (Grows (action s).2 M.final → pre → post (action s).1)

theorem Meaning.step_bind (a : Lower.Build α) (b : α → Lower.Build β) (p : Prop)
    (q : α → Prop) (r : β → Prop) (ha : M.Step a p q) (hb : ∀ x, M.Step (b x) (q x) r) :
    M.Step (a >>= b) p r := by
  intro s
  obtain ⟨ga, ta⟩ := ha s
  obtain ⟨gb, tb⟩ := hb (a s).1 (a s).2
  exact ⟨ga.trans gb, fun grows hp => tb grows (ta (gb.trans grows) hp)⟩

theorem Meaning.step_weaken (a : Lower.Build α) (p p' : Prop) (q q' : α → Prop)
    (h : M.Step a p q) (hp : p' → p) (hq : ∀ x, p' → q x → q' x) : M.Step a p' q' := by
  intro s
  obtain ⟨g, t⟩ := h s
  exact ⟨g, fun grows pre => hq _ pre (t grows (hp pre))⟩

theorem Meaning.step_keep (a : Lower.Build α) (p : Prop) (q : α → Prop) (h : M.Step a p q) :
    M.Step a p (fun x => p ∧ q x) :=
  M.step_weaken a p p q _ h id (fun _ hp hq => ⟨hp, hq⟩)

theorem Meaning.step_pure (x : α) (p : Prop) : M.Step (pure x) p (fun y => y = x ∧ p) :=
  fun s => ⟨Grows.refl s, fun _ hp => ⟨rfl, hp⟩⟩

theorem Meaning.step_emit (dest : Option String) (op : Mlir.Op) (value : Mlir.Value)
    (plain : isInstance op = false) (stateless : isCompreg op = false) (p : Prop)
    (eval : p → op.eval M.env = some value) :
    M.Step (Lower.emit dest op) p (fun name => M.env name = some value) := by
  intro s
  refine ⟨grows_emit dest op s, fun grows hp => ?_⟩
  have member : ([dest.getD (toString s.nextTemp)], op) ∈ M.final.body.toList := by
    apply grows.body.subset
    rw [emit_body]
    simp
  obtain ⟨name, v, same, hv, hop⟩ := M.ops _ op member plain stateless
  cases List.singleton_inj.mp same
  show M.env (Lower.emit dest op s).1 = _
  rw [emit_result, hv, ← hop, eval hp]

theorem Meaning.step_named (dest : Option String) (value : String) (p : Prop) :
    M.Step (Lower.named dest value) p (fun name => name = value ∧ p) :=
  fun s => ⟨grows_named dest value s, fun _ hp => ⟨named_result dest value s, hp⟩⟩

theorem Meaning.step_inRange (depth : Nat) (addr : String)
    (address : BitVec (Typed.addressWidth depth)) :
    M.Step (Lower.inRange depth addr) (M.env addr = some (.bits _ address))
      (fun result => match result with
        | none => depth = 2 ^ Typed.addressWidth depth
        | some ok => M.env ok = some (.bits 1 (BitVec.ofBool (address.toNat < depth)))) := by
  unfold Lower.inRange
  by_cases full : depth = 2 ^ Typed.addressWidth depth
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = true from beq_iff_eq.mpr full,
      ↓reduceIte]
    exact M.step_weaken _ _ _ _ _ (M.step_pure none _) id (fun _ _ h => h.1 ▸ full)
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = false from by simp [full],
      Bool.false_eq_true, ↓reduceIte]
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_emit none _ _ rfl rfl _
      (fun _ => eval_constant M.env _ _ (guard_bound depth full))))
    intro bound
    apply M.step_bind _ _ _ _ _ (M.step_emit none _
      (.bits 1 (BitVec.ofBool (address.toNat < depth))) rfl rfl _ (fun h => by
        rw [← guard_value depth full address]
        exact eval_predicate M.env .ult addr bound _ _ h.1 h.2))
    intro ok
    exact M.step_weaken _ _ _ _ _ (M.step_pure (some ok) _) id
      (fun _ _ h => by rcases h with ⟨rfl, h⟩; exact h)

theorem lookup_memory_unique {ctx : Typed.Ctx} {name : String} {w w' d d' : Nat}
    (found : ctx.lookup (.name name) = some (.memory w d))
    (found' : ctx.lookup (.name name) = some (.memory w' d')) : w' = w ∧ d' = d := by
  rw [found] at found'
  cases found'
  exact ⟨rfl, rfl⟩

theorem bits_inj {w : Nat} {x y : BitVec w} (h : Mlir.Value.bits w x = .bits w y) : x = y := by
  cases h
  rfl

theorem Meaning.read_value (r : Lower.ReadPort) (hr : r ∈ M.final.reads)
    (width depth : Nat) (found : ctx.lookup (.name r.memory) = some (.memory width depth))
    (address : BitVec (Typed.addressWidth depth))
    (ha : M.env r.addr = some (.bits _ address)) :
    M.env (readName r) =
      some (.bits width (memoryRead (M.words r.memory width depth found) address.toNat)) := by
  obtain ⟨w', d', found', address', ha', hd⟩ := M.reads r hr
  obtain ⟨rfl, rfl⟩ := lookup_memory_unique found found'
  rw [ha] at ha'
  cases bits_inj (Option.some.inj ha')
  exact hd

theorem Meaning.step_expr (e : Typed.Expr ctx ty) (legal : Legal e) (dest : Option String) :
    M.Step (Lower.expr M.registers e dest) True
      (fun name => M.env name = some (coreValue ty (evalExpr M.values M.memories e))) := by
  induction e generalizing dest with
  | ref p node found =>
    exact M.step_weaken _ _ _ _ _ (M.step_named dest _ True) id
      (fun _ _ h => h.1 ▸ M.refs node _ found)
  | clock p name found =>
    exact M.step_weaken _ _ _ _ _ (M.step_pure name True) id
      (fun _ _ h => h.1 ▸ M.clocks name found)
  | const p w v => exact M.step_emit dest _ _ rfl rfl _ (fun _ => eval_constant M.env w v legal)
  | un p op a ih =>
    cases op
    apply M.step_bind _ _ _ _ _ (ih legal none)
    intro aName
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_emit none _ _ rfl rfl _
      (fun _ => eval_constant M.env _ _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide)))))
    intro ones
    exact M.step_emit dest _ _ rfl rfl _ (fun h => eval_not M.env _ _ _ h.1 h.2)
  | bin p op ordinary a b ia ib =>
    apply M.step_bind _ _ _ _ _ (ia legal.1 none)
    intro aName
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_weaken _ _ _ _ _
      (ib legal.2 none) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact M.step_emit dest _ _ rfl rfl _
      (fun h => eval_binary M.env op ordinary _ _ _ _ h.1 h.2)
  | concat p a b bound ia ib =>
    apply M.step_bind _ _ _ _ _ (ia legal.1 none)
    intro aName
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_weaken _ _ _ _ _
      (ib legal.2 none) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact M.step_emit dest _ _ rfl rfl _ (fun h => eval_concat M.env _ _ _ _ h.1 h.2)
  | icmp p pred a b ia ib =>
    apply M.step_bind _ _ _ _ _ (ia legal.1 none)
    intro aName
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_weaken _ _ _ _ _
      (ib legal.2 none) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact M.step_emit dest _ _ rfl rfl _ (fun h => eval_predicate M.env pred _ _ _ _ h.1 h.2)
  | mux p c a b ic ia ib =>
    apply M.step_bind _ _ _ _ _ (ic legal.1 none)
    intro cName
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_weaken _ _ _ _ _
      (ia legal.2.1 none) (fun _ => trivial) (fun _ _ h => h)))
    intro aName
    apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_weaken _ _ _ _ _
      (ib legal.2.2 none) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact M.step_emit dest _ _ rfl rfl _ (fun h => eval_mux M.env _ _ _ _ _ _ h.1.1 h.1.2 h.2)
  | extract p a lo count bound ih =>
    apply M.step_bind _ _ _ _ _ (ih legal none)
    intro aName
    exact M.step_emit dest _ _ rfl rfl _ (fun h => eval_extract M.env _ _ lo count h bound)
  | replicate p a count bound ih =>
    apply M.step_bind _ _ _ _ _ (ih legal.1 none)
    intro aName
    exact M.step_emit dest _ _ rfl rfl _ (fun h => eval_replicate M.env _ _ count h legal.2)
  | @read width depth p name found addr ih =>
    intro s
    have walk := ih legal none (reserve s name)
    cases hw : Lower.expr M.registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    let index := (s.readCounts.lookup name).getD 0
    let address := evalExpr M.values M.memories addr
    have guardStep := M.step_inRange depth a address (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guardStep
    rw [read_eq M.registers p name found addr dest s a walked hw guard state hg]
    have before : Grows s state :=
      (((grows_reserve s _).trans walk.1).trans (grows_record _ _)).trans guardStep.1
    have early (grows : Grows state M.final) : M.env a = some (.bits _ address) ∧
        M.env s!"{name}.r{index}_data" =
          some (.bits width (memoryRead (M.words name width depth found) address.toNat)) := by
      have w := walk.2 (((grows_record _ _).trans guardStep.1).trans grows) trivial
      have member : (⟨name, index, a⟩ : Lower.ReadPort) ∈ M.final.reads :=
        grows.reads.subset (guardStep.1.reads.subset (List.mem_cons_self ..))
      exact ⟨w, M.read_value ⟨name, index, a⟩ member width depth found address w⟩
    cases guard with
    | none =>
      obtain ⟨grow, rest⟩ := M.step_named dest s!"{name}.r{index}_data" True state
      refine ⟨before.trans grow, fun grows _ => ?_⟩
      have e := early (grow.trans grows)
      have full := guardStep.2 (grow.trans grows) e.1
      change M.env (Lower.named dest _ state).1 = _
      rw [(rest grows trivial).1, e.2]
      dsimp only [coreValue, evalExpr]
      rw [full_depth_read ⟨depth, width, 0, 0⟩ _ _ (M.models name _ _ found) full]
    | some ok =>
      have tail : M.Step (readTail dest s!"{name}.r{index}_data" width (some ok))
          (M.env ok = some (.bits 1 (BitVec.ofBool (address.toNat < depth))) ∧
            M.env s!"{name}.r{index}_data" =
              some (.bits width (memoryRead (M.words name width depth found) address.toNat)))
          (fun result => M.env result = some (.bits width
            (memoryRead (M.memories name width depth found) address.toNat))) := by
        apply M.step_bind _ _ _ _ _ (M.step_keep _ _ _ (M.step_emit none _ _ rfl rfl _
          (fun _ => eval_constant M.env _ 0 (Nat.two_pow_pos _))))
        intro zero
        apply M.step_emit dest _ _ rfl rfl _
        intro h
        have ev := eval_mux M.env ok s!"{name}.r{index}_data" zero _ _ _ h.1.1 h.1.2 h.2
        have gr := guarded_read _ _ _ (M.models name _ _ found) address
        rw [← gr]
        by_cases inside : address.toNat < depth
        · simpa [evalMux, inside] using ev
        · simpa [evalMux, inside] using ev
      obtain ⟨grow, rest⟩ := tail state
      refine ⟨before.trans grow, fun grows _ => ?_⟩
      have e := early (grow.trans grows)
      have g := guardStep.2 (grow.trans grows) e.1
      exact rest grows ⟨g, e.2⟩

end Silicon.Core.LowerProof
