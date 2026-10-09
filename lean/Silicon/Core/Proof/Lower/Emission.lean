import Silicon.Core.Proof.Lower.Expressions

/-!
Expression emission builds the value bindings used by the module image valuation.
The module proof must join these bindings at fresh names. No op equation is a premise.
-/
namespace Silicon.Core.LowerProof

open Semantics

abbrev Image := List (String × Mlir.Value)

def Image.Agrees (image : Image) (env : Mlir.Env) : Prop :=
  ∀ binding ∈ image, env binding.1 = some binding.2

abbrev ModelMemories (ctx : Typed.Ctx) :=
  (name : String) → (width depth : Nat) →
    ctx.lookup (.name name) = some (.memory width depth) →
      Fin (2 ^ Typed.addressWidth depth) → BitVec width

def ReadEquation (words : ModelMemories ctx) (env : Mlir.Env) (r : Lower.ReadPort) : Prop :=
  ∃ width depth, ∃ found, ∃ address : BitVec (Typed.addressWidth depth),
    env r.addr = some (.bits _ address) ∧
    env s!"{r.memory}.r{r.index}_data" =
      some (.bits width (memoryRead (words r.memory width depth found) address.toNat))

/-- A frame retains the old ops and proves only the appended op and read equations. -/
def EmissionFrame (words : ModelMemories ctx) (env : Mlir.Env)
    (before after : Lower.State) : Prop :=
  (∃ tail, after.body.toList = before.body.toList ++ tail ∧
    ∀ names op, (names, op) ∈ tail → ∃ name value,
      names = [name] ∧ env name = some value ∧ op.eval env = some value) ∧
  (∀ r ∈ after.reads, r ∈ before.reads ∨ ReadEquation words env r)

def allocatedNames (s : Lower.State) : List String :=
  s.body.toList.flatMap Prod.fst ++ s.reads.map (fun r => s!"{r.memory}.r{r.index}_data")

/-- Each binding accounts for one new op result or one new memory read result. -/
def Image.Accounts (image : Image) (before after : Lower.State) : Prop :=
  ∀ name, (image.map Prod.fst).count name + (allocatedNames before).count name =
    (allocatedNames after).count name

theorem accounts_refl (s : Lower.State) : Image.Accounts [] s s := by
  intro name
  simp

theorem accounts_trans (a b c : Lower.State) (xs ys : Image)
    (hx : xs.Accounts a b) (hy : ys.Accounts b c) : (xs ++ ys).Accounts a c := by
  intro name
  have ha := hx name
  have hb := hy name
  simp only [List.map_append, List.count_append]
  omega

theorem frame_refl (words : ModelMemories ctx) (env : Mlir.Env) (s : Lower.State) :
    EmissionFrame words env s s := by
  exact ⟨⟨[], by simp, by simp⟩, fun _ h => Or.inl h⟩

theorem frame_trans (words : ModelMemories ctx) (env : Mlir.Env)
    (a b c : Lower.State) (ab : EmissionFrame words env a b)
    (bc : EmissionFrame words env b c) : EmissionFrame words env a c := by
  obtain ⟨⟨xs, hx, ex⟩, rx⟩ := ab
  obtain ⟨⟨ys, hy, ey⟩, ry⟩ := bc
  refine ⟨⟨xs ++ ys, by simp [hy, hx, List.append_assoc], ?_⟩, ?_⟩
  · intro names op h
    rcases List.mem_append.mp h with h | h
    · exact ex names op h
    · exact ey names op h
  · intro r hr
    rcases ry r hr with hr | hr
    · exact rx r hr
    · exact Or.inr hr

def Emits (words : ModelMemories ctx) (action : Lower.Build α)
    (pre : Mlir.Env → Prop) (post : α → Mlir.Env → Prop) : Prop :=
  ∀ s, ∃ image : Image, image.Accounts s (action s).2 ∧
    ∀ env, image.Agrees env → pre env →
    EmissionFrame words env s (action s).2 ∧ post (action s).1 env

theorem emits_pure (words : ModelMemories ctx) (a : α) (p : Mlir.Env → Prop) :
    Emits words (pure a) p (fun result env => result = a ∧ p env) := by
  intro s
  exact ⟨[], accounts_refl s, fun env _ hp => ⟨frame_refl words env s, rfl, hp⟩⟩

theorem emits_bind (words : ModelMemories ctx) (a : Lower.Build α)
    (b : α → Lower.Build β) (p : Mlir.Env → Prop)
    (q : α → Mlir.Env → Prop) (r : β → Mlir.Env → Prop)
    (ha : Emits words a p q) (hb : ∀ x, Emits words (b x) (q x) r) :
    Emits words (a >>= b) p r := by
  intro s
  obtain ⟨xs, sx, hx⟩ := ha s
  obtain ⟨ys, sy, hy⟩ := hb (a s).1 (a s).2
  refine ⟨xs ++ ys, accounts_trans _ _ _ xs ys sx sy, ?_⟩
  intro env agree hp
  have ax := hx env (fun x h => agree x (List.mem_append_left _ h)) hp
  have by' := hy env (fun x h => agree x (List.mem_append_right _ h)) ax.2
  exact ⟨frame_trans words env _ _ _ ax.1 by'.1, by'.2⟩

theorem emits_weaken (words : ModelMemories ctx) (a : Lower.Build α)
    (p p' : Mlir.Env → Prop) (q q' : α → Mlir.Env → Prop)
    (h : Emits words a p q) (hp : ∀ env, p' env → p env)
    (hq : ∀ x env, p' env → q x env → q' x env) : Emits words a p' q' := by
  intro s
  obtain ⟨image, shape, hi⟩ := h s
  refine ⟨image, shape, fun env agree pre => ?_⟩
  have got := hi env agree (hp env pre)
  exact ⟨got.1, hq _ env pre got.2⟩

theorem emits_keep (words : ModelMemories ctx) (a : Lower.Build α)
    (p : Mlir.Env → Prop) (q : α → Mlir.Env → Prop)
    (h : Emits words a p q) : Emits words a p (fun x env => p env ∧ q x env) :=
  emits_weaken words a p p q _ h (fun _ hp => hp) (fun _ _ hp hq => ⟨hp, hq⟩)

theorem emits_emit (words : ModelMemories ctx) (dest : Option String)
    (op : Mlir.Op) (value : Mlir.Value) (p : Mlir.Env → Prop)
    (eval : ∀ env, p env → op.eval env = some value) :
    Emits words (Lower.emit dest op) p (fun name env => env name = some value) := by
  intro s
  cases dest with
  | none =>
    refine ⟨[(s!"silicon_t{s.nextTemp}", value)], ?_, ?_⟩
    · intro name
      change (_ : Nat) + (allocatedNames s).count name =
        (allocatedNames { s with
          nextTemp := s.nextTemp + 1
          body := s.body.push ([s!"silicon_t{s.nextTemp}"], op) }).count name
      simp [allocatedNames, List.flatMap_append, List.count_append, List.count_cons, Nat.add_comm,
        Nat.add_assoc]
    intro env agree hp
    have hv := agree _ (List.mem_singleton_self _)
    refine ⟨⟨⟨[([s!"silicon_t{s.nextTemp}"], op)], ?_, ?_⟩, ?_⟩, hv⟩
    · change (s.body.push _).toList = _
      rw [Array.toList_push]
    · intro names other h
      cases List.mem_singleton.mp h
      exact ⟨_, value, rfl, hv, eval env hp⟩
    · intro r hr
      exact Or.inl hr
  | some name =>
    refine ⟨[(name, value)], ?_, ?_⟩
    · intro n
      change (_ : Nat) + (allocatedNames s).count n =
        (allocatedNames { s with body := s.body.push ([name], op) }).count n
      simp [allocatedNames, List.flatMap_append, List.count_append, List.count_cons, Nat.add_comm,
        Nat.add_assoc]
    intro env agree hp
    have hv := agree _ (List.mem_singleton_self _)
    refine ⟨⟨⟨[([name], op)], ?_, ?_⟩, ?_⟩, hv⟩
    · change (s.body.push _).toList = _
      rw [Array.toList_push]
    · intro names other h
      cases List.mem_singleton.mp h
      exact ⟨_, value, rfl, hv, eval env hp⟩
    · intro r hr
      exact Or.inl hr

theorem emits_named (words : ModelMemories ctx) (dest : Option String)
    (name : String) (p : Mlir.Env → Prop) :
    Emits words (Lower.named dest name) p (fun result env => result = name ∧ p env) := by
  intro s
  refine ⟨[], ?_, fun env _ hp => ?_⟩
  · cases dest <;> exact accounts_refl s
  cases dest <;> exact ⟨⟨⟨[], by simp [Lower.named]; rfl, by simp⟩,
    fun _ h => Or.inl h⟩, rfl, hp⟩

/-- The environment must agree only at the source reads of this expression. -/
def ExpressionInputs (registers : List String) (values : Valuation ctx) (env : Mlir.Env) :
    Typed.Expr ctx ty → Prop
  | .ref _ node found => env (Lower.valueName registers node) = some (.bits _ (values node _ found))
  | .clock _ name _ => env name = some .clock
  | .const .. => True
  | .un _ _ a | .extract _ a .. | .replicate _ a .. | .read _ _ _ a =>
      ExpressionInputs registers values env a
  | .bin _ _ _ a b | .concat _ a b _ | .icmp _ _ a b =>
      ExpressionInputs registers values env a ∧ ExpressionInputs registers values env b
  | .mux _ c a b => ExpressionInputs registers values env c ∧
      ExpressionInputs registers values env a ∧ ExpressionInputs registers values env b

def coreValue : (ty : Ty) → TyValue ty → Mlir.Value
  | .bits w, v => .bits w v
  | .clock, _ => .clock

def Legal : Typed.Expr ctx ty → Prop
  | .ref .. | .clock .. => True
  | .const _ w v => v < 2 ^ w
  | .un _ _ a | .extract _ a .. | .read _ _ _ a => Legal a
  | .replicate (width := w) _ a .. => Legal a ∧ 0 < w
  | .bin _ _ _ a b | .concat _ a b _ | .icmp _ _ a b => Legal a ∧ Legal b
  | .mux _ c a b => Legal c ∧ Legal a ∧ Legal b

theorem emits_read (words : ModelMemories ctx) (name : String) (index : Nat)
    (width depth : Nat) (found : ctx.lookup (.name name) = some (.memory width depth))
    (addr : String) (address : BitVec (Typed.addressWidth depth)) :
    Emits words (modify fun s => { s with reads := ⟨name, index, addr⟩ :: s.reads })
      (fun env => env addr = some (.bits _ address))
      (fun _ env => env addr = some (.bits _ address) ∧
        env s!"{name}.r{index}_data" =
          some (.bits width (memoryRead (words name width depth found) address.toNat))) := by
  intro s
  refine ⟨[(s!"{name}.r{index}_data",
    .bits width (memoryRead (words name width depth found) address.toNat))], ?_, ?_⟩
  · intro n
    change (_ : Nat) + (allocatedNames s).count n =
      (allocatedNames { s with reads := ⟨name, index, addr⟩ :: s.reads }).count n
    simp [allocatedNames, List.count_append, List.count_cons, Nat.add_comm, Nat.add_assoc]
  intro env agree ha
  have hd := agree _ (List.mem_singleton_self _)
  refine ⟨⟨⟨[], by simp; rfl, by simp⟩, ?_⟩, ha, hd⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Or.inr ⟨width, depth, found, address, ha, hd⟩
  · exact Or.inl hr

theorem emits_inRange (words : ModelMemories ctx) (depth : Nat) (addr : String)
    (address : BitVec (Typed.addressWidth depth)) :
    Emits words (Lower.inRange depth addr)
      (fun env => env addr = some (.bits _ address))
      (fun result env => match result with
        | none => depth = 2 ^ Typed.addressWidth depth
        | some name => env name = some (.bits 1 (BitVec.ofBool (address.toNat < depth)))) := by
  unfold Lower.inRange
  by_cases full : depth = 2 ^ Typed.addressWidth depth
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = true from beq_iff_eq.mpr full,
      ↓reduceIte]
    exact emits_weaken words _ _ _ _ _ (emits_pure words none _)
      (fun _ h => h) (by intro x env _ h; rcases h with ⟨rfl, _⟩; exact full)
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = false from by simp [full],
      Bool.false_eq_true, ↓reduceIte]
    apply emits_bind words _ _ _ _ _
      (emits_keep words _ _ _ (emits_emit words none _ _ _
        (fun env _ => eval_constant env _ _ (guard_bound depth full))))
    intro bound
    apply emits_bind words _ _ _ _ _
      (emits_emit words none _ (.bits 1 (BitVec.ofBool (address.toNat < depth))) _ ?_)
    · intro ok
      exact emits_weaken words _ _ _ _ _ (emits_pure words (some ok) _)
        (fun _ h => h) (by intro x env _ h; rcases h with ⟨rfl, h⟩; exact h)
    · intro env h
      rw [← guard_value depth full address]
      exact eval_predicate env .ult addr bound _ _ h.1 h.2

theorem emits_expr (registers : List String) (values : Valuation ctx)
    (memories : Memories ctx) (words : ModelMemories ctx)
    (models : ∀ name width depth found,
      MemModelProof.Agrees ⟨depth, width, 0, 0⟩ (words name width depth found)
        (memories name width depth found)) (e : Typed.Expr ctx ty) (legal : Legal e)
    (dest : Option String) :
    Emits words (Lower.expr registers e dest) (fun env => ExpressionInputs registers values env e)
      (fun name env => env name = some (coreValue ty (evalExpr values memories e))) := by
  induction e generalizing dest with
  | ref p node found =>
    exact emits_weaken words _ _ _ _ _ (emits_named words dest _ _)
      (fun _ h => h) (by intro x env _ h; rcases h with ⟨rfl, h⟩; exact h)
  | clock p name found =>
    exact emits_weaken words _ _ _ _ _ (emits_pure words name _)
      (fun _ h => h) (by intro x env _ h; rcases h with ⟨rfl, h⟩; exact h)
  | const p w v => exact emits_emit words dest _ _ _ (fun env _ => eval_constant env w v legal)
  | un p op a ih =>
    cases op
    apply emits_bind words _ _ _ _ _ (ih legal none)
    intro aName
    apply emits_bind words _ _ _ _ _
      (emits_keep words _ _ _ (emits_emit words none _ _ _
        (fun env _ => eval_constant env _ _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide)))))
    intro ones
    exact emits_emit words dest _ _ _ (fun env h => eval_not env _ _ _ h.1 h.2)
  | bin p op ordinary a b ia ib =>
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ia legal.1 none) (fun _ h => h.1)
        (fun _ _ _ h => h)))
    intro aName
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ib legal.2 none) (fun _ h => h.1.2)
        (fun _ _ _ h => h)))
    intro bName
    exact emits_emit words dest _ _ _
      (fun env h => eval_binary env op ordinary _ _ _ _ h.1.2 h.2)
  | concat p a b bound ia ib =>
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ia legal.1 none) (fun _ h => h.1)
        (fun _ _ _ h => h)))
    intro aName
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ib legal.2 none) (fun _ h => h.1.2)
        (fun _ _ _ h => h)))
    intro bName
    exact emits_emit words dest _ _ _ (fun env h => eval_concat env _ _ _ _ h.1.2 h.2)
  | icmp p pred a b ia ib =>
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ia legal.1 none) (fun _ h => h.1)
        (fun _ _ _ h => h)))
    intro aName
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ib legal.2 none) (fun _ h => h.1.2)
        (fun _ _ _ h => h)))
    intro bName
    exact emits_emit words dest _ _ _ (fun env h => eval_predicate env pred _ _ _ _ h.1.2 h.2)
  | mux p c a b ic ia ib =>
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ic legal.1 none) (fun _ h => h.1)
        (fun _ _ _ h => h)))
    intro cName
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ia legal.2.1 none) (fun _ h => h.1.2.1)
        (fun _ _ _ h => h)))
    intro aName
    apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
      (emits_weaken words _ _ _ _ _ (ib legal.2.2 none) (fun _ h => h.1.1.2.2)
        (fun _ _ _ h => h)))
    intro bName
    exact emits_emit words dest _ _ _ (fun env h => eval_mux env _ _ _ _ _ _ h.1.1.2 h.1.2 h.2)
  | extract p a lo count bound ih =>
    apply emits_bind words _ _ _ _ _ (ih legal none)
    intro name
    exact emits_emit words dest _ _ _ (fun env h => eval_extract env _ _ lo count h bound)
  | replicate p a count bound ih =>
    apply emits_bind words _ _ _ _ _ (ih legal.1 none)
    intro name
    exact emits_emit words dest _ _ _ (fun env h => eval_replicate env _ _ count h legal.2)
  | @read width depth p name found addr ih =>
    intro s
    let index := (s.readCounts.lookup name).getD 0
    let reserved := { s with readCounts := (name, index + 1) :: s.readCounts }
    have address := ih legal none
    have rest : Emits words (do
        let a ← Lower.expr registers addr none
        modify fun s => { s with reads := ⟨name, index, a⟩ :: s.reads }
        match ← Lower.inRange depth a with
        | none => Lower.named dest s!"{name}.r{index}_data"
        | some ok => do
          let zero ← Lower.emit none (.constant width 0)
          Lower.emit dest (.mux ok s!"{name}.r{index}_data" zero (.int width)))
        (fun env => ExpressionInputs registers values env addr)
        (fun result env => env result = some (coreValue _
          (evalExpr values memories (.read p name found addr)))) := by
      apply emits_bind words _ _ _ _ _ address
      intro a
      apply emits_bind words _ _ _ _ _ (emits_read words name index _ _ found a _)
      intro unused
      apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
        (emits_weaken words _ _ _ _ _ (emits_inRange words _ a _) (fun _ h => h.1)
          (fun _ _ _ h => h)))
      intro guard
      cases guard with
      | none =>
        apply emits_weaken words _ _ _ _ _ (emits_named words dest _ _)
          (fun _ h => h)
        intro result env _ h
        rcases h with ⟨rfl, h⟩
        dsimp only [coreValue, evalExpr]
        rw [← full_depth_read _ _ _ (models name _ _ found) h.2]
        exact h.1.2
      | some ok =>
        apply emits_bind words _ _ _ _ _ (emits_keep words _ _ _
          (emits_emit words none _ _ _ (fun env _ => eval_constant env _ 0 (Nat.two_pow_pos _))))
        intro zero
        apply emits_emit words dest _ _ _
        intro env h
        have ev := eval_mux env ok s!"{name}.r{index}_data" zero _ _ _ h.1.2 h.1.1.2 h.2
        have gr := guarded_read _ _ _ (models name _ _ found) (evalExpr values memories addr)
        dsimp only [coreValue, evalExpr]
        rw [← gr]
        by_cases inside : (evalExpr values memories addr).toNat < depth
        · simpa [evalMux, inside] using ev
        · simpa [evalMux, inside] using ev
    obtain ⟨image, shape, hi⟩ := rest reserved
    refine ⟨image, shape, fun env agree hp => ?_⟩
    have h := hi env agree hp
    exact ⟨frame_trans words env s reserved _
      ⟨⟨[], by simp [reserved], by simp⟩, fun _ hr => Or.inl hr⟩ h.1, h.2⟩

def PositiveKind : Typed.Kind → Prop
  | .value (.bits width) | .memory width _ => 0 < width
  | _ => True

theorem context_positive (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (node : Deps.Node) (kind : Typed.Kind)
    (found : m.ctx.lookup node = some kind) : PositiveKind kind := by
  have numbers := d.wellFormed.2.2.2.1
  have mn := numbers (.module m.erase) (d.design.environments m hm).2.2
  rw [d.design.module_context m hm] at found
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (node, kind) ∈ Typed.context d.design.erase m.erase := by
    rw [he]
    simp
  simp only [Typed.context, Typed.contextFromPorts, List.mem_append] at member
  rcases member with hp | hs
  · obtain ⟨p, hp, eq⟩ := List.mem_map.mp hp
    have pn := mn.1 p hp
    split at eq
    · cases eq; trivial
    · cases eq
      cases ht : p.ty with
      | clock => trivial
      | bits w => exact (ht ▸ pn).1
  · obtain ⟨stmt, hs, eq⟩ := List.mem_flatMap.mp hs
    have sn := (mn.2 stmt hs).1
    cases stmt <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at eq
    case let_ p n w e => cases eq; exact sn.1
    case reg p n w c r => cases eq; exact sn.1
    case mem p n w depth c => cases eq; exact sn.1.1
    case inst p n child inputs =>
      obtain ⟨port, hp, eq⟩ := List.mem_filterMap.mp eq
      split at eq <;> try contradiction
      cases eq
      unfold Typed.portsOf at hp
      cases hi : d.design.erase.items.find? (fun i => i.name == child) with
      | none => simp [hi] at hp
      | some item =>
        have ip := (numbers item (List.mem_of_find?_eq_some hi)).1 port (by simpa [hi] using hp)
        cases ht : port.ty with
        | clock => trivial
        | bits w => exact (ht ▸ ip).1
    all_goals cases eq

theorem expression_legal (ctx : Typed.Ctx)
    (positive : ∀ node kind, ctx.lookup node = some kind → PositiveKind kind)
    (e : Typed.Expr ctx ty)
    (numbers : ∀ node ∈ Rules.exprNodes e.erase, Rules.DeclaredNode node) :
    Legal e ∧ (match ty with | .bits width => 0 < width | .clock => True) := by
  induction e with
  | ref p node found => exact ⟨trivial, positive node _ found⟩
  | clock => exact ⟨trivial, trivial⟩
  | const p w v =>
    have h := numbers _ (List.mem_singleton_self _)
    exact ⟨h.2, h.1.1⟩
  | un p op a ih =>
    have h := ih (fun node hn => numbers node (List.mem_cons_of_mem _ hn))
    exact h
  | bin p op ordinary a b ia ib =>
    have ha := ia (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
    have hb := ib (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_right _ hn)))
    exact ⟨⟨ha.1, hb.1⟩, ha.2⟩
  | concat p a b bound ia ib =>
    have ha := ia (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
    have hb := ib (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_right _ hn)))
    exact ⟨⟨ha.1, hb.1⟩, by have h := ha.2; dsimp at h ⊢; omega⟩
  | icmp p pred a b ia ib =>
    have ha := ia (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
    have hb := ib (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_right _ hn)))
    exact ⟨⟨ha.1, hb.1⟩, Nat.zero_lt_succ 0⟩
  | mux p c a b ic ia ib =>
    have hc := ic (fun node hn => numbers node (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_left _ hn))))
    have ha := ia (fun node hn => numbers node (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ hn))))
    have hb := ib (fun node hn => numbers node
      (List.mem_cons_of_mem _ (List.mem_append_right _ hn)))
    exact ⟨⟨hc.1, ha.1, hb.1⟩, ha.2⟩
  | extract p a lo count bound ih =>
    have h := ih (fun node hn => numbers node (List.mem_cons_of_mem _ hn))
    exact ⟨h.1, numbers _ (List.mem_cons_self ..)⟩
  | replicate p a count bound ih =>
    have h := ih (fun node hn => numbers node (List.mem_cons_of_mem _ hn))
    have countPos : 0 < count := numbers _ (List.mem_cons_self ..)
    exact ⟨⟨h.1, h.2⟩, Nat.mul_pos h.2 countPos⟩
  | read p name found addr ih =>
    have h := ih (fun node hn => numbers node (List.mem_cons_of_mem _ hn))
    exact ⟨h.1, positive _ _ found⟩

end Silicon.Core.LowerProof
