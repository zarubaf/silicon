import Silicon.Core.Proof.Lower.Growth

/-!
Operand typing refers to the final module, so it uses the final op list and alias map.
A build step proves the typing of each new op when its operand names have their types.
-/
namespace Silicon.Core.LowerProof

/-- `Has x ty` states that `x` names a definition of type `ty` in the final module. -/
structure Typing (ctx : Typed.Ctx) where
  registers : List String
  final : Lower.State
  rename : String → String
  Has : String → Mlir.Ty → Prop
  defined : ∀ names op, (names, op) ∈ final.body.toList →
    ∀ pair ∈ names.zip op.resultTypes, rename pair.1 = pair.1 → Has pair.1 pair.2
  temps : ∀ i : Nat, rename (toString i) = (toString i)
  reads : ∀ r ∈ final.reads, ∀ w depth,
    ctx.lookup (.name r.memory) = some (.memory w depth) → Has (readName r) (.int w)
  refs : ∀ node w, ctx.lookup node = some (.value (.bits w)) →
    Has (Lower.valueName registers node) (.int w)
  clocks : ∀ name, ctx.lookup (.name name) = some .clock → Has name .clock

variable {ctx : Typed.Ctx} (E : Typing ctx)

def Typing.Good (entry : List String × Mlir.Op) : Prop :=
  entry.1.length = entry.2.resultTypes.length ∧ entry.2.Valid ∧
    ∀ o ∈ entry.2.operands, E.Has o.1 o.2

def Typing.GoodRead (r : Lower.ReadPort) : Prop :=
  ∃ w depth, ctx.lookup (.name r.memory) = some (.memory w depth) ∧
    E.Has r.addr (.int (Typed.addressWidth depth))

def Typing.GoodWrite (w : Lower.WritePort) : Prop :=
  ∃ width depth, ctx.lookup (.name w.memory) = some (.memory width depth) ∧
    E.Has w.addr (.int (Typed.addressWidth depth)) ∧ E.Has w.data (.int width) ∧
    E.Has w.enable (.int 1)

def Typing.GoodNext (next : String × String) : Prop :=
  ∃ width, Typed.valueTy ctx next.1 = some (.bits width) ∧ E.Has next.2 (.int width)

def Typing.GoodReset (reset : String × Option (String × String)) : Prop :=
  ∃ width, ctx.lookup (.name reset.1) = some (.value (.bits width)) ∧
    ∀ pair ∈ reset.2.toList, E.Has pair.1 (.int 1) ∧ E.Has pair.2 (.int width)

def Typing.NewGood (s t : Lower.State) : Prop :=
  (∀ entry ∈ t.body.toList, entry ∈ s.body.toList ∨ E.Good entry) ∧
  (∀ r ∈ t.reads, r ∈ s.reads ∨ E.GoodRead r) ∧
  (∀ w ∈ t.writes, w ∈ s.writes ∨ E.GoodWrite w) ∧
  (∀ n ∈ t.nexts, n ∈ s.nexts ∨ E.GoodNext n) ∧
  (∀ r ∈ t.resets, r ∈ s.resets ∨ E.GoodReset r)

theorem Typing.newGood_refl (s : Lower.State) : E.NewGood s s :=
  ⟨fun _ h => Or.inl h, fun _ h => Or.inl h, fun _ h => Or.inl h, fun _ h => Or.inl h,
    fun _ h => Or.inl h⟩

private theorem or_chain {P : α → Prop} {xs ys zs : List α}
    (ab : ∀ x ∈ ys, x ∈ xs ∨ P x) (bc : ∀ x ∈ zs, x ∈ ys ∨ P x) : ∀ x ∈ zs, x ∈ xs ∨ P x := by
  intro x h
  rcases bc x h with h | h
  · exact ab x h
  · exact Or.inr h

theorem Typing.newGood_trans {a b c : Lower.State} (ab : E.NewGood a b) (bc : E.NewGood b c) :
    E.NewGood a c :=
  ⟨or_chain ab.1 bc.1, or_chain ab.2.1 bc.2.1, or_chain ab.2.2.1 bc.2.2.1,
    or_chain ab.2.2.2.1 bc.2.2.2.1, or_chain ab.2.2.2.2 bc.2.2.2.2⟩

theorem Typing.newGood_same {s t : Lower.State} (body : t.body = s.body) (reads : t.reads = s.reads)
    (writes : t.writes = s.writes) (nexts : t.nexts = s.nexts) (resets : t.resets = s.resets) :
    E.NewGood s t :=
  ⟨fun _ h => Or.inl (body ▸ h), fun _ h => Or.inl (reads ▸ h), fun _ h => Or.inl (writes ▸ h),
    fun _ h => Or.inl (nexts ▸ h), fun _ h => Or.inl (resets ▸ h)⟩

/-- A typed build step: it grows the state, and with its precondition its new ops type. -/
def Typing.Step (action : Lower.Build α) (pre : Prop) (post : α → Prop) : Prop :=
  ∀ s, Grows s (action s).2 ∧
    (Grows (action s).2 E.final → pre → E.NewGood s (action s).2 ∧ post (action s).1)

theorem Typing.step_bind (a : Lower.Build α) (b : α → Lower.Build β) (p : Prop)
    (q : α → Prop) (r : β → Prop) (ha : E.Step a p q) (hb : ∀ x, E.Step (b x) (q x) r) :
    E.Step (a >>= b) p r := by
  intro s
  obtain ⟨ga, ta⟩ := ha s
  obtain ⟨gb, tb⟩ := hb (a s).1 (a s).2
  refine ⟨ga.trans gb, fun grows hp => ?_⟩
  have first := ta (gb.trans grows) hp
  have second := tb grows first.2
  exact ⟨E.newGood_trans first.1 second.1, second.2⟩

theorem Typing.step_weaken (a : Lower.Build α) (p p' : Prop) (q q' : α → Prop)
    (h : E.Step a p q) (hp : p' → p) (hq : ∀ x, p' → q x → q' x) : E.Step a p' q' := by
  intro s
  obtain ⟨g, t⟩ := h s
  exact ⟨g, fun grows pre => ⟨(t grows (hp pre)).1, hq _ pre (t grows (hp pre)).2⟩⟩

theorem Typing.step_keep (a : Lower.Build α) (p : Prop) (q : α → Prop) (h : E.Step a p q) :
    E.Step a p (fun x => p ∧ q x) :=
  E.step_weaken a p p q _ h id (fun _ hp hq => ⟨hp, hq⟩)

theorem Typing.step_pure (x : α) (p : Prop) : E.Step (pure x) p (fun y => y = x ∧ p) :=
  fun s => ⟨Grows.refl s, fun _ hp => ⟨E.newGood_refl s, rfl, hp⟩⟩

theorem Typing.step_emit (dest : Option String) (op : Mlir.Op) (ty : Mlir.Ty)
    (result : op.resultTypes = [ty]) (p : Prop)
    (good : p → op.Valid ∧ ∀ o ∈ op.operands, E.Has o.1 o.2)
    (fresh : p → ∀ name, dest = some name → E.rename name = name) :
    E.Step (Lower.emit dest op) p (fun name => E.Has name ty) := by
  intro s
  refine ⟨grows_emit dest op s, fun grows hp => ?_⟩
  have body := emit_body dest op s
  refine ⟨⟨fun entry h => ?_, fun r h => ?_, fun r h => ?_, fun r h => ?_, fun r h => ?_⟩, ?_⟩
  · rw [body] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · cases List.mem_singleton.mp h
      exact Or.inr ⟨by simp [result], (good hp).1, (good hp).2⟩
  all_goals try (left; cases dest <;> exact h)
  · rw [emit_result]
    have member : ([dest.getD (toString s.nextTemp)], op) ∈ E.final.body.toList := by
      apply grows.body.subset
      rw [body]
      simp
    apply E.defined _ op member (dest.getD (toString s.nextTemp), ty) (by simp [result])
    cases dest with
    | none => exact E.temps _
    | some name => exact fresh hp name rfl

theorem Typing.step_named (dest : Option String) (value : String) (p : Prop) :
    E.Step (Lower.named dest value) p (fun name => name = value ∧ p) := by
  intro s
  refine ⟨grows_named dest value s, fun _ hp => ⟨?_, named_result dest value s, hp⟩⟩
  cases dest <;> exact E.newGood_refl s

theorem Typing.step_inRange (depth : Nat) (addr : String) :
    E.Step (Lower.inRange depth addr) (E.Has addr (.int (Typed.addressWidth depth)))
      (fun result => match result with
        | none => depth = 2 ^ Typed.addressWidth depth
        | some ok => E.Has ok (.int 1)) := by
  unfold Lower.inRange
  by_cases full : depth = 2 ^ Typed.addressWidth depth
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = true from beq_iff_eq.mpr full,
      ↓reduceIte]
    exact E.step_weaken _ _ _ _ _ (E.step_pure none _) id (fun _ _ h => h.1 ▸ full)
  · simp only [show (depth == 2 ^ Typed.addressWidth depth) = false from by simp [full],
      Bool.false_eq_true, ↓reduceIte]
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_emit none
      (.constant (Typed.addressWidth depth) depth) _ rfl _
      (fun _ => ⟨guard_bound depth full, by simp [Mlir.Op.operands]⟩)
      (fun _ _ h => nomatch h)))
    intro bound
    apply E.step_bind _ _ _ _ _ (E.step_emit none
      (.icmp .ult addr bound (Typed.addressWidth depth)) (.int 1) rfl _
      (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1, h.2⟩⟩) (fun _ _ h => nomatch h))
    intro ok
    exact E.step_weaken _ _ _ _ _ (E.step_pure (some ok) _) id
      (fun _ _ h => by rcases h with ⟨rfl, h⟩; exact h)

/-- The final module gives a type to each leaf of an expression. -/
def NotAliased : Typed.Expr ctx ty → Prop
  | .ref .. => False
  | .read (depth := depth) .. => depth ≠ 2 ^ Typed.addressWidth depth
  | _ => True

theorem Typing.step_expr (e : Typed.Expr ctx ty) (legal : Legal e) (dest : Option String)
    (fresh : ∀ name, dest = some name → NotAliased e → E.rename name = name) :
    E.Step (Lower.expr E.registers e dest) True (fun name => E.Has name (Lower.type ty)) := by
  induction e generalizing dest with
  | ref p node found =>
    exact E.step_weaken _ _ _ _ _ (E.step_named dest _ True) id
      (fun _ _ h => h.1 ▸ E.refs node _ found)
  | clock p name found =>
    exact E.step_weaken _ _ _ _ _ (E.step_pure name True) id
      (fun _ _ h => h.1 ▸ E.clocks name found)
  | const p w v =>
    exact E.step_emit dest _ _ rfl _ (fun _ => ⟨legal, by simp [Mlir.Op.operands]⟩)
      (fun _ name h => fresh name h trivial)
  | un p op a ih =>
    cases op
    apply E.step_bind _ _ _ _ _ (ih legal none (fun _ h => nomatch h))
    intro aName
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_emit none _ _ rfl _
      (fun _ => ⟨Nat.sub_lt (Nat.two_pow_pos _) (by decide), by simp [Mlir.Op.operands]⟩)
      (fun _ _ h => nomatch h)))
    intro ones
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1, h.2⟩⟩)
      (fun _ name h => fresh name h trivial)
  | bin p op ordinary a b ia ib =>
    apply E.step_bind _ _ _ _ _ (ia legal.1 none (fun _ h => nomatch h))
    intro aName
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (ib legal.2 none (fun _ h => nomatch h)) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1, h.2⟩⟩)
      (fun _ name h => fresh name h trivial)
  | concat p a b bound ia ib =>
    apply E.step_bind _ _ _ _ _ (ia legal.1 none (fun _ h => nomatch h))
    intro aName
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (ib legal.2 none (fun _ h => nomatch h)) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1, h.2⟩⟩)
      (fun _ name h => fresh name h trivial)
  | icmp p pred a b ia ib =>
    apply E.step_bind _ _ _ _ _ (ia legal.1 none (fun _ h => nomatch h))
    intro aName
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (ib legal.2 none (fun _ h => nomatch h)) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1, h.2⟩⟩)
      (fun _ name h => fresh name h trivial)
  | mux p c a b ic ia ib =>
    apply E.step_bind _ _ _ _ _ (ic legal.1 none (fun _ h => nomatch h))
    intro cName
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (ia legal.2.1 none (fun _ h => nomatch h)) (fun _ => trivial) (fun _ _ h => h)))
    intro aName
    apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_weaken _ _ _ _ _
      (ib legal.2.2 none (fun _ h => nomatch h)) (fun _ => trivial) (fun _ _ h => h)))
    intro bName
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1.1, h.1.2, h.2⟩⟩)
      (fun _ name h => fresh name h trivial)
  | extract p a lo count bound ih =>
    apply E.step_bind _ _ _ _ _ (ih legal none (fun _ h => nomatch h))
    intro aName
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨bound, by simp [Mlir.Op.operands]; exact h⟩)
      (fun _ name h => fresh name h trivial)
  | replicate p a count bound ih =>
    apply E.step_bind _ _ _ _ _ (ih legal.1 none (fun _ h => nomatch h))
    intro aName
    exact E.step_emit dest _ _ rfl _
      (fun h => ⟨⟨by rw [Nat.mul_div_cancel_left count legal.2], legal.2⟩,
        by simp [Mlir.Op.operands]; exact h⟩)
      (fun _ name h => fresh name h trivial)
  | @read width depth p name found addr ih =>
    intro s
    have walk := ih legal none (fun _ h => nomatch h) (reserve s name)
    cases hw : Lower.expr E.registers addr none (reserve s name) with
    | mk a walked =>
    rw [hw] at walk
    let index := (s.readCounts.lookup name).getD 0
    have guardStep := E.step_inRange depth a (record walked ⟨name, index, a⟩)
    cases hg : Lower.inRange depth a (record walked ⟨name, index, a⟩) with
    | mk guard state =>
    rw [hg] at guardStep
    rw [read_eq E.registers p name found addr dest s a walked hw guard state hg]
    have before : Grows s state :=
      (((grows_reserve s _).trans walk.1).trans (grows_record _ _)).trans guardStep.1
    have data (grows : Grows state E.final) : E.Has s!"{name}.r{index}_data" (.int width) :=
      E.reads ⟨name, index, a⟩ (grows.reads.subset (guardStep.1.reads.subset
        (List.mem_cons_self ..))) width depth found
    have early (grows : Grows state E.final) : E.NewGood s state ∧ E.Has a
        (.int (Typed.addressWidth depth)) := by
      have w := walk.2 (((grows_record _ _).trans guardStep.1).trans grows) trivial
      have g := guardStep.2 grows w.2
      have recorded : E.NewGood walked (record walked ⟨name, index, a⟩) := by
        refine ⟨fun entry h => Or.inl h, fun r h => ?_, fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun _ h => Or.inl h⟩
        rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨width, depth, found, w.2⟩
        · exact Or.inl h
      have first := E.newGood_trans (E.newGood_same rfl rfl rfl rfl rfl) w.1
      exact ⟨E.newGood_trans (E.newGood_trans first recorded) g.1, w.2⟩
    cases guard with
    | none =>
      obtain ⟨grow, rest⟩ := E.step_named dest s!"{name}.r{index}_data" True state
      refine ⟨before.trans grow, fun grows _ => ?_⟩
      have r := rest grows trivial
      have e := early (grow.trans grows)
      refine ⟨E.newGood_trans e.1 r.1, ?_⟩
      change E.Has (Lower.named dest _ state).1 _
      rw [r.2.1]
      exact data (grow.trans grows)
    | some ok =>
      have short : depth ≠ 2 ^ Typed.addressWidth depth := by
        intro full
        have result := inRange_result depth a (record walked ⟨name, index, a⟩)
        rw [hg] at result
        have e : some ok = none := result.trans (ite_eq_left_of_eq_true _ _ (eq_true full))
        cases e
      have tail : E.Step (readTail dest s!"{name}.r{index}_data" width (some ok))
          (E.Has ok (.int 1) ∧ E.Has s!"{name}.r{index}_data" (.int width))
          (fun result => E.Has result (.int width)) := by
        apply E.step_bind _ _ _ _ _ (E.step_keep _ _ _ (E.step_emit none _ _ rfl _
          (fun _ => ⟨Nat.two_pow_pos _, by simp [Mlir.Op.operands]⟩) (fun _ _ h => nomatch h)))
        intro zero
        exact E.step_emit dest _ _ rfl _
          (fun h => ⟨trivial, by simp [Mlir.Op.operands]; exact ⟨h.1.1, h.1.2, h.2⟩⟩)
          (fun _ n h => fresh n h short)
      obtain ⟨grow, rest⟩ := tail state
      refine ⟨before.trans grow, fun grows _ => ?_⟩
      have e := early (grow.trans grows)
      have g := guardStep.2 (grow.trans grows) e.2
      have r := rest grows ⟨g.2, data (grow.trans grows)⟩
      exact ⟨E.newGood_trans e.1 r.1, r.2⟩

end Silicon.Core.LowerProof
