-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleNext

/-!
The statements of a module give one image of bindings for their new op results, memory read
results, and instance results. An environment that matches the image satisfies every new plain
op and every new memory read. Instance results take values that the caller chooses.
-/
namespace Silicon.Core.LowerProof

open Semantics

variable {ctx : Typed.Ctx}

/-- New plain ops hold and new memory reads hold. Instance ops have no op equation. -/
def StmtFrame (words : ModelMemories ctx) (env : Mlir.Env) (s t : Lower.State) : Prop :=
  (∃ tail, t.body.toList = s.body.toList ++ tail ∧ ∀ names op, (names, op) ∈ tail →
    isInstance op = false → ∃ name value, names = [name] ∧ env name = some value ∧
      op.eval env = some value) ∧
  (∀ r ∈ t.reads, r ∈ s.reads ∨ ReadEquation words env r)

theorem stmtFrame_of (words : ModelMemories ctx) (env : Mlir.Env) (s t : Lower.State)
    (h : EmissionFrame words env s t) : StmtFrame words env s t := by
  obtain ⟨⟨tail, body, ops⟩, reads⟩ := h
  exact ⟨⟨tail, body, fun names op he _ => ops names op he⟩, reads⟩

theorem stmtFrame_refl (words : ModelMemories ctx) (env : Mlir.Env) (s : Lower.State) :
    StmtFrame words env s s :=
  stmtFrame_of words env s s (frame_refl words env s)

theorem stmtFrame_trans (words : ModelMemories ctx) (env : Mlir.Env)
    (a b c : Lower.State) (ab : StmtFrame words env a b)
    (bc : StmtFrame words env b c) : StmtFrame words env a c := by
  obtain ⟨⟨xs, hx, ex⟩, rx⟩ := ab
  obtain ⟨⟨ys, hy, ey⟩, ry⟩ := bc
  refine ⟨⟨xs ++ ys, by simp [hy, hx, List.append_assoc], ?_⟩, ?_⟩
  · intro names op h plain
    rcases List.mem_append.mp h with h | h
    · exact ex names op h plain
    · exact ey names op h plain
  · intro r hr
    rcases ry r hr with hr | hr
    · exact rx r hr
    · exact Or.inr hr

def SEmits (words : ModelMemories ctx) (action : Lower.Build α)
    (pre : Mlir.Env → Prop) (post : α → Mlir.Env → Prop) : Prop :=
  ∀ s, ∃ image : Image, image.Accounts s (action s).2 ∧
    ∀ env, image.Agrees env → pre env →
    StmtFrame words env s (action s).2 ∧ post (action s).1 env

theorem semits_of (words : ModelMemories ctx) (a : Lower.Build α) (p : Mlir.Env → Prop)
    (q : α → Mlir.Env → Prop) (h : Emits words a p q) : SEmits words a p q := by
  intro s
  obtain ⟨image, shape, hi⟩ := h s
  exact ⟨image, shape, fun env agree hp =>
    ⟨stmtFrame_of words env _ _ (hi env agree hp).1, (hi env agree hp).2⟩⟩

theorem semits_pure (words : ModelMemories ctx) (a : α) (p : Mlir.Env → Prop) :
    SEmits words (pure a) p (fun result env => result = a ∧ p env) :=
  semits_of words _ _ _ (emits_pure words a p)

theorem semits_bind (words : ModelMemories ctx) (a : Lower.Build α)
    (b : α → Lower.Build β) (p : Mlir.Env → Prop)
    (q : α → Mlir.Env → Prop) (r : β → Mlir.Env → Prop)
    (ha : SEmits words a p q) (hb : ∀ x, SEmits words (b x) (q x) r) :
    SEmits words (a >>= b) p r := by
  intro s
  obtain ⟨xs, sx, hx⟩ := ha s
  obtain ⟨ys, sy, hy⟩ := hb (a s).1 (a s).2
  refine ⟨xs ++ ys, accounts_trans _ _ _ xs ys sx sy, ?_⟩
  intro env agree hp
  have ax := hx env (fun x h => agree x (List.mem_append_left _ h)) hp
  have by' := hy env (fun x h => agree x (List.mem_append_right _ h)) ax.2
  exact ⟨stmtFrame_trans words env _ _ _ ax.1 by'.1, by'.2⟩

theorem semits_weaken (words : ModelMemories ctx) (a : Lower.Build α)
    (p p' : Mlir.Env → Prop) (q q' : α → Mlir.Env → Prop)
    (h : SEmits words a p q) (hp : ∀ env, p' env → p env)
    (hq : ∀ x env, p' env → q x env → q' x env) : SEmits words a p' q' := by
  intro s
  obtain ⟨image, shape, hi⟩ := h s
  refine ⟨image, shape, fun env agree pre => ?_⟩
  have got := hi env agree (hp env pre)
  exact ⟨got.1, hq _ env pre got.2⟩

theorem semits_keep (words : ModelMemories ctx) (a : Lower.Build α)
    (p : Mlir.Env → Prop) (q : α → Mlir.Env → Prop)
    (h : SEmits words a p q) : SEmits words a p (fun x env => p env ∧ q x env) :=
  semits_weaken words a p p q _ h (fun _ hp => hp) (fun _ _ hp hq => ⟨hp, hq⟩)

/-- A state update that keeps the body, the reads, and the temporaries binds nothing. -/
theorem semits_update (words : ModelMemories ctx) (f : Lower.State → Lower.State)
    (body : ∀ s, (f s).body = s.body) (reads : ∀ s, (f s).reads = s.reads) (p : Mlir.Env → Prop) :
    SEmits words (modify f) p (fun _ env => p env) := by
  intro s
  refine ⟨[], fun name => ?_, fun env _ hp => ⟨⟨⟨[], ?_, by simp⟩, fun r hr => ?_⟩, hp⟩⟩
  · change _ + _ = (allocatedNames (f s)).count name
    simp [allocatedNames, body, reads]
  · change (f s).body.toList = _
    simp [body]
  · change r ∈ (f s).reads at hr
    rw [reads] at hr
    exact Or.inl hr

/-- An instance op binds its result names to values that the caller chooses. -/
theorem semits_instance (words : ModelMemories ctx) (names : List String) (op : Mlir.Op)
    (instanceOp : isInstance op = true) (value : String → Mlir.Value) (p : Mlir.Env → Prop) :
    SEmits words (modify fun s : Lower.State => { s with body := s.body.push (names, op) }) p
      (fun _ env => p env ∧ ∀ n ∈ names, env n = some (value n)) := by
  intro s
  refine ⟨names.map fun n => (n, value n), fun name => ?_, fun env agree hp => ⟨⟨⟨[(names, op)],
    ?_, ?_⟩, fun r hr => Or.inl hr⟩, hp, fun n hn => agree _ (List.mem_map_of_mem hn)⟩⟩
  · change _ + _ = (allocatedNames { s with body := s.body.push (names, op) }).count name
    simp [allocatedNames, List.count_append, List.map_map, Function.comp_def]
    omega
  · change (s.body.push _).toList = _
    rw [Array.toList_push]
  · intro names' op' he plain
    cases List.mem_singleton.mp he
    rw [instanceOp] at plain
    cases plain

/-- Agreement at every source value and clock. -/
def GlobalInputs (registers : List String) (values : Valuation ctx) (env : Mlir.Env) : Prop :=
  (∀ node w found, env (Lower.valueName registers node) = some (.bits w (values node w found))) ∧
  (∀ name, ctx.lookup (.name name) = some .clock → env name = some .clock)

theorem expressionInputs_of_global (registers : List String) (values : Valuation ctx)
    (env : Mlir.Env) (global : GlobalInputs registers values env) (e : Typed.Expr ctx ty) :
    ExpressionInputs registers values env e := by
  induction e with
  | ref p node found => exact global.1 node _ found
  | clock p name found => exact global.2 name found
  | const => trivial
  | un p op a ih => exact ih
  | bin p op ordinary a b ia ib => exact ⟨ia, ib⟩
  | concat p a b bound ia ib => exact ⟨ia, ib⟩
  | icmp p pred a b ia ib => exact ⟨ia, ib⟩
  | mux p c a b ic ia ib => exact ⟨ic, ia, ib⟩
  | extract p a lo count bound ih => exact ih
  | replicate p a count bound ih => exact ih
  | read p name found addr ih => exact ih

section
variable {ports : String → List Port} (registers : List String) (values : Valuation ctx)
  (memories : Memories ctx) (words : ModelMemories ctx)
  (models : ∀ name width depth found,
    MemModelProof.Agrees ⟨depth, width, 0, 0⟩ (words name width depth found)
      (memories name width depth found))

include models in
theorem semits_expr (e : Typed.Expr ctx ty) (legal : Legal e) (dest : Option String) :
    SEmits words (Lower.expr registers e dest) (GlobalInputs registers values)
      (fun name env => env name = some (coreValue ty (evalExpr values memories e))) :=
  semits_weaken words _ _ _ _ _
    (semits_of words _ _ _ (emits_expr registers values memories words models e legal dest))
    (fun env h => expressionInputs_of_global registers values env h e) (fun _ _ _ h => h)

include models in
theorem semits_args {child : String}
    (xs : List ((q : {q : Port // q ∈ ports child}) × Typed.Expr ctx q.val.ty))
    (legal : ∀ i ∈ xs, Legal i.2) : SEmits words (xs.mapM fun input => do
      let value ← Lower.expr registers input.2 none
      return (input.1.val.name, value, Lower.type input.1.val.ty))
      (GlobalInputs registers values) (fun _ env => GlobalInputs registers values env) := by
  revert legal
  induction xs with
  | nil =>
    intro _
    rw [List.mapM_nil]
    exact semits_weaken words _ _ _ _ _ (semits_pure words [] _) (fun _ h => h)
      (fun _ _ _ h => h.2)
  | cons x xs ih =>
    intro legalXs
    rw [List.mapM_cons]
    apply semits_bind words _ _ _ _ _ (semits_bind words _ _ _ _ _ (semits_keep words _ _ _
      (semits_expr registers values memories words models x.2
        (legalXs x (List.mem_cons_self ..)) none))
      (fun v => semits_weaken words _ _ _ _ (fun _ env => GlobalInputs registers values env)
        (semits_pure words (x.1.val.name, v, Lower.type x.1.val.ty) _) (fun _ h => h)
        (fun _ _ _ h => h.2.1)))
    intro y
    apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _ (semits_weaken words _ _ _ _ _
      (ih (fun i hi => legalXs i (List.mem_cons_of_mem _ hi))) (fun _ h => h)
      (fun _ _ _ h => h)))
    intro ys
    exact semits_weaken words _ _ _ _ _ (semits_pure words (y :: ys) _) (fun _ h => h)
      (fun _ _ _ h => h.2.1)

include models in
theorem semits_statement (stmt : Typed.Stmt ctx ports) (legal : StmtLegal stmt)
    (value : String → Mlir.Value) :
    SEmits words (Lower.statement registers stmt) (GlobalInputs registers values)
      (fun _ _ => True) := by
  cases stmt with
  | let_ p name w e | assign p name w target e =>
    simp only [Lower.statement]
    apply semits_bind words _ _ _ _ _ (semits_expr registers values memories words models e legal
      (some name))
    intro _
    exact semits_weaken words _ _ _ _ _ (semits_pure words () _) (fun _ _ => trivial)
      (fun _ _ _ _ => trivial)
  | next p name w target e =>
    simp only [Lower.statement]
    apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _
      (semits_expr registers values memories words models e legal none))
    intro next
    exact semits_weaken words _ _ _ _ _ (semits_update words
      (fun s : Lower.State => { s with nexts := (name, next) :: s.nexts }) (fun _ => rfl)
      (fun _ => rfl) _) (fun _ h => h) (fun _ _ _ _ => trivial)
  | mem =>
    exact semits_weaken words _ _ _ _ _ (semits_pure words () _) (fun _ h => h)
      (fun _ _ _ _ => trivial)
  | reg p name w clk reset =>
    simp only [Lower.statement]
    have values : SEmits words (reset.mapM fun r => do
        let signal ← Lower.expr registers r.signal none
        let value ← Lower.expr registers r.value none
        return (signal, value)) (GlobalInputs registers values)
        (fun _ env => GlobalInputs registers values env) := by
      cases reset with
      | none =>
        rw [Option.mapM_none]
        exact semits_weaken words _ _ _ _ _ (semits_pure words none _) (fun _ h => h)
          (fun _ _ _ h => h.2)
      | some r =>
        have hr := legal r (List.mem_singleton_self r)
        rw [Option.mapM_some, map_eq_pure_bind]
        have inner : SEmits words (do
            let signal ← Lower.expr registers r.signal none
            let value ← Lower.expr registers r.value none
            return (signal, value)) (GlobalInputs registers values)
            (fun _ env => GlobalInputs registers values env) := by
          apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _ (semits_expr registers values
            memories words models r.signal hr.1 none))
          intro signal
          apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _ (semits_weaken words _ _ _ _ _
            (semits_expr registers values memories words models r.value hr.2 none)
            (fun _ h => h.1) (fun _ _ _ h => h)))
          intro value
          exact semits_weaken words _ _ _ _ _ (semits_pure words (signal, value) _) (fun _ h => h)
            (fun _ _ _ h => h.2.1.1)
        apply semits_bind words _ _ _ _ _ inner
        intro pair
        exact semits_weaken words _ _ _ _ _ (semits_pure words (some pair) _) (fun _ h => h)
          (fun _ _ _ h => h.2)
    apply semits_bind words _ _ _ _ _ values
    intro opt
    exact semits_weaken words _ _ _ _ _ (semits_update words
      (fun s : Lower.State => { s with resets := (name, opt) :: s.resets }) (fun _ => rfl)
      (fun _ => rfl) _) (fun _ h => h) (fun _ _ _ _ => trivial)
  | write p name index w depth target addr data enable =>
    simp only [Lower.statement]
    apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _
      (semits_expr registers values memories words models addr legal.1 none))
    intro a
    apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _ (semits_weaken words _ _ _ _ _
      (semits_expr registers values memories words models data legal.2.1 none) (fun _ h => h.1)
      (fun _ _ _ h => h)))
    intro d
    apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _ (semits_weaken words _ _ _ _ _
      (semits_expr registers values memories words models enable legal.2.2 none)
      (fun _ h => h.1.1) (fun _ _ _ h => h)))
    intro en
    apply semits_bind words _ _ _ _ _ (semits_keep words _ _ _ (semits_weaken words _ _ _ _ _
      (semits_of words _ _ _ (emits_inRange words depth a (evalExpr values memories addr)))
      (fun _ h => h.1.1.2) (fun _ _ _ h => h)))
    intro guard
    have finish (enabled : String) (q : Mlir.Env → Prop) :
        SEmits words (modify fun s : Lower.State =>
          { s with writes := ⟨name, index, a, d, enabled⟩ :: s.writes }) q (fun _ _ => True) :=
      semits_weaken words _ _ _ _ _ (semits_update words (fun s : Lower.State =>
        { s with writes := ⟨name, index, a, d, enabled⟩ :: s.writes }) (fun _ => rfl)
        (fun _ => rfl) q) (fun _ h => h) (fun _ _ _ _ => trivial)
    cases guard with
    | none =>
      apply semits_bind words _ _ _ _ _ (semits_pure words en _)
      intro enabled
      exact finish enabled _
    | some ok =>
      apply semits_bind words _ _ _ _ _ (semits_of words _ _ _ (emits_emit words none
        (.comb .and en ok 1) (.bits 1 (evalExpr values memories enable &&&
          BitVec.ofBool ((evalExpr values memories addr).toNat < depth))) _
        (fun env h => eval_binary env .and (by decide) en ok _ _ h.1.2 h.2)))
      intro enabled
      exact finish enabled _
  | inst p name child inputs =>
    simp only [Lower.statement]
    apply semits_bind words _ _ _ _ _ (semits_args registers values memories words models inputs
      legal)
    intro args
    exact semits_weaken words _ _ _ _ _ (semits_instance words _ _ rfl value _) (fun _ h => h)
      (fun _ _ _ _ => trivial)

/-- A named statement emits its own name with the core value of its expression. -/
def LetPost : Typed.Stmt ctx ports → Lower.State → Mlir.Env → Prop
  | .let_ _ x _ e, s, env | .assign _ x _ _ e, s, env =>
    ExpressionInputs registers values env e →
      env (Lower.expr registers e (some x) s).1 = some (coreValue _ (evalExpr values memories e))
  | _, _, _ => True

/-- The result bindings of an instance statement. -/
def instBindings (value : String → Mlir.Value) : Typed.Stmt ctx ports → Image
  | .inst _ n child _ => (instResults ports child).map fun q =>
      (s!"{n}.{q.1}", value s!"{n}.{q.1}")
  | _ => []

include models in
theorem image_statement (stmt : Typed.Stmt ctx ports) (legal : StmtLegal stmt)
    (value : String → Mlir.Value) (s : Lower.State) :
    ∃ image : Image, image.Accounts s (Lower.statement registers stmt s).2 ∧
      (∀ env, image.Agrees env → GlobalInputs registers values env →
        StmtFrame words env s (Lower.statement registers stmt s).2) ∧
      (∀ env, image.Agrees env → LetPost registers values memories stmt s env) ∧
      ∀ b ∈ instBindings value stmt, b ∈ image := by
  have generic : (∀ env, LetPost registers values memories stmt s env) →
      instBindings value stmt = [] →
      ∃ image : Image, image.Accounts s (Lower.statement registers stmt s).2 ∧
        (∀ env, image.Agrees env → GlobalInputs registers values env →
          StmtFrame words env s (Lower.statement registers stmt s).2) ∧
        (∀ env, image.Agrees env → LetPost registers values memories stmt s env) ∧
        ∀ b ∈ instBindings value stmt, b ∈ image := by
    intro post empty
    obtain ⟨image, shape, frame⟩ := semits_statement registers values memories words models stmt
      legal value s
    refine ⟨image, shape, fun env agree hp => (frame env agree hp).1, fun env _ => post env, ?_⟩
    rw [empty]
    intro b hb
    cases hb
  cases stmt with
  | let_ p x w e | assign p x w target e =>
    obtain ⟨image, shape, emitted⟩ := emits_expr registers values memories words models e legal
      (some x) s
    exact ⟨image, shape, fun env agree hp => stmtFrame_of words env _ _
      (emitted env agree (expressionInputs_of_global registers values env hp e)).1,
      fun env agree inputs => (emitted env agree inputs).2, fun b hb => nomatch hb⟩
  | inst p n child inputs =>
    obtain ⟨xs, sx, hx⟩ := semits_args registers values memories words models inputs legal s
    let s₁ := (inputs.mapM (inputArgument registers) s).2
    let args := (inputs.mapM (inputArgument registers) s).1
    let names := (instResults ports child).map fun q => s!"{n}.{q.1}"
    let op : Mlir.Op := .instance n child (instArgs ports child args) (instResults ports child)
    let t := { s₁ with body := s₁.body.push (names, op) }
    have hstate : (Lower.statement registers (.inst p n child inputs) s).2 = t := rfl
    have sy : Image.Accounts (names.map fun q => (q, value q)) s₁ t := by
      intro name
      change _ + _ = (allocatedNames t).count name
      simp [t, allocatedNames, List.count_append, List.map_map, Function.comp_def]
      omega
    have fy : ∀ env, StmtFrame words env s₁ t := by
      intro env
      refine ⟨⟨[(names, op)], ?_, ?_⟩, fun r hr => Or.inl hr⟩
      · change (s₁.body.push _).toList = _
        rw [Array.toList_push]
      · intro names' op' he plain
        cases List.mem_singleton.mp he
        cases plain
    rw [hstate]
    refine ⟨xs ++ names.map fun q => (q, value q), accounts_trans _ _ _ _ _ sx sy,
      fun env agree hp => stmtFrame_trans words env _ _ _
        (hx env (fun b h => agree b (List.mem_append_left _ h)) hp).1 (fy env),
      fun _ _ => trivial, fun b hb => List.mem_append_right _ ?_⟩
    simpa [instBindings, names, List.map_map, Function.comp_def] using hb
  | _ => exact generic (fun _ => trivial) rfl

include models in
theorem image_statements (stmts : List (Typed.Stmt ctx ports))
    (legal : ∀ x ∈ stmts, StmtLegal x) (value : String → Mlir.Value) (s : Lower.State) :
    let t := ((do for stmt in stmts do Lower.statement registers stmt) s).2
    ∃ image : Image, image.Accounts s t ∧
      (∀ env, image.Agrees env → GlobalInputs registers values env → StmtFrame words env s t) ∧
      (∀ stmt ∈ stmts, ∃ s₀, Grows (Lower.statement registers stmt s₀).2 t ∧
        ∀ env, image.Agrees env → LetPost registers values memories stmt s₀ env) ∧
      ∀ stmt ∈ stmts, ∀ b ∈ instBindings value stmt, b ∈ image := by
  induction stmts generalizing s with
  | nil =>
    intro t
    rw [show t = s from run_nil registers s]
    exact ⟨[], accounts_refl s, fun env _ _ => stmtFrame_refl words env s,
      (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | cons stmt rest ih =>
    intro t
    rw [show t = _ from run_cons registers stmt rest s]
    obtain ⟨xs, sx, fx, px, ix⟩ := image_statement registers values memories words models stmt
      (legal stmt (List.mem_cons_self ..)) value s
    obtain ⟨ys, sy, fy, py, iy⟩ := ih (fun x hx => legal x (List.mem_cons_of_mem _ hx))
      (Lower.statement registers stmt s).2
    refine ⟨xs ++ ys, accounts_trans _ _ _ xs ys sx sy, fun env agree hp => ?_, ⟨?_, ?_⟩⟩
    · exact stmtFrame_trans words env _ _ _
        (fx env (fun b h => agree b (List.mem_append_left _ h)) hp)
        (fy env (fun b h => agree b (List.mem_append_right _ h)) hp)
    · intro st hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨s, grows_statements registers rest _,
          fun env agree => px env (fun b h => agree b (List.mem_append_left _ h))⟩
      · obtain ⟨s₀, grows, post⟩ := py st hs
        exact ⟨s₀, grows, fun env agree =>
          post env (fun b h => agree b (List.mem_append_right _ h))⟩
    · intro st hs b hb
      rcases List.mem_cons.mp hs with rfl | hs
      · exact List.mem_append_left _ (ix b hb)
      · exact List.mem_append_right _ (iy st hs b hb)

end

end Silicon.Core.LowerProof
