import Silicon.Core.Proof.Lower.InstanceArgs
import Silicon.Core.Proof.Lower.CoreChild

/-!
An MLIR solution, read back at the names of the core nodes, satisfies the core equations.
Core solution uniqueness then fixes it. The proof needs no order on MLIR names.
-/
namespace Silicon.Core.LowerProof

open Semantics

theorem coreValue_cast {ty : Ty} {w : Nat} (hb : ty = .bits w) (x : TyValue ty) :
    coreValue ty x = .bits w (cast (congrArg TyValue hb) x) := by
  subst hb
  rfl

def readBack (m : Typed.Module) (V : Mlir.Env) : Valuation m.ctx :=
  fun node w _ =>
    ((V (rename m (Lower.valueName (Lower.registers m) node))) >>= Mlir.Value.asBits w).getD 0

theorem readBack_eq (m : Typed.Module) (V : Mlir.Env) (node : Deps.Node) (w : Nat) (found)
    (x : BitVec w)
    (hx : V (rename m (Lower.valueName (Lower.registers m) node)) = some (.bits w x)) :
    readBack m V node w found = x := by
  simp [readBack, hx, Mlir.Value.asBits]

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)

include h hm in
theorem read_refs {d : Mlir.Design} {state inputs V : Mlir.Env} {children : String → Mlir.Env}
    (hv : Mlir.LocalSolution d (Lower.module m).1 state inputs V children) (node : Deps.Node)
    (w : Nat) (found : m.ctx.lookup node = some (.value (.bits w))) :
    (V ∘ rename m) (Lower.valueName (Lower.registers m) node) =
      some (.bits w (readBack m V node w found)) := by
  have has := refs_has raw t h m hm node w found
  obtain ⟨v, hv, ty⟩ := local_types hv _ _ (mem_of_lookup has)
  obtain ⟨x, rfl⟩ := bits_of_ty ty
  rw [readBack_eq m V node w found x hv]
  exact hv

include h hm in
theorem read_clocks {d : Mlir.Design} {state inputs V : Mlir.Env} {children : String → Mlir.Env}
    (hv : Mlir.LocalSolution d (Lower.module m).1 state inputs V children) (name : String)
    (found : m.ctx.lookup (.name name) = some .clock) :
    (V ∘ rename m) name = some .clock := by
  have has := clocks_has raw t h m hm name found
  obtain ⟨v, hv, ty⟩ := local_types hv _ _ (mem_of_lookup has)
  cases v <;> cases ty
  exact hv

omit h in
theorem register_entry_body (i : Nat) (p : Pos) (n : String) (w : Nat) (clk : String)
    (target) (reset) (ni : Nat) (np : Pos) (next : Typed.Expr m.ctx (.bits w))
    (he : Typed.Equation.reg i p n w clk target reset ni np next ∈ m.body) :
    ∃ nextName, (finalState m).nexts.lookup n = some nextName ∧
      ([s!"silicon_reg_{n}"], Lower.substitute (rename m) (.compreg nextName clk
        (((finalState m).resets.lookup n).getD none) (.int w))) ∈ (Lower.module m).1.body := by
  have hs : Typed.Stmt.next np n w target next ∈ Lower.statements m :=
    (statement_of_eq m _).mpr ⟨_, he, (ni, .next np n w target next), by
      simp [Typed.Equation.parts], rfl⟩
  obtain ⟨s, grows⟩ := presence m _ hs
  have pushed : (n, (Lower.expr (Lower.registers m) next none s).1) ∈
      (Lower.statement (ports := m.interfaces) (Lower.registers m)
        (.next np n w target next) s).2.nexts :=
    List.mem_cons_self ..
  obtain ⟨x, hx⟩ := lookup_some_of_mem (grows.nexts.subset pushed)
  refine ⟨x, hx, ?_⟩
  rw [module_body]
  apply List.mem_map.mpr
  refine ⟨([s!"silicon_reg_{n}"], .compreg x clk
    (((finalState m).resets.lookup n).getD none) (.int w)),
    List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, he, ?_⟩), rfl⟩
  simp only [hx]
  rfl

variable (env : Env (certified raw t h).design)

/-- Model words of each memory, chosen from a corresponding MLIR state. -/
noncomputable def stateWords (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) : ModelMemories m.ctx :=
  fun name w depth found =>
    (corresponds_memory (certified raw t h) env noExterns m hm s σ corr name w depth found).choose

theorem stateWords_spec (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (name : String)
    (w depth : Nat) (found : m.ctx.lookup (.name name) = some (.memory w depth)) :
    (σ.instance name).regs "silicon_reg_mem" =
      some (.array _ _ (stateWords raw t h noExterns m hm env s σ corr name w depth found)) ∧
    MemModelProof.Agrees ⟨depth, w, 0, 0⟩
      (stateWords raw t h noExterns m hm env s σ corr name w depth found)
      (stateMemories m (designChildren (certified raw t h) env m hm) s name w depth found) :=
  (corresponds_memory (certified raw t h) env noExterns m hm s σ corr name w depth
    found).choose_spec

/-- The meaning of a hierarchy solution at its own level. -/
noncomputable def readMeaning (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (inputs : Mlir.Env)
    (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all) :
    Meaning m.ctx where
  registers := Lower.registers m
  final := finalState m
  env := all [] ∘ rename m
  values := readBack m (all [])
  memories := stateMemories m (designChildren (certified raw t h) env m hm) s
  words := stateWords raw t h noExterns m hm env s σ corr
  models := fun name w depth found =>
    (stateWords_spec raw t h noExterns m hm env s σ corr name w depth found).2
  ops := read_ops raw t h m hm hv.1
  reads := read_reads raw t h noExterns m hm σ inputs all hv _
    (fun name w depth found => (stateWords_spec raw t h noExterns m hm env s σ corr name w
      depth found).1)
  refs := read_refs raw t h m hm hv.1
  clocks := read_clocks raw t h m hm hv.1

theorem statement_of_part (eq : Typed.Equation m.ctx m.interfaces) (he : eq ∈ m.body)
    (part : Nat × Typed.Stmt m.ctx m.interfaces) (hp : part ∈ eq.parts) :
    part.2 ∈ Lower.statements m :=
  (statement_of_eq m _).mpr ⟨eq, he, part, hp, rfl⟩

omit noExterns in
include h hm in
theorem inst_statement_unique (p p' : Pos) (n child : String)
    (conns conns' : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
    (hs : Typed.Stmt.inst p n child conns ∈ Lower.statements m)
    (hs' : Typed.Stmt.inst p' n child conns' ∈ Lower.statements m) : conns = conns' := by
  obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
  obtain ⟨eq', he', part', hp', same'⟩ := (statement_of_eq m _).mp hs'
  cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  all_goals try (rcases hp with rfl | rfl <;> cases same)
  all_goals try (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases same)
  all_goals try (subst hp; cases same)
  cases eq' <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp'
  all_goals try (rcases hp' with rfl | rfl <;> cases same')
  all_goals try (rcases hp' with rfl | ⟨_, _, rfl⟩ <;> cases same')
  all_goals try (subst hp'; cases same')
  have f := find_equation (certified raw t h) m hm _ he
  have f' := find_equation (certified raw t h) m hm _ he'
  simp only [equationName] at f f'
  rw [f] at f'
  cases f'
  rfl

theorem cast_coreValue {ty ty' : Ty} (same : ty = ty') (values : Valuation m.ctx)
    (memories : Memories m.ctx) (e : Typed.Expr m.ctx ty) :
    coreValue ty' (evalExpr values memories (same ▸ e)) =
      coreValue ty (evalExpr values memories e) := by
  subst same
  rfl

omit noExterns in
/-- An instance op passes each child input the core value of its connection, for any
environment that has the meaning of the statements. -/
theorem connection_agree (M : Meaning m.ctx) (hregs : M.registers = Lower.registers m)
    (hfinal : M.final = finalState m) (V : Mlir.Env) (hV : ∀ y, V (rename m y) = M.env y)
    (i : Nat) (p : Pos) (n child : String)
    (conns : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
    (member : Typed.Equation.inst i p n child conns ∈ m.body)
    (c : Typed.Module) (found : t.bodies.find? (·.name == child) = some c) :
    ∃ args, ((instResults m.interfaces child).map (fun q => s!"{n}.{q.1}"),
      Mlir.Op.instance n child (instArgs m.interfaces child args) (instResults m.interfaces child))
        ∈ (finalState m).body.toList ∧
      InputsAgree c.ports (transportInput (child_ports (certified raw t h) m hm child c found)
        (connectionValues (certified raw t h) m hm M.values M.memories
          ⟨.inst i p n child conns, member⟩))
        (Mlir.instanceInputs ((instArgs m.interfaces child args).map (renameArg (rename m)))
          V) := by
  let d := certified raw t h
  have hports := child_ports d m hm child c found
  have hs := statement_of_part m _ member (i, .inst p n child conns) (by
    simp [Typed.Equation.parts])
  obtain ⟨e, he, args, _, rfl⟩ := instance_present m _ hs n rfl
  refine ⟨args, he, ?_⟩
  obtain ⟨regs, final, envM, values, memories, words, models, ops, reads, refs, clocks⟩ := M
  simp only at hregs hfinal hV ⊢
  subst hregs hfinal
  let M : Meaning m.ctx :=
    ⟨Lower.registers m, finalState m, envM, values, memories, words, models, ops, reads, refs,
      clocks⟩
  have good := (M.step_statements (Lower.statements m) (Lower.statements m) (fun _ h => h)
    (fun x hx => stmt_legal raw t h m hm x hx) {}).2 (Grows.refl _)
  rcases good.1 _ he with absent | good
  · cases absent
  obtain ⟨p', conns', args₀, hs', matched, sameArgs, _, _⟩ := good n child _ _ rfl
  cases inst_statement_unique raw t h m hm p p' n child conns conns' hs hs'
  have interfaces : m.interfaces = Typed.portsOf t.erase := (t.environments m hm).1
  have unique : ((m.interfaces child).map Port.name).Nodup := by
    rw [interfaces]
    exact interfaces_nodup t.erase (certified raw t h).wellFormed child
  intro q
  have hq : q.val ∈ m.interfaces child := by rw [hports]; exact q.property.1
  let selected := selectConnection conns q.val.name
    (typed_input_count d m hm i p n child conns member ⟨q.val, hq, q.property.2⟩)
  have foundInput : conns.find? (fun x => x.1.val.name == q.val.name) = some selected.val := by
    unfold selected selectConnection
    exact (Option.some_get _).symm
  obtain ⟨v, findArg, value⟩ := argsMatch_find M conns args₀ matched q.val.name _ foundInput
  have findInst := instArgs_find m.interfaces child unique args₀ q.val hq q.property.2 _ findArg
  rw [← sameArgs] at findInst
  have findRenamed : ((instArgs m.interfaces child args).map (renameArg (rename m))).find?
      (fun x => x.1 == q.val.name) =
      some (renameArg (rename m) (q.val.name, v, Lower.type selected.val.1.val.ty)) := by
    rw [List.find?_map]
    simp only [Function.comp_def, renameArg]
    rw [findInst]
    rfl
  have value' : V (rename m v) = some (coreValue _ (M.core selected.val.2)) :=
    (hV v).trans value
  have lhs := typed_coreValue V (rename m v) _ _ value'
  simp only [Mlir.instanceInputs, findRenamed, renameArg, Option.bind_eq_bind]
  refine lhs.trans (congrArg some ?_)
  change _ = coreValue q.val.ty (evalExpr values memories
    (connectionExpr d m hm i p n child conns member ⟨q.val, hq, q.property.2⟩))
  unfold connectionExpr
  rw [cast_coreValue m]
  rfl

theorem instance_facts (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ)
    (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (i : Nat) (p : Pos) (n child : String)
    (conns : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
    (member : Typed.Equation.inst i p n child conns ∈ m.body)
    (c : Typed.Module) (found : t.bodies.find? (·.name == child) = some c) :
    let d := certified raw t h
    let back := readBack m (all [])
    let memories := stateMemories m (designChildren d env m hm) s
    ∃ args', (Lower.module m).1.findInstance n = some (child, args') ∧
      ((lower t).withModels (memoryConfigs t)).findModule child = some (Lower.module c).1 ∧
      Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module c).1
        (σ.instance n)
        (Mlir.instanceInputs args' (all [])) (fun path => all (n :: path)) ∧
      InputsAgree c.ports (transportInput (child_ports d m hm child c found)
        (connectionValues d m hm back memories ⟨.inst i p n child conns, member⟩))
        (Mlir.instanceInputs args' (all [])) ∧
      ∀ port ∈ m.interfaces child, port.dir = .output →
        all [] s!"{n}.{port.name}" = all [n] (rename c port.name) := by
  intro d back memories
  let MU := readMeaning raw t h noExterns m hm env s σ corr inputs all hv
  have hc := List.mem_of_find?_eq_some found
  have hports := child_ports d m hm child c found
  obtain ⟨args, he, agreeInputs⟩ := connection_agree raw t h m hm MU rfl rfl (all [])
    (fun _ => rfl) i p n child conns member c found
  let args' := (instArgs m.interfaces child args).map (renameArg (rename m))
  have entry : ((instResults m.interfaces child).map (fun q => s!"{n}.{q.1}"),
      Mlir.Op.instance n child args' (instResults m.interfaces child)) ∈
        (Lower.module m).1.body := by
    rw [module_body]
    exact List.mem_map.mpr ⟨_, List.mem_append_left _ (List.mem_append_left _ he),
      by simp only [substitute_instance]; rfl⟩
  have hfind :
      ((lower t).withModels (memoryConfigs t)).findModule child = some (Lower.module c).1 := by
    have name : (Lower.module c).1.name = child := by
      rw [module_name]
      simpa using List.find?_some found
    rw [← name]
    exact findModule_mem _ (design_names raw t h noExterns) _ (body_in_design t noExterns c hc)
  have fi := findInstance_mem _ (module_instNames raw t h noExterns m hm _ rfl) _ _ _ _ _ entry
  have childSolution := hierarchy_child _ _ σ inputs all hv n child args' fi _ hfind
  obtain ⟨child', found', _, _, _, outputs⟩ := hv.1.2.1 _ entry
  rw [hfind] at found'
  cases found'
  refine ⟨args', fi, hfind, childSolution, agreeInputs, fun port portMember dir => ?_⟩
  obtain ⟨k, hk, hname, hout⟩ := filter_index (m.interfaces child) (·.dir == .output)
    (fun q => s!"{n}.{q.name}") (fun q => rename c q.name) port portMember (by simp [dir])
  have names : (instResults m.interfaces child).map (fun q => s!"{n}.{q.1}") =
      ((m.interfaces child).filter (·.dir == .output)).map (fun q => s!"{n}.{q.name}") := by
    rw [instResults_filter, List.map_map]
    rfl
  have childOutputs : (Lower.module c).1.outputs =
      ((m.interfaces child).filter (·.dir == .output)).map (fun q => rename c q.name) := by
    rw [outputs_filter, hports]
  obtain ⟨v, hv₁, ⟨source, hsrc, hv₂⟩, _⟩ := outputs ⟨k, by rw [names]; exact hk⟩
  have atName : all [] s!"{n}.{port.name}" = some v := by
    rw [← hname]
    simp only [names] at hv₁
    exact hv₁
  rw [childOutputs, hout] at hsrc
  cases hsrc
  rw [atName]
  exact hv₂.symm

theorem read_instance (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ)
    (inputs : Mlir.Env) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (i : Nat) (p : Pos) (n child : String)
    (conns : List ((q : {q : Port // q ∈ m.interfaces child}) × Typed.Expr m.ctx q.val.ty))
    (member : Typed.Equation.inst i p n child conns ∈ m.body)
    (c : Typed.Module) (found : t.bodies.find? (·.name == child) = some c)
    (correct : ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found))
    (port : Port) (portMember : port ∈ m.interfaces child) (dir : port.dir = .output)
    (h₂ : port ∈ c.ports) :
    let d := certified raw t h
    let back := readBack m (all [])
    let memories := stateMemories m (designChildren d env m hm) s
    all [] s!"{n}.{port.name}" = some (coreValue port.ty
      ((step d env c (List.mem_of_find?_eq_some found)
        (cast (State_inst_module d env m hm i p n child conns member c found)
          (s ⟨.inst i p n child conns, member⟩))
        (transportInput (child_ports d m hm child c found)
          (connectionValues d m hm back memories ⟨.inst i p n child conns, member⟩))).2
        ⟨port, h₂, dir⟩)) := by
  intro d back memories
  obtain ⟨args', _, _, childSolution, agreeInputs, link⟩ := instance_facts raw t h noExterns m hm
    env s σ corr inputs all hv i p n child conns member c found
  have corr' := corresponds_instance d env noExterns m hm s σ corr i p n child conns member c found
  obtain ⟨outs, _⟩ := (correct _ _ corr' _ _ agreeInputs).2 _ childSolution
  rw [link port portMember dir]
  exact outs ⟨port, h₂, dir⟩

theorem read_solution (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m)
    (inputs : Mlir.Env) (agree : InputsAgree m.ports input inputs) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (children : ∀ i p n child inputs, Typed.Equation.inst i p n child inputs ∈ m.body →
      ∀ c (found : t.bodies.find? (·.name == child) = some c),
        ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found)) :
    IsSolution (certified raw t h) env m hm s input (readBack m (all [])) := by
  let MU := readMeaning raw t h noExterns m hm env s σ corr inputs all hv
  have named (x : String) (stmt : Typed.Stmt m.ctx m.interfaces)
      (hs : stmt ∈ Lower.statements m) (letName : LetName stmt = some x) (w : Nat)
      (e : Typed.Expr m.ctx (.bits w))
      (result : ∀ s', letResult (Lower.registers m) stmt s' =
        (Lower.expr (Lower.registers m) e (some x) s').1)
      (state : ∀ s', (Lower.statement (Lower.registers m) stmt s').2 =
        (Lower.expr (Lower.registers m) e (some x) s').2) (legal : Legal e) (found) :
      readBack m (all []) (.name x) w found = MU.core e := by
    obtain ⟨s', grows, renamed⟩ := let_results raw t h m hm stmt hs x letName
    have post := (MU.step_expr e legal (some x) s').2 (state s' ▸ grows) trivial
    apply readBack_eq
    rw [valueName_plain _ _ (letName_not_register raw t h m hm stmt hs x letName), renamed,
      result]
    exact post
  intro node width found driver
  cases driver with
  | input p member dir bits =>
    have hp : Lower.port p ∈ (Lower.module m).1.inputPorts := by
      simp only [Mlir.Module.inputPorts, module_ports, List.mem_filter, List.mem_map]
      exact ⟨⟨_, member, rfl⟩, by simp [Lower.port, dir]⟩
    obtain ⟨v, hi, _, hval⟩ := hv.1.1 _ hp
    have ha := agree ⟨p, member, dir⟩
    simp only [Lower.port] at hi hval
    rw [hi, coreValue_cast bits] at ha
    cases ha
    apply readBack_eq
    rw [valueName_plain _ _ (port_not_register raw t h m hm _ member),
      rename_other raw t h m hm _ (input_not_letName raw t h m hm _ member dir)]
    exact hval
  | let_ index pos x _ e member =>
    have hs := statement_of_part m _ member (index, .let_ pos x width e) (by
      simp [Typed.Equation.parts])
    exact named x _ hs rfl width e (fun _ => rfl) (fun _ => rfl)
      (stmt_legal raw t h m hm _ hs) found
  | assign index pos x _ target e member =>
    have hs := statement_of_part m _ member (index, .assign pos x width target e) (by
      simp [Typed.Equation.parts])
    exact named x _ hs rfl width e (fun _ => rfl) (fun _ => rfl)
      (stmt_legal raw t h m hm _ hs) found
  | reg i p n _ clk target reset ni np next member =>
    obtain ⟨nextName, _, entry⟩ := register_entry_body m i p n width clk target reset ni np next
      member
    have equation := hv.1.2.1 _ entry
    simp only [Lower.substitute] at equation
    obtain ⟨name, v, same, hs, _, hval⟩ := equation
    cases List.singleton_inj.mp same
    have hreg := corresponds_register (certified raw t h) env noExterns m hm s σ corr i p n width
      clk target reset ni np next member
    change σ.regs _ = _ at hreg
    rw [hreg] at hs
    cases hs
    apply readBack_eq
    have inRegs : n ∈ Lower.registers m := List.mem_filterMap.mpr ⟨_, member, rfl⟩
    have contains : (Lower.registers m).contains n = true := by simpa using inRegs
    simp only [Lower.valueName, contains, ↓reduceIte]
    rw [rename_invalid raw t h m hm _ (register_invalid n)]
    exact hval
  | inst i p n child conns member port portMember dir bits =>
    obtain ⟨c, found⟩ := instance_child_exists (certified raw t h) noExterns m hm i p n child
      conns member
    have h₂ : port ∈ c.ports := by
      rw [← child_ports (certified raw t h) m hm child c found]
      exact portMember
    have value := read_instance raw t h noExterns m hm env s σ corr inputs all hv i p n child
      conns member c found (children i p n child conns member c found) port portMember dir h₂
    apply readBack_eq
    simp only [Lower.valueName]
    rw [rename_invalid raw t h m hm _ (result_invalid n port.name), value,
      coreValue_cast bits]
    simp only [ValueDriver.eval]
    exact congrArg (fun x => some (Mlir.Value.bits width (cast (congrArg TyValue bits) x)))
      (child_out (certified raw t h) env m hm i p n child conns member c found _ _ port
        portMember h₂ dir).symm


include h hm in
theorem output_not_clock (q : Port) (hq : q ∈ m.ports) (dir : q.dir = .output) :
    q.ty ≠ .clock :=
  ((module_wf raw t h).2.2.2.2.2.2.2.1 (.module m.erase) (module_item raw t h m hm)).2.1 q hq dir

theorem read_outputs (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m)
    (inputs : Mlir.Env) (agree : InputsAgree m.ports input inputs) (all : Mlir.Valuation)
    (hv : Mlir.IsHierarchySolution ((lower t).withModels (memoryConfigs t)) (Lower.module m).1 σ
      inputs all)
    (children : ∀ i p n child inputs, Typed.Equation.inst i p n child inputs ∈ m.body →
      ∀ c (found : t.bodies.find? (·.name == child) = some c),
        ModuleCorrect raw t h noExterns env c (List.mem_of_find?_eq_some found)) :
    OutputsAgree m (step (certified raw t h) env m hm s input).2 (all []) := by
  have same := backTranslation_eq_solution (certified raw t h) env m hm s input _
    (read_solution raw t h noExterns m hm env s σ corr input inputs agree all hv children)
  intro q
  obtain ⟨⟨pos, qdir, name, ty⟩, hq, dir⟩ := q
  cases ty with
  | clock => exact absurd rfl (output_not_clock raw t h m hm _ hq dir)
  | bits w =>
    have found := port_found t (certified raw t h).wellFormed m hm ⟨pos, qdir, name, .bits w⟩ hq rfl
    have value := read_refs raw t h m hm hv.1 (.name name) w found
    rw [valueName_plain _ _ (port_not_register raw t h m hm _ hq)] at value
    refine value.trans ?_
    change _ = some (Mlir.Value.bits w (solution (certified raw t h) env m hm s input
      (.name name) w _))
    rw [← same]

end

end Silicon.Core.LowerProof
