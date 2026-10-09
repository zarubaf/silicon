import Silicon.Core.Proof.Lower.Leaves

/-!
Each source value has its declared type in the lowered module. An alias chain follows
decreasing source ranks to a definition.
-/
namespace Silicon.Core.LowerProof

def stmtWidth : Typed.Stmt ctx ports → Nat
  | .let_ _ _ w _ | .assign _ _ w _ _ => w
  | _ => 0

theorem valueTy_lookup (ctx : Typed.Ctx) (n : String) (w : Nat)
    (h : Typed.valueTy ctx n = some (.bits w)) :
    ctx.lookup (.name n) = some (.value (.bits w)) := by
  unfold Typed.valueTy at h
  split at h <;> simp_all

theorem valueName_plain (registers : List String) (x : String) (absent : x ∉ registers) :
    Lower.valueName registers (.name x) = x := by
  simp [Lower.valueName, absent]

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

omit h hm in
theorem register_decl (x : String) (hx : x ∈ Lower.registers m) :
    ∃ p w clk r, Core.Stmt.reg p x w clk r ∈ m.erase.body := by
  obtain ⟨eq, he, named⟩ := List.mem_filterMap.mp hx
  cases eq <;> simp only [Option.some.injEq, reduceCtorEq] at named
  case reg i p n w clk target reset ni np next =>
    subst named
    refine ⟨p, w, clk, reset.map Typed.Reset.erase, ?_⟩
    rw [← statements_erase m]
    apply List.mem_map.mpr
    exact ⟨.reg p n w clk reset, (statement_of_eq m _).mpr ⟨_, he, (i, .reg p n w clk reset),
      by simp [Typed.Equation.parts], rfl⟩, rfl⟩

theorem port_not_register (p : Port) (hp : p ∈ m.ports) : p.name ∉ Lower.registers m := by
  intro hx
  obtain ⟨p', w, clk, r, hs⟩ := register_decl m _ hx
  have scope := List.nodup_append.mp (scope_nodup raw t h m hm)
  exact scope.2.2 _ (List.mem_map_of_mem hp) _
    (List.mem_filterMap.mpr ⟨_, hs, rfl⟩) rfl

theorem letName_not_register (stmt : Typed.Stmt m.ctx m.interfaces)
    (hs : stmt ∈ Lower.statements m) (x : String) (named : LetName stmt = some x) :
    x ∉ Lower.registers m := by
  intro hx
  obtain ⟨p', w', clk, r, hr⟩ := register_decl m _ hx
  have member := stmt_erase_member m stmt hs
  cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
  all_goals subst named
  case let_ p n w e =>
    have scope := (List.nodup_append.mp (scope_nodup raw t h m hm)).2.1
    have same := filterMap_unique scope member hr n rfl rfl
    cases same
  case assign p n w target e =>
    have resolved := ((module_wf raw t h).2.1.2 m.erase (checked_erase_member raw t h m hm)
      _ member).1
    change ((Rules.findPort m.erase n).any fun port => port.dir == .output) = true at resolved
    obtain ⟨port, found, _⟩ := (Option.any_eq_true _ _).mp resolved
    have named := List.find?_some found
    have portMember := List.mem_of_find?_eq_some found
    apply port_not_register raw t h m hm port portMember
    rw [show port.name = n by simpa using named]
    exact hx

theorem letName_lookup (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m)
    (x : String) (named : LetName stmt = some x) :
    m.ctx.lookup (.name x) = some (.value (.bits (stmtWidth stmt))) := by
  have member := stmt_erase_member m stmt hs
  cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
  all_goals subst named
  case let_ p n w e =>
    apply lookup_name raw t h m hm
    show (Deps.Node.name n, Typed.Kind.value (.bits w)) ∈ m.ctx
    rw [m.context_eq]
    unfold Typed.contextFromPorts
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, member, List.mem_singleton_self _⟩
  case assign p n w target e => exact valueTy_lookup _ _ _ target

theorem base_refs (node : Deps.Node) (w : Nat)
    (found : m.ctx.lookup node = some (.value (.bits w)))
    (notLet : ∀ x, node = .name x → x ∉ (Lower.statements m).filterMap LetName) :
    Has m (Lower.valueName (Lower.registers m) node) (.int w) := by
  have member := lookup_member _ _ _ found
  rw [m.context_eq] at member
  rcases context_member _ _ _ _ member with ⟨p, hp, rfl, kind⟩ | ⟨stmt, hs, decl⟩
  · unfold portKind at kind
    split at kind
    · cases kind
    · have kind : p.ty = .bits w := (Typed.Kind.value.inj kind).symm
      rw [valueName_plain _ _ (port_not_register raw t h m hm p hp)]
      cases dir : p.dir with
      | input =>
        have input := defs_input m p hp dir
        rw [kind] at input
        exact has_of_mem raw t h m hm _ _
          (rename_other raw t h m hm _ (input_not_letName raw t h m hm p hp dir)) input
      | output =>
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
              exact absurd (List.mem_filterMap.mpr ⟨_, ht, rfl⟩ :
                p.name ∈ (Lower.statements m).filterMap LetName) (notLet _ rfl)
          next => cases hsome
  · cases stmt with
    | let_ p n w' e =>
      obtain ⟨rfl, _⟩ := decl
      obtain ⟨typed, ht, erased⟩ := typed_of_raw m _ hs
      cases typed <;> simp only [Typed.Stmt.erase, reduceCtorEq] at erased
      case let_ p'' n'' w'' e'' =>
        obtain ⟨_, rfl, _⟩ := Core.Stmt.let_.inj erased
        exact absurd (List.mem_filterMap.mpr ⟨_, ht, rfl⟩ :
          n'' ∈ (Lower.statements m).filterMap LetName) (notLet _ rfl)
    | reg p n w' clk r =>
      obtain ⟨rfl, kind⟩ := decl
      cases kind
      obtain ⟨eq, he, part, hp, erased⟩ := eq_of_raw m _ hs
      cases eq with
      | reg i p'' n'' w'' clk'' target reset ni np next =>
        simp only [Typed.Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · obtain ⟨_, rfl, rfl, _⟩ := Core.Stmt.reg.inj erased
          have inRegs : n'' ∈ Lower.registers m := List.mem_filterMap.mpr ⟨_, he, rfl⟩
          simp only [Lower.valueName, List.contains_iff_mem, inRegs, ↓reduceIte]
          exact register_has raw t h m hm i p'' n'' w'' clk'' target reset ni np next he
        · cases erased
      | _ =>
        simp only [Typed.Equation.parts, List.mem_cons, List.mem_map, List.not_mem_nil,
          or_false] at hp
        all_goals first
          | (rcases hp with rfl | rfl <;> cases erased)
          | (subst hp; cases erased)
          | (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases erased)
    | mem => obtain ⟨_, kind⟩ := decl; cases kind
    | inst p i child xs =>
      obtain ⟨port, hp, output, rfl, kind⟩ := decl
      cases ty : port.ty with
      | clock => rw [ty] at kind; cases kind
      | bits w' =>
        rw [ty] at kind
        cases kind
        exact instport_has raw t h m hm p i child xs hs port hp output w ty
    | _ => exact decl.elim

theorem named_has (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m)
    (n : String) (w : Nat) (e : Typed.Expr m.ctx (.bits w))
    (alias : AliasOf (Lower.registers m) (Lower.statementState m) e (finalAliases m)[n]?)
    (entry : NotAliased e →
      ∃ op, ([n], op) ∈ (Lower.statementState m).body.toList ∧ op.resultTypes = [.int w])
    (deps : ∀ p' x' f', e = .ref p' (.name x') f' →
      Deps.equations m.children stmt.erase = [(.name n, [.name x'])])
    (ih : ∀ stmt' ∈ Lower.statements m, ∀ x', LetName stmt' = some x' →
      Typed.rank m.ranks (.name x') < Typed.rank m.ranks (.name n) →
        Has m x' (.int (stmtWidth stmt'))) :
    Has m n (.int w) := by
  have emitted (fresh : NotAliased e) (absent : (finalAliases m)[n]? = none) :
      Has m n (.int w) := by
    obtain ⟨op, member, types⟩ := entry fresh
    apply has_of_mem raw t h m hm _ _ (rename_none m n absent)
    apply defs_body m _ (List.mem_append_left _ (List.mem_append_left _ member))
    rw [types]
    exact List.mem_singleton_self _
  cases e with
  | ref p' node f' =>
    rw [has_alias raw t h m hm n _ alias]
    by_cases named : ∃ x', node = .name x' ∧ x' ∈ (Lower.statements m).filterMap LetName
    · obtain ⟨x', rfl, mem⟩ := named
      obtain ⟨stmt', hs', named'⟩ := List.mem_filterMap.mp mem
      have rank := ref_edge m stmt hs n x' (deps p' x' f' rfl) (letName_key m stmt' hs' x' named')
      have typed := ih stmt' hs' x' named' rank
      have width := (letName_lookup raw t h m hm stmt' hs' x' named').symm.trans f'
      have width : stmtWidth stmt' = w := by
        have := Typed.Kind.value.inj (Option.some.inj width)
        exact Ty.bits.inj this
      rw [valueName_plain _ _ (letName_not_register raw t h m hm stmt' hs' x' named'), ← width]
      exact typed
    · exact base_refs raw t h m hm node w f' (fun x eq mem => named ⟨x, eq, mem⟩)
  | @read width depth p' memory found addr =>
    rcases alias with ⟨_, r, hr, same, alias⟩ | ⟨short, absent⟩
    · rw [has_alias raw t h m hm n _ alias]
      exact reads_has raw t h m hm r hr w depth (same ▸ found)
    · exact emitted short absent
  | const => exact emitted trivial alias
  | un => exact emitted trivial alias
  | bin => exact emitted trivial alias
  | concat => exact emitted trivial alias
  | icmp => exact emitted trivial alias
  | mux => exact emitted trivial alias
  | extract => exact emitted trivial alias
  | replicate => exact emitted trivial alias

omit h hm in
theorem named_entry (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m)
    (n : String) (w : Nat) (e : Typed.Expr m.ctx (.bits w))
    (run : ∀ s, (Lower.statement (Lower.registers m) stmt s).2 =
      (Lower.expr (Lower.registers m) e (some n) s).2)
    (fresh : NotAliased e) :
    ∃ op, ([n], op) ∈ (Lower.statementState m).body.toList ∧ op.resultTypes = [.int w] := by
  obtain ⟨s, grows⟩ := presence m stmt hs
  obtain ⟨op, member, types⟩ := expr_dest_entry (Lower.registers m) e n fresh s
  rw [← run] at member
  exact ⟨op, grows.body.subset member, types⟩

theorem let_has_aux (k : Nat) : ∀ stmt ∈ Lower.statements m, ∀ n, LetName stmt = some n →
    Typed.rank m.ranks (.name n) < k → Has m n (.int (stmtWidth stmt)) := by
  induction k with
  | zero => intro _ _ _ _ bound; omega
  | succ k ih =>
    intro stmt hs n named bound
    have alias := (final_aliases raw t h m hm).2 stmt hs
    have below : ∀ stmt' ∈ Lower.statements m, ∀ x', LetName stmt' = some x' →
        Typed.rank m.ranks (.name x') < Typed.rank m.ranks (.name n) →
          Has m x' (.int (stmtWidth stmt')) :=
      fun stmt' hs' x' named' lt => ih stmt' hs' x' named' (by omega)
    cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
    all_goals subst named
    case let_ p n w e =>
      exact named_has raw t h m hm _ hs n w e alias
        (named_entry m _ hs n w e (fun _ => rfl))
        (fun p' x' f' eq => by subst eq; rfl) below
    case assign p n w target e =>
      exact named_has raw t h m hm _ hs n w e alias
        (named_entry m _ hs n w e (fun _ => rfl))
        (fun p' x' f' eq => by subst eq; rfl) below

theorem refs_has (node : Deps.Node) (w : Nat)
    (found : m.ctx.lookup node = some (.value (.bits w))) :
    Has m (Lower.valueName (Lower.registers m) node) (.int w) := by
  by_cases named : ∃ x', node = .name x' ∧ x' ∈ (Lower.statements m).filterMap LetName
  · obtain ⟨x', rfl, mem⟩ := named
    obtain ⟨stmt, hs, named⟩ := List.mem_filterMap.mp mem
    have typed := let_has_aux raw t h m hm _ stmt hs x' named (Nat.lt_succ_self _)
    have width := (letName_lookup raw t h m hm stmt hs x' named).symm.trans found
    have width : stmtWidth stmt = w := Ty.bits.inj (Typed.Kind.value.inj (Option.some.inj width))
    rw [valueName_plain _ _ (letName_not_register raw t h m hm stmt hs x' named), ← width]
    exact typed
  · exact base_refs raw t h m hm node w found (fun x eq mem => named ⟨x, eq, mem⟩)

end

end Silicon.Core.LowerProof
