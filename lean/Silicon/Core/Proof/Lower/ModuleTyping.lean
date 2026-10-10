import Silicon.Core.Proof.Lower.Refs
import Silicon.Core.Proof.Lower.StatementTyping

/-!
The final module types every op, port, and update that its statements build.
-/
namespace Silicon.Core.LowerProof

theorem temporary_invalid (i : Nat) : Rules.invalidName (toString i) = true := by
  simp only [Rules.invalidName, decimal_not_core, Bool.not_false]

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

def moduleTyping : Typing m.ctx where
  registers := Lower.registers m
  final := Lower.statementState m
  rename := rename m
  Has := Has m
  defined := fun names op he pair hp same =>
    has_of_mem raw t h m hm pair.1 pair.2 same
      (defs_body m (names, op) (List.mem_append_left _ (List.mem_append_left _ he)) pair hp)
  temps := fun i => rename_invalid raw t h m hm _ (temporary_invalid i)
  reads := fun r hr w depth found => reads_has raw t h m hm r hr w depth found
  refs := fun node w found => refs_has raw t h m hm node w found
  clocks := fun n found => clocks_has raw t h m hm n found

theorem stmt_legal (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m) :
    StmtLegal stmt := by
  let d := Semantics.CertifiedDesign.ofCheck raw t h
  have numbers := d.wellFormed.2.2.2.1
  have declared := (numbers (.module m.erase) (t.environments m hm).2.2).2 stmt.erase
    (by
      have member := stmt_erase_member m stmt hs
      have erase := check_sound_erase raw t h
      change stmt.erase ∈ m.erase.body
      exact member)
  have legal : ∀ {ty}, ∀ e : Typed.Expr m.ctx ty, e.erase ∈ Rules.stmtExprs stmt.erase →
      Legal e := fun e he =>
    (expression_legal m.ctx (context_positive d m hm) e (declared.2 e.erase he)).1
  cases stmt with
  | let_ p n w e => exact legal e (List.mem_singleton_self _)
  | assign p n w target e => exact legal e (List.mem_singleton_self _)
  | next p n w target e => exact legal e (List.mem_singleton_self _)
  | mem => trivial
  | reg p n w clk reset =>
    intro r hr
    have hr : reset = some r := Option.mem_toList.mp hr
    subst hr
    exact ⟨legal r.signal (by simp [Rules.stmtExprs, Typed.Stmt.erase, Typed.Reset.erase]),
      legal r.value (by simp [Rules.stmtExprs, Typed.Stmt.erase, Typed.Reset.erase])⟩
  | write p n index w depth target a d en =>
    exact ⟨legal a (by simp [Rules.stmtExprs, Typed.Stmt.erase]),
      legal d (by simp [Rules.stmtExprs, Typed.Stmt.erase]),
      legal en (by simp [Rules.stmtExprs, Typed.Stmt.erase])⟩
  | inst p n child inputs =>
    intro i hi
    exact legal i.2 (by
      simp only [Rules.stmtExprs, Typed.Stmt.erase, List.map_map, List.mem_map]
      exact ⟨i, hi, rfl⟩)

omit h hm in
theorem aliasOf_none (e : Typed.Expr m.ctx ty) (fresh : NotAliased e)
    (v : Option String) (alias : AliasOf (Lower.registers m) (Lower.statementState m) e v) :
    v = none := by
  cases e with
  | ref => exact fresh.elim
  | read =>
    rcases alias with ⟨full, _⟩ | ⟨_, none⟩
    · exact absurd full fresh
    · exact none
  | _ => exact alias

theorem stmt_fresh (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m) :
    (moduleTyping raw t h m hm).StmtFresh stmt := by
  have alias := (final_aliases raw t h m hm).2 stmt hs
  cases stmt with
  | let_ p n w e =>
    intro fresh
    exact rename_none m n (aliasOf_none m e fresh _ alias)
  | assign p n w target e =>
    intro fresh
    exact rename_none m n (aliasOf_none m e fresh _ alias)
  | _ => trivial

omit h hm in
theorem reg_width (stmt : Typed.Stmt m.ctx m.interfaces) (hs : stmt ∈ Lower.statements m) :
    RegWidth stmt := by
  cases stmt with
  | reg p n w clk reset =>
    obtain ⟨eq, he, part, hp, same⟩ := (statement_of_eq m _).mp hs
    cases eq <;> simp only [Typed.Equation.parts, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at hp
    all_goals first
      | (rcases hp with rfl | rfl <;> cases same)
      | (subst hp; cases same)
      | (rcases hp with rfl | ⟨_, _, rfl⟩ <;> cases same)
    case reg.reg.inl.refl => exact valueTy_lookup _ _ _ (by assumption)
  | _ => trivial

/-- Every op, port, and update of the final statement state has a type. -/
theorem final_good : (moduleTyping raw t h m hm).NewGood {} (Lower.statementState m) := by
  have step := (moduleTyping raw t h m hm).step_statements (Lower.statements m)
    (fun stmt hs => ⟨stmt_legal raw t h m hm stmt hs, stmt_fresh raw t h m hm stmt hs,
      reg_width m stmt hs⟩) {}
  exact step.2 (Grows.refl _)

end

end Silicon.Core.LowerProof
