import Silicon.Core.Proof.Lower.Growth
import Silicon.Core.Proof.Lower.Resolve

/-!
Each alias of a checked module comes from one named statement.
Source ranks decrease along aliases, so alias resolution reaches a defined name.
-/
namespace Silicon.Core.LowerProof

private theorem filterMap_sublist (xs : List α) (f g : α → Option β)
    (h : ∀ x, f x = none ∨ f x = g x) : (xs.filterMap f).Sublist (xs.filterMap g) := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rcases h x with hx | hx
    · rw [hx]
      cases g x with
      | none => exact ih
      | some y => exact ih.cons _
    · rw [hx]
      cases g x with
      | none => exact ih
      | some y => exact ih.cons_cons _

theorem checked_erase_member (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) : m.erase ∈ Typed.modules raw := by
  have erase := check_sound_erase raw t h
  apply List.mem_filterMap.mpr
  exact ⟨.module m.erase, erase ▸ (t.environments m hm).2.2, rfl⟩

theorem letNames_nodup (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) :
    ((Lower.statements m).filterMap LetName).Nodup := by
  have unique := Check.module_driver_names_nodup raw m.erase (check_sound raw t h).1
    (checked_erase_member raw t h m hm)
  rw [← statements_erase m] at unique
  rw [List.filterMap_map] at unique
  apply List.Nodup.sublist _ unique
  apply filterMap_sublist
  intro stmt
  cases stmt <;> simp [LetName, Typed.Stmt.erase, Stmt.driverName]

theorem letName_legal (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (stmt : Typed.Stmt m.ctx m.interfaces)
    (hs : stmt ∈ Lower.statements m) (name : String) (named : LetName stmt = some name) :
    Rules.invalidName name = false := by
  have member : stmt.erase ∈ m.erase.body := by
    rw [← statements_erase m]
    exact List.mem_map_of_mem hs
  apply checked_driver_legal raw m.erase (check_sound raw t h).1
    (checked_erase_member raw t h m hm) _ member
  cases stmt <;> simp_all [LetName, Typed.Stmt.erase, Stmt.driverName]

abbrev finalAliases (m : Typed.Module) : Std.HashMap String String :=
  (Lower.statementState m).aliases

theorem final_aliases (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) :
    (∀ k, k ∉ (Lower.statements m).filterMap LetName → (finalAliases m)[k]? = none) ∧
    ∀ stmt ∈ Lower.statements m,
      StmtAlias (Lower.registers m) (Lower.statementState m) (finalAliases m) stmt := by
  have result := statements_aliases (Lower.registers m) (Lower.statements m) {}
    (letNames_nodup raw t h m hm) (fun _ _ => Std.HashMap.getElem?_empty)
  exact ⟨fun k hk => (result.1 k hk).trans Std.HashMap.getElem?_empty, result.2⟩

theorem alias_source (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (k v : String)
    (found : (finalAliases m)[k]? = some v) :
    ∃ stmt ∈ Lower.statements m, LetName stmt = some k ∧
      StmtAlias (Lower.registers m) (Lower.statementState m) (finalAliases m) stmt := by
  have facts := final_aliases raw t h m hm
  by_cases member : k ∈ (Lower.statements m).filterMap LetName
  · obtain ⟨stmt, hs, named⟩ := List.mem_filterMap.mp member
    exact ⟨stmt, hs, named, facts.2 stmt hs⟩
  · rw [facts.1 k member] at found
    cases found

theorem alias_key_legal (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (k : String) (hk : k ∈ finalAliases m) :
    Rules.invalidName k = false := by
  obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp
    (Std.HashMap.isSome_getElem?_iff_mem.mpr hk)
  obtain ⟨stmt, hs, named, _⟩ := alias_source raw t h m hm k v found
  exact letName_legal raw t h m hm stmt hs k named

theorem readName_invalid (r : Lower.ReadPort) : Rules.invalidName (readName r) = true := by
  have ne := source_ne_result (readName r) r.memory s!"r{r.index}_data"
  by_cases legal : Rules.invalidName (readName r) = false
  · exact absurd (by
      change r.memory ++ ("." ++ "r") ++ r.index.repr ++ "_data" =
        r.memory ++ "." ++ ("r" ++ r.index.repr ++ "_data")
      simp only [String.append_assoc]) (ne legal)
  · simpa using legal

theorem register_invalid (name : String) :
    Rules.invalidName (regName name) = true := by
  simp [Rules.invalidName, regName_not_core]

theorem stmt_erase_member (m : Typed.Module) (stmt : Typed.Stmt m.ctx m.interfaces)
    (hs : stmt ∈ Lower.statements m) : stmt.erase ∈ m.erase.body := by
  rw [← statements_erase m]
  exact List.mem_map_of_mem hs

theorem letName_key (m : Typed.Module) (stmt : Typed.Stmt m.ctx m.interfaces)
    (hs : stmt ∈ Lower.statements m) (name : String) (named : LetName stmt = some name) :
    Deps.Node.name name ∈ (Deps.graph m.erase m.children).map Prod.fst := by
  rw [Deps.graph_keys]
  apply List.mem_map.mpr
  have member := stmt_erase_member m stmt hs
  cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
  all_goals subst named
  all_goals exact ⟨_, List.mem_flatMap.mpr ⟨_, member, List.mem_singleton_self _⟩, rfl⟩

theorem ref_edge (m : Typed.Module) (stmt : Typed.Stmt m.ctx m.interfaces)
    (hs : stmt ∈ Lower.statements m) (k v : String)
    (erased : Deps.equations m.children stmt.erase = [(.name k, [.name v])])
    (key : Deps.Node.name v ∈ (Deps.graph m.erase m.children).map Prod.fst) :
    Typed.rank m.ranks (.name v) < Typed.rank m.ranks (.name k) := by
  have member := stmt_erase_member m stmt hs
  have equation : (Deps.Node.name k, [Deps.Node.name v]) ∈
      m.erase.body.flatMap (Deps.equations m.children) := by
    apply List.mem_flatMap.mpr
    refine ⟨stmt.erase, member, ?_⟩
    rw [erased]
    exact List.mem_singleton_self _
  obtain ⟨reads, row, kept⟩ := Deps.graph_row m.erase m.children _ equation
  exact m.acyclic _ row _ ((kept _).mpr ⟨List.mem_singleton_self _, Or.inl key⟩)

theorem alias_decreasing (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (k v : String)
    (found : (finalAliases m)[k]? = some v) (hv : v ∈ finalAliases m) :
    Typed.rank m.ranks (.name v) < Typed.rank m.ranks (.name k) := by
  obtain ⟨stmt, hs, named, alias⟩ := alias_source raw t h m hm k v found
  have legal := alias_key_legal raw t h m hm v hv
  obtain ⟨w', found'⟩ := Option.isSome_iff_exists.mp
    (Std.HashMap.isSome_getElem?_iff_mem.mpr hv)
  obtain ⟨stmt', hs', named', _⟩ := alias_source raw t h m hm v w' found'
  have key := letName_key m stmt' hs' v named'
  cases stmt <;> simp only [LetName, reduceCtorEq, Option.some.injEq] at named
  all_goals subst named
  case let_ p name w e | assign p name w target e =>
    simp only [StmtAlias, found] at alias
    cases e <;> simp only [AliasOf, reduceCtorEq] at alias
    case ref p' node f =>
      cases node with
      | name x =>
        simp only [Lower.valueName, Option.some.injEq] at alias
        split at alias
        · subst alias
          rw [register_invalid] at legal
          cases legal
        · subst alias
          exact ref_edge m _ hs name v rfl key
      | port i q =>
        simp only [Lower.valueName, Option.some.injEq] at alias
        exact absurd alias (source_ne_result v i q legal)
    case read =>
      rcases alias with ⟨_, r, _, _, same⟩ | ⟨_, same⟩
      · cases same
        rw [readName_invalid] at legal
        cases legal
      · cases same

end Silicon.Core.LowerProof
