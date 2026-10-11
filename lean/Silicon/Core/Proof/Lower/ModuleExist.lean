-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleExistParts

/-!
The image of the core solution is an MLIR solution of the lowered module. Each source instance
takes a child solution with the core child outputs. Each memory takes the model solution of
its array.
-/
namespace Silicon.Core.LowerProof

open Semantics

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = []) (m : Typed.Module) (hm : m ∈ t.bodies)
  (env : Env (certified raw t h).design)

/-- The image environment of a module state and input, with its meaning. -/
structure ImageFacts (s : State (certified raw t h) env m hm) (input : Input m) where
  words : ModelMemories m.ctx
  env0 : Mlir.Env
  meaning : Meaning m.ctx
  registers : meaning.registers = Lower.registers m
  final : meaning.final = finalState m
  isEnv : meaning.env = env0
  values : meaning.values = solution (certified raw t h) env m hm s input
  memories : meaning.memories = stateMemories m (designChildren (certified raw t h) env m hm) s
  isWords : meaning.words = words
  good : meaning.NewGood (Lower.statements m) {} (finalState m)
  outside : ∀ y, y ∉ allocatedNames (finalState m) →
    env0 y = some (coreAt m (solution (certified raw t h) env m hm s input) y)
  renamed : ∀ y, env0 (rename m y) = env0 y

theorem image_facts (s : State (certified raw t h) env m hm) (σ : Mlir.ModuleState)
    (corr : Corresponds (certified raw t h) env noExterns m hm s σ) (input : Input m) :
    ∃ facts : ImageFacts raw t h m hm env s input,
      facts.words = stateWords raw t h noExterns m hm env s σ corr := by
  let d := certified raw t h
  let sol := solution d env m hm s input
  let memories := stateMemories m (designChildren d env m hm) s
  let words := stateWords raw t h noExterns m hm env s σ corr
  have models : ∀ name width depth found,
      MemModelProof.Agrees ⟨depth, width, 0, 0⟩ (words name width depth found)
        (memories name width depth found) := fun name width depth found =>
    (stateWords_spec raw t h noExterns m hm env s σ corr name width depth found).2
  obtain ⟨J, perm, frame, lets, insts⟩ := module_image raw t h m hm sol memories words models
  have unique : (J.map Prod.fst).Nodup := perm.nodup_iff.mpr (allocated_nodup raw t h m hm)
  let env0 := imageEnv J (coreAt m sol)
  have solved := localSolution_isSolution d m hm (designChildren d env m hm) s input
  have letSolves : ∀ index pos x w e, Typed.Equation.let_ index pos x w e ∈ m.body → ∀ found,
      sol (.name x) w found = evalExpr sol memories e :=
    fun index pos x w e member found => solved (.name x) w found (.let_ index pos x w e member)
  have assignSolves : ∀ index pos x w target e,
      Typed.Equation.assign index pos x w target e ∈ m.body → ∀ found,
      sol (.name x) w found = evalExpr sol memories e :=
    fun index pos x w target e member found =>
      solved (.name x) w found (.assign index pos x w target e member)
  have global := image_global raw t h m hm sol memories J unique perm lets insts letSolves
    assignSolves
  have frames := frame env0 (imageEnv_agrees J _ unique) global
  let ME : Meaning m.ctx := {
    registers := Lower.registers m
    final := finalState m
    env := env0
    values := sol
    memories := memories
    words := words
    models := models
    ops := fun names op he plain _ => by
      obtain ⟨⟨tail, body, eqs⟩, _⟩ := frames
      have same : tail = (finalState m).body.toList := by simpa using body.symm
      exact eqs names op (same ▸ he) plain
    reads := fun r hr => by
      rcases frames.2 r hr with absent | read
      · cases absent
      · exact read
    refs := global.1
    clocks := global.2 }
  have aliasOK : ∀ k v, (finalAliases m)[k]? = some v → env0 k = env0 v := by
    intro k v found
    obtain ⟨stmt, hs, named, _⟩ := alias_source raw t h m hm k v found
    obtain ⟨s', grows, result⟩ := statements_named_results (Lower.registers m) (Lower.statements m)
      {} (letNames_nodup raw t h m hm) (fun _ _ => Std.HashMap.getElem?_empty) stmt hs k named
    change ResultAlias _ k (finalAliases m)[k]? at result
    rw [found] at result
    change v = _ at result
    subst result
    have lookupK := letName_lookup raw t h m hm stmt hs k named
    have atK := global.1 (.name k) _ lookupK
    rw [valueName_plain _ _ (letName_not_register raw t h m hm stmt hs k named)] at atK
    change env0 k = _ at atK
    rw [atK]
    cases stmt with
    | let_ p x w e =>
      simp only [LetName, Option.some.injEq] at named
      subst named
      obtain ⟨index, member⟩ := let_equation m p x w e hs
      have post := (ME.step_expr e (stmt_legal raw t h m hm _ hs) (some x) s').2 grows trivial
      change env0 _ = _ at post
      rw [show letResult (Lower.registers m) (Typed.Stmt.let_ (ports := m.interfaces) p x w e) s' =
        (Lower.expr (Lower.registers m) e (some x) s').1 from rfl, post]
      exact congrArg (fun v => some (Mlir.Value.bits w v)) (letSolves index p x w e member lookupK)
    | assign p x w target e =>
      simp only [LetName, Option.some.injEq] at named
      subst named
      obtain ⟨index, member⟩ := assign_equation m p x w target e hs
      have post := (ME.step_expr e (stmt_legal raw t h m hm _ hs) (some x) s').2 grows trivial
      change env0 _ = _ at post
      rw [show letResult (Lower.registers m) (Typed.Stmt.assign (ports := m.interfaces) p x w
        target e) s' = (Lower.expr (Lower.registers m) e (some x) s').1 from rfl, post]
      exact congrArg (fun v => some (Mlir.Value.bits w v))
        (assignSolves index p x w target e member lookupK)
    | _ => simp [LetName] at named
  have good := (ME.step_statements (Lower.statements m) (Lower.statements m) (fun _ h => h)
    (fun x hx => stmt_legal raw t h m hm x hx) {}).2 (Grows.refl _)
  refine ⟨⟨words, env0, ME, rfl, rfl, rfl, rfl, rfl, rfl, good, fun y absent =>
    imageEnv_outside J _ y (fun member => absent (perm.mem_iff.mp member)),
    fun y => resolve_preserves (finalAliases m) env0 aliasOK _ y⟩, rfl⟩

end

end Silicon.Core.LowerProof
