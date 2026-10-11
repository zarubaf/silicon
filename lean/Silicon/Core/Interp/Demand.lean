-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Interp.Prepared

/-!
A cache belongs to one instance and one cycle. Its values remain valid as more
inputs become available. An output request supplies only its declared dependencies.
-/
namespace Silicon.Core.Interp

open Semantics

structure Evaluator (model : Component ports deps) where
  Cache : model.State → PortValues ports .input → Type
  empty : (state : model.State) → (input : PortValues ports .input) → Cache state input
  output : (state : model.State) → {target : PortValues ports .input} →
    (input : PortValues ports .input) → (port : PortRef ports .output) →
    (∀ p, p.val.name ∈ (deps.lookup port.val.name).getD [] → input p = target p) →
    Cache state target →
    {result : TyValue port.val.ty × Cache state target //
      result.1 = model.out state target port}
  finish : (state : model.State) → (input : PortValues ports .input) → Cache state input →
    {result : model.State × PortValues ports .output //
      result = (model.next state input, model.out state input)}

structure Program (ports : List Port) (deps : Deps) where
  model : Component ports deps
  evaluator : Evaluator model

def CycleRunner (m : Typed.Module) (children : Children m) : (e : EquationRef m) → Type 1
  | ⟨.inst i p n child inputs, member⟩ =>
    Evaluator (children ⟨.inst i p n child inputs, member⟩)
  | _ => PUnit

abbrev Runners (m : Typed.Module) (children : Children m) :=
  (e : EquationRef m) → CycleRunner m children e

/-! The selection includes every equation read and has fixed input leaves. -/
structure Selection (m : Typed.Module) (input target : Input m) where
  contains : Deps.Node → Bool
  closed : ∀ node dep, contains node = true → ValueEdge m node dep → contains dep = true
  inputs : ∀ (p : PortRef m.ports .input), contains (.name p.val.name) = true →
    input p = target p

def allSelection (m : Typed.Module) (input : Input m) : Selection m input input :=
  ⟨fun _ => true, by simp, by simp⟩

def coneSelection (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (input target : Input m) (port : PortRef m.ports .output) (cone : PortCone m port)
    (agree : ∀ p, p.val.name ∈ ((Deps.infer m.erase m.children).lookup
      port.val.name).getD [] → input p = target p) : Selection m input target := by
  refine ⟨cone.contains, ?_, ?_⟩
  · intro node dep selected edge
    obtain ⟨reads, row, read⟩ := edge
    exact (cone.spec dep).mpr (cone_closed m.erase m.children
      (typed_graph_unique d.design d.wellFormed m hm) _ _ row
      ((cone.spec node).mp selected) dep read)
  · intro p selected
    by_cases clock : p.val.ty = .clock
    · haveI : Subsingleton (TyValue p.val.ty) := by rw [clock]; infer_instance
      exact Subsingleton.elim _ _
    · obtain ⟨width, ht⟩ : ∃ width, p.val.ty = .bits width := by
        cases ht : p.val.ty with
        | clock => exact False.elim (clock ht)
        | bits width => exact ⟨width, rfl⟩
      obtain ⟨deps, entry⟩ := output_infer_entry m.erase m.children port
      apply agree
      simpa [entry] using cone_input_inferred m.erase m.children port.val.name p.val.name
        deps entry (input_port_mem m.erase p.val p.property.1 p.property.2 ht)
        ((cone.spec _).mp selected)

/-! A selected driver reads only earlier selected values. -/
theorem driver_congr (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (state : LocalState m children) (input target : Input m)
    (selection : Selection m input target) (values final : Valuation m.ctx)
    (driver : ValueDriver m node width) (selected : selection.contains node = true)
    (agree : ∀ dep width found, ValueEdge m node dep → values dep width found =
      final dep width found) :
    driver.eval m children state input values (stateMemories m children state)
        (connectionValues d m hm values (stateMemories m children state)) =
      driver.eval m children state target final (stateMemories m children state)
        (connectionValues d m hm final (stateMemories m children state)) := by
  cases driver with
  | input p member dir bits =>
    exact congrArg (cast (congrArg TyValue bits)) (selection.inputs ⟨p, member, dir⟩ selected)
  | reg => rfl
  | let_ index pos name ownWidth expr member =>
    apply evalExpr_congr
    intro dep read width found
    apply agree dep width found
    refine ⟨Deps.reads expr.erase, ?_, read⟩
    apply List.mem_flatMap.mpr
    let stmt : Typed.Stmt m.ctx m.interfaces := .let_ pos name _ expr
    refine ⟨stmt.erase, ?_, by simp [stmt, Typed.Stmt.erase, Deps.equations]⟩
    apply (Ownership.mem_equationsErase m.body _).mpr
    exact ⟨_, member, index, .let_ pos name _ expr, by simp [Typed.Equation.parts], rfl⟩
  | assign index pos name width target expr member =>
    apply evalExpr_congr
    intro dep read width found
    apply agree dep width found
    refine ⟨Deps.reads expr.erase, ?_, read⟩
    apply List.mem_flatMap.mpr
    refine ⟨Core.Stmt.assign pos name expr.erase, ?_, by simp [Deps.equations]⟩
    apply (Ownership.mem_equationsErase m.body _).mpr
    exact ⟨_, member, index, .assign pos name _ target expr,
      by simp [Typed.Equation.parts], rfl⟩
  | inst index pos name child inputs member port portMember dir bits =>
    apply congrArg (cast (congrArg TyValue bits))
    apply (children ⟨.inst index pos name child inputs, member⟩).out_respects
    intro input dependency
    apply connectionValues_congr
    intro dep read width found
    exact agree dep width found (instance_read_row d m hm index pos name child inputs member
      ⟨port, portMember, dir⟩ input dependency dep read)

end Silicon.Core.Interp
