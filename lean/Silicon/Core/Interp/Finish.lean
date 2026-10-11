-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Interp.Cycle

/-! State updates use final connections and the values already stored for this cycle. -/
namespace Silicon.Core.Interp

open Semantics

def nextCached (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) (values : Valuation m.ctx)
    (same : values = localSolution d m hm children state input)
    (cache : ChildCache d m hm children runners state input) (e : EquationRef m) :
    {value : CellState m e.val (children e) // value =
      (localStepWithValues d m hm children state values).1 e} := by
  let memories := stateMemories m children state
  let connections := connectionValues d m hm values memories
  obtain ⟨e, member⟩ := e
  cases e with
  | inst i p n child inputs =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    have eq : finalConnections d m hm children state input e = connections e := by
      dsimp only [connections]
      rw [same]
      rfl
    let childCache := cast (congrArg ((runners e).Cache (state e)) eq)
      (ChildCache.get d m hm children runners state input cache e)
    let result := (runners e).finish (state e) (connections e) childCache
    exact ⟨result.val.1, congrArg Prod.fst result.property⟩
  | reg _ _ _ _ _ _ reset _ _ next =>
    exact ⟨nextRegister values memories reset next, rfl⟩
  | mem i p n w size c t writes =>
    exact ⟨nextMemory values memories (state ⟨.mem i p n w size c t writes, member⟩) writes, rfl⟩
  | let_ | assign => exact ⟨(), rfl⟩

private def equationDecEq (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    DecidableEq (EquationRef m) := fun a b =>
  decidable_of_iff (equationName a.val = equationName b.val) (by
    constructor
    · intro same
      exact Subtype.ext (equation_unique d.design d.wellFormed m hm _ _
        a.property b.property same)
    · intro same
      subst b
      rfl)

def finishCache (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (prepared : OrderedValues d m hm)
    (state : LocalState m children) (input : Input m)
    (cache : CycleCache d m hm children runners state input) :
    {result : LocalState m children × Output m // result =
      localStepWithValues d m hm children state (localSolution d m hm children state input)} := by
  let filled := completeCache d m hm children runners prepared state input cache
  let values := filled.val.1
  have same : values = localSolution d m hm children state input := filled.property
  letI := equationDecEq d m hm
  letI : Hashable (EquationRef m) := ⟨fun e => hash (equationName e.val)⟩
  let next := indexed
    (fun e =>
      (nextCached d m hm children runners state input values same filled.val.2.children e).val)
    m.body.attach (fun e => List.mem_attach _ e)
  refine ⟨(next.get, outputValues d m hm values), ?_⟩
  apply Prod.ext
  · change next.get = _
    rw [Table.get_eq]
    funext e
    exact (nextCached d m hm children runners state input values same
      filled.val.2.children e).property
      |>.trans (by rw [same])
  · change outputValues d m hm values = _
    rw [same]
    rfl

/-! An output request fills only its dependency cone; the final pass fills the rest. -/
def localEvaluator (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (prepared : Prepared d m hm) :
    Evaluator (localComponent d m hm children) :=
  { Cache := CycleCache d m hm children runners
    empty := emptyCache d m hm children runners
    output := fun state {target} input port agree cache => by
      let cone := prepared.cones port
      let selection := coneSelection d m hm input target port cone agree
      let filled := fillNodes d m hm children runners state input selection prepared.toOrderedValues
        cone.nodes cone.sorted cache (fun r selected absent =>
          False.elim (absent (cone.complete r selected)))
      let values := curryValues (fun ref => filled.val.values.getD ref 0)
      refine ⟨(outputValues d m hm values port, filled.val), ?_⟩
      rcases port with ⟨⟨pos, dir, name, ty⟩, member, direction⟩
      cases ty with
      | clock => rfl
      | bits width =>
        have selected : selection.contains (.name name) = true := by
          exact (cone.spec _).mpr (cone_self m.erase m.children _)
        exact (Std.DHashMap.getD_eq_getD_get?).trans
          (congrArg (fun x => x.getD 0) (filled.property ⟨.name name, width,
            port_found d.design d.wellFormed m hm _ member rfl⟩ selected))
    finish := fun state input cache =>
      finishCache d m hm children runners prepared.toOrderedValues state input cache }

def cachedLocalStep (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : LocalState m children × Output m :=
  (finishCache d m hm children runners
    (prepareValues d m hm (Deps.graph m.erase m.children) rfl) state input
    (emptyCache d m hm children runners state input)).val

theorem cachedLocalStep_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (runners : Runners m children)
    (state : LocalState m children) (input : Input m) :
    cachedLocalStep d m hm children runners state input =
      localStepWithValues d m hm children state (localSolution d m hm children state input) :=
  (finishCache d m hm children runners
    (prepareValues d m hm (Deps.graph m.erase m.children) rfl) state input
    (emptyCache d m hm children runners state input)).property

end Silicon.Core.Interp
