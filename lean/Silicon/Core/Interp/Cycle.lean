import Silicon.Core.Interp.Demand

/-! The value cache and child caches grow until the cycle's final state update. -/
namespace Silicon.Core.Interp

open Semantics

def finalConnections (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (state : LocalState m children) (target : Input m) :=
  connectionValues d m hm (localSolution d m hm children state target)
    (stateMemories m children state)

def CachedChild (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (target : Input m) : (e : EquationRef m) → Type
  | ⟨.inst i p n child inputs, member⟩ =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    (runners e).Cache (state e) (finalConnections d m hm children state target e)
  | _ => Unit

abbrev ChildCache (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (target : Input m) := (e : EquationRef m) → CachedChild d m hm children runners state target e

structure CycleCache (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (target : Input m) where
  values : Std.DHashMap (ValueRef m.ctx) (fun ref => Value ref.width)
  valid : ∀ ref value, values.get? ref = some value →
    value = localSolution d m hm children state target ref.node ref.width ref.found
  children : ChildCache d m hm children runners state target

def emptyCache (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (target : Input m) : CycleCache d m hm children runners state target where
  values := ∅
  valid := by simp
  children := fun e => match e with
    | ⟨.inst i p n child inputs, member⟩ =>
      let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
      (runners e).empty (state e) (finalConnections d m hm children state target e)
    | ⟨.let_ .., _⟩ | ⟨.reg .., _⟩ | ⟨.mem .., _⟩ | ⟨.assign .., _⟩ => ()

def updateChild (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (target : Input m) (cache : ChildCache d m hm children runners state target)
    (e : EquationRef m) (value : CachedChild d m hm children runners state target e) :
    ChildCache d m hm children runners state target :=
  fun other => if same : equationName e.val = equationName other.val then
    have eq : e = other := Subtype.ext
      (equation_unique d.design d.wellFormed m hm e.val other.val e.property other.property same)
    eq ▸ value
  else cache other

/-! Only a missing value invokes a driver or a child output request. -/
def evalMissing (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) {target : Input m} (selection : Selection m input target)
    (cache : CycleCache d m hm children runners state target)
    (ref : ValueRef m.ctx) (driver : ValueDriver m ref.node ref.width)
    (selected : selection.contains ref.node = true)
    (ready : ∀ dep width found, ValueEdge m ref.node dep →
      cache.values.getD ⟨dep, width, found⟩ 0 =
        localSolution d m hm children state target dep width found) :
    {result : Value ref.width × ChildCache d m hm children runners state target //
      result.1 = localSolution d m hm children state target ref.node ref.width ref.found} := by
  obtain ⟨node, width, found⟩ := ref
  let values := curryValues (fun ref => cache.values.getD ref 0)
  let memories := stateMemories m children state
  have solved := localSolution_isSolution d m hm children state target
    node width found driver
  have correct := driver_congr d m hm children state input target selection values
    (localSolution d m hm children state target) driver selected ready
  cases driver with
  | inst i p n child inputs member port portMember dir bits =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    let result := (runners e).output (state e) (connectionValues d m hm values memories e)
      ⟨port, portMember, dir⟩ (by
        intro input dependency
        apply connectionValues_congr
        intro dep read width found
        exact ready dep width found (instance_read_row d m hm i p n child inputs member
          ⟨port, portMember, dir⟩ input dependency dep read)) (cache.children e)
    exact ⟨(cast (congrArg TyValue bits) result.val.1,
      updateChild d m hm children runners state target cache.children e result.val.2), by
        rw [result.property]
        exact solved.symm⟩
  | _ => exact ⟨(_, cache.children), correct.trans solved.symm⟩

/-! A cache hit leaves the node and all its descendants untouched. -/
def visitNode (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) {target : Input m} (selection : Selection m input target)
    (prepared : Prepared d m hm) (cache : CycleCache d m hm children runners state target)
    (ref : ValueRef m.ctx)
    (ready : selection.contains ref.node = true → ∀ dep width found,
      ValueEdge m ref.node dep → cache.values.getD ⟨dep, width, found⟩ 0 =
        localSolution d m hm children state target dep width found) :
    {out : CycleCache d m hm children runners state target //
      (∀ r v, cache.values.get? r = some v → out.values.get? r = some v) ∧
      (selection.contains ref.node = true → out.values.get? ref =
        some (localSolution d m hm children state target ref.node ref.width ref.found))} := by
  match found : cache.values.get? ref with
  | some value =>
    exact ⟨cache, (by simp), fun _ => found.trans (congrArg some (cache.valid _ _ found))⟩
  | none =>
    if selected : selection.contains ref.node = true then
      let result := evalMissing d m hm children runners state input selection cache ref
        (indexedDriver d m hm prepared.drivers prepared.total ref) selected (ready selected)
      refine ⟨⟨cache.values.insert ref result.val.1, ?_, result.val.2⟩, ?_, ?_⟩
      · intro r v hv
        simp only [Std.DHashMap.get?_insert] at hv
        split at hv
        next same =>
          have eq := eq_of_beq same
          subst r
          cases hv
          exact result.property
        next => exact cache.valid _ _ hv
      · intro r v hv
        rw [Std.DHashMap.get?_insert]
        split
        next same =>
          have eq := eq_of_beq same
          subst r
          rw [found] at hv
          contradiction
        next => exact hv
      · intro _
        simp only [Std.DHashMap.get?_insert, beq_self_eq_true, ↓reduceDIte]
        exact congrArg some result.property
    else exact ⟨cache, (by simp), fun h => False.elim (selected h)⟩

/-! The ordered pass fills a cone without replacing any value already in the cache. -/
def fillNodes (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) {target : Input m} (selection : Selection m input target)
    (prepared : Prepared d m hm) (nodes : List (ValueRef m.ctx))
    (sorted : nodes.Pairwise (fun a b => valueRank m a.node ≤ valueRank m b.node))
    (cache : CycleCache d m hm children runners state target)
    (ready : ∀ r, selection.contains r.node = true → r ∉ nodes → cache.values.get? r =
      some (localSolution d m hm children state target r.node r.width r.found)) :
    {out : CycleCache d m hm children runners state target //
      ∀ r, selection.contains r.node = true → out.values.get? r =
        some (localSolution d m hm children state target r.node r.width r.found)} := by
  match nodes with
  | [] => exact ⟨cache, fun r hr => ready r hr (by simp)⟩
  | node :: rest =>
    obtain ⟨lower, sortedRest⟩ := List.pairwise_cons.mp sorted
    let result := visitNode d m hm children runners state input selection prepared cache node (by
      intro selected dep width found edge
      have selectedDep := selection.closed node.node dep selected edge
      obtain ⟨reads, row, read⟩ := edge
      have rank : valueRank m dep < valueRank m node.node :=
        valueRank_read m _ row dep read
      have absent : (⟨dep, width, found⟩ : ValueRef m.ctx) ∉ node :: rest := by
        intro member
        rcases List.mem_cons.mp member with same | member
        · cases same; simp only at rank; omega
        · have := lower ⟨dep, width, found⟩ member
          dsimp only at this
          omega
      simp only [Std.DHashMap.getD_eq_getD_get?, ready ⟨dep, width, found⟩ selectedDep absent,
        Option.getD_some])
    exact fillNodes d m hm children runners state input selection prepared rest sortedRest
      result.val (by
        intro r selected absent
        by_cases same : r = node
        · subst r
          exact result.property.2 selected
        · apply result.property.1
          exact ready r selected (by simp [same, absent]))
termination_by nodes

def fillCache (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) {target : Input m} (selection : Selection m input target)
    (prepared : Prepared d m hm) (cache : CycleCache d m hm children runners state target) :=
  fillNodes d m hm children runners state input selection prepared prepared.nodes prepared.sorted
    cache (fun r _ absent => False.elim (absent (prepared.complete r)))

end Silicon.Core.Interp
