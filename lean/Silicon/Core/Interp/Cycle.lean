import Silicon.Core.Interp.Values
import Silicon.Core.Semantics.Step

/-! A child call returns its outputs and next state in one record. -/
namespace Silicon.Core.Interp

open Semantics

structure CycleResult (model : Component ports deps) (state : model.State)
    (input : PortValues ports .input) where
  result : model.State × PortValues ports .output
  correct : result = (model.next state input, model.out state input)

structure Program (ports : List Port) (deps : Deps) where
  model : Component ports deps
  cycle : (state : model.State) → (input : PortValues ports .input) →
    CycleResult model state input

structure Snapshot (model : Component ports deps) (state : model.State) where
  input : PortValues ports .input
  cycle : CycleResult model state input

private instance (ty : Ty) : DecidableEq (TyValue ty) := by
  cases ty <;> infer_instance

private def sameInputs (ports : List Port) (a b : PortValues ports .input) : Decidable (a = b) :=
  decidable_of_iff (∀ p ∈ ports.attach, ∀ h : p.val.dir = .input,
    a ⟨p.val, p.property, h⟩ = b ⟨p.val, p.property, h⟩) (by
      constructor
      · intro h
        funext p
        exact h ⟨p.val, p.property.1⟩ (by simp) p.property.2
      · intro h
        subst b
        simp)

def cachedCycle (model : Component ports deps)
    (run : (state : model.State) → (input : PortValues ports .input) →
      CycleResult model state input)
    (state : model.State) (input : PortValues ports .input)
    (cached : Option (Snapshot model state)) : CycleResult model state input :=
  match cached with
  | none => run state input
  | some old =>
    have := sameInputs ports old.input input
    if same : old.input = input then same ▸ old.cycle else run state input

def CycleRunner (m : Typed.Module) (children : Children m) :
    (e : EquationRef m) → Type
  | ⟨.inst i p n child inputs, member⟩ =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    (state : (children e).State) → (input : PortValues (m.interfaces child) .input) →
      CycleResult (children e) state input
  | _ => Unit

abbrev Runners (m : Typed.Module) (children : Children m) :=
  (e : EquationRef m) → CycleRunner m children e

def CachedChild (m : Typed.Module) (children : Children m) (state : LocalState m children) :
    (e : EquationRef m) → Type
  | ⟨.inst i p n child inputs, member⟩ =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    Option (Snapshot (children e) (state e))
  | _ => Unit

abbrev ChildCache (m : Typed.Module) (children : Children m) (state : LocalState m children) :=
  (e : EquationRef m) → CachedChild m children state e

def emptyChildren (m : Typed.Module) (children : Children m) (state : LocalState m children) :
    ChildCache m children state
  | ⟨.inst .., _⟩ => none
  | ⟨.let_ .., _⟩ | ⟨.reg .., _⟩ | ⟨.mem .., _⟩ | ⟨.assign .., _⟩ => ()

def updateChild (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (state : LocalState m children) (cache : ChildCache m children state)
    (e : EquationRef m) (value : CachedChild m children state e) : ChildCache m children state :=
  fun other => if same : equationName e.val = equationName other.val then
    have eq : e = other := Subtype.ext
      (equation_unique d.design d.wellFormed m hm e.val other.val e.property other.property same)
    eq ▸ value
  else cache other

/-! A snapshot is valid for its stored inputs, even when other parent values advance. -/
def evalCached (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) (values : Valuation m.ctx) (memories : Memories m.ctx)
    (connections : ConnectionValues m) (cache : ChildCache m children state)
    (driver : ValueDriver m node width) :
    {result : Value width × ChildCache m children state //
      result.1 = driver.eval m children state input values memories connections} := by
  cases driver with
  | inst i p n child inputs member port portMember dir bits =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    let result := cachedCycle (children e) (runners e) (state e) (connections e) (cache e)
    exact ⟨(cast (congrArg TyValue bits) (result.result.2 ⟨port, portMember, dir⟩),
      updateChild d m hm children state cache e (some ⟨connections e, result⟩)), by
        simp only [result.correct]
        rfl⟩
  | _ => exact ⟨(_, cache), rfl⟩

abbrev CycleCache (m : Typed.Module) (children : Children m) (state : LocalState m children) :=
  Std.DHashMap (ValueRef m.ctx) (fun ref => Value ref.width) × ChildCache m children state

def evalNode (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) (table : DriverTable m)
    (complete : ∀ node width (_v : ValueDriver m node width),
      (table.get? (node, width)).isSome)
    (cache : CycleCache m children state) (ref : ValueRef m.ctx) : CycleCache m children state :=
  let values := curryValues (fun ref => cache.1.getD ref 0)
  let memories := stateMemories m children state
  let result := evalCached d m hm children runners state input values memories
    (connectionValues d m hm values memories) cache.2 (indexedDriver d m hm table complete ref)
  (cache.1.insert ref result.val.1, result.val.2)

theorem evalNode_values (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) (table : DriverTable m)
    (complete : ∀ node width (_v : ValueDriver m node width),
      (table.get? (node, width)).isSome)
    (cache : CycleCache m children state) (ref : ValueRef m.ctx) :
    (evalNode d m hm children runners state input table complete cache ref).1 =
      cache.1.insert ref ((localSystem d m hm children state input).rhs
        (fun ref => cache.1.getD ref 0) ref) := by
  dsimp only [evalNode]
  rw [(evalCached ..).property, indexedDriver_eq]
  rfl

def cycleCache (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : CycleCache m children state :=
  let system := preparedSystem d m hm children state input
  let table := driverTable m (drivers m)
  let complete := fun node width (v : ValueDriver m node width) =>
    driverTable_total m (drivers m) v (driver_mem m v)
  ((valueRefs m.ctx).mergeSort (fun a b => system.rank a ≤ system.rank b)).foldl
    (evalNode d m hm children runners state input table complete)
    (∅, emptyChildren m children state)

theorem cycleCache_values (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : (cycleCache d m hm children runners state input).1 =
      orderedCache (preparedSystem d m hm children state input) (valueRefs m.ctx) := by
  have fold (nodes : List (ValueRef m.ctx)) (cache : CycleCache m children state) :
      (nodes.foldl (evalNode d m hm children runners state input (driverTable m (drivers m))
        (fun _ _ v => driverTable_total m (drivers m) v (driver_mem m v))) cache).1 =
      evaluate (localSystem d m hm children state input) nodes cache.1 := by
    induction nodes generalizing cache with
    | nil => rfl
    | cons node rest ih =>
      simp only [List.foldl_cons, ih, evaluate, evalNode_values]
      rfl
  unfold cycleCache orderedCache
  rw [preparedSystem_eq]
  exact fold _ _

def nextCached (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (values : Valuation m.ctx) (cache : ChildCache m children state) : LocalState m children :=
  let memories := stateMemories m children state
  let connections := connectionValues d m hm values memories
  fun e => match e with
  | ⟨.inst i p n child inputs, member⟩ =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    (cachedCycle (children e) (runners e) (state e) (connections e) (cache e)).result.1
  | ⟨.reg _ _ _ _ _ _ r _ _ x, _⟩ => nextRegister values memories r x
  | ⟨.mem i p n w size c t writes, h⟩ =>
    nextMemory values memories (state ⟨.mem i p n w size c t writes, h⟩) writes
  | ⟨.let_ .., _⟩ | ⟨.assign .., _⟩ => ()

theorem nextCached_eq (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (values : Valuation m.ctx) (cache : ChildCache m children state) :
    nextCached d m hm children runners state values cache =
      (localStepWithValues d m hm children state values).1 := by
  funext e
  obtain ⟨e, member⟩ := e
  cases e <;> try rfl
  rename_i i p n child inputs
  let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
  exact congrArg Prod.fst (cachedCycle (children e) (runners e) (state e)
    (connectionValues d m hm values (stateMemories m children state) e) (cache e)).correct

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

/-! Materialize state cells before the result exposes its state lookup function. -/
def cachedLocalStep (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (children : Children m) (runners : Runners m children) (state : LocalState m children)
    (input : Input m) : LocalState m children × Output m :=
  let cache := cycleCache d m hm children runners state input
  let values := curryValues (fun ref => cache.1.getD ref 0)
  letI := equationDecEq d m hm
  letI : Hashable (EquationRef m) := ⟨fun e => hash (equationName e.val)⟩
  let next := indexed (nextCached d m hm children runners state values cache.2)
    m.body.attach (fun e => List.mem_attach _ e)
  (next.get, outputValues d m hm values)

theorem cachedLocalStep_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (runners : Runners m children)
    (state : LocalState m children) (input : Input m) :
    cachedLocalStep d m hm children runners state input =
      localStepWithValues d m hm children state (localSolution d m hm children state input) := by
  simp only [cachedLocalStep, Table.get_eq, nextCached_eq]
  have values : curryValues
      (fun ref => (cycleCache d m hm children runners state input).1.getD ref 0) =
      localSolution d m hm children state input := by
    rw [cycleCache_values]
    exact orderedSolution_eq d m hm children state input
  rw [values]
  rfl

end Silicon.Core.Interp
