-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Decode
import Silicon.Core.Semantics.DriverUnique
import Silicon.Core.Semantics.InstanceRank
import Silicon.Core.Semantics.EquationSolution

/-!
The local equation system evaluates typed drivers with fixed state and input.
The checked rank order proves existence and uniqueness of its current-cycle values.
-/
namespace Silicon.Core.Semantics

structure ValueRef (ctx : Typed.Ctx) where
  node : Deps.Node
  width : Nat
  found : ctx.lookup node = some (.value (.bits width))

abbrev RefValues (ctx : Typed.Ctx) := (ref : ValueRef ctx) → Value ref.width

def curryValues (values : RefValues ctx) : Valuation ctx :=
  fun node width found => values ⟨node, width, found⟩

def uncurryValues (values : Valuation ctx) : RefValues ctx :=
  fun ref => values ref.node ref.width ref.found

def stateMemories (m : Typed.Module) (children : Children m)
    (state : LocalState m children) : Memories m.ctx :=
  fun name width depth found => (decodeMemory m name width depth found).eval m children state

theorem ValueDriver.eval_rank_congr (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) (a b : Valuation m.ctx) (memories : Memories m.ctx)
    (driver : ValueDriver m node width)
    (agree : ∀ dep width found, valueRank m dep < valueRank m node →
      a dep width found = b dep width found) :
    driver.eval m children state input a memories (connectionValues d m hm a memories) =
      driver.eval m children state input b memories (connectionValues d m hm b memories) := by
  cases driver with
  | input => rfl
  | reg => rfl
  | let_ index pos name width expr member =>
    apply evalExpr_congr
    intro dep read width found
    exact agree dep width found (let_read_rank m index pos name _ expr member dep read)
  | assign index pos name width target expr member =>
    apply evalExpr_congr
    intro dep read width found
    exact agree dep width found (assign_read_rank m index pos name _ target expr member dep read)
  | inst index pos name child inputs member port portMember dir bits =>
    apply congrArg (cast (congrArg TyValue bits))
    exact instance_out_congr d m hm index pos name child inputs member
      ⟨port, portMember, dir⟩ children state a b memories agree

def localSystem (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : EquationSolution.System (ValueRef m.ctx) (fun ref => Value ref.width) where
  initial := fun _ => 0
  rank := fun ref => valueRank m ref.node
  rhs := fun values ref =>
    let memories := stateMemories m children state
    (decodeValue d.design d.wellFormed m hm ref.node ref.width ref.found).eval
      m children state input (curryValues values) memories
      (connectionValues d m hm (curryValues values) memories)
  respects := by
    intro ref a b agree
    apply ValueDriver.eval_rank_congr
    intro dep width found lower
    exact agree ⟨dep, width, found⟩ lower

def localSolution (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : Valuation m.ctx :=
  curryValues (EquationSolution.solution (localSystem d m hm children state input))

/-! Every actual driver equation must hold, independently of the decoder's selection. -/
def IsLocalSolution (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) (values : Valuation m.ctx) : Prop :=
  ∀ node width found (driver : ValueDriver m node width),
    values node width found = driver.eval m children state input values
      (stateMemories m children state)
      (connectionValues d m hm values (stateMemories m children state))

theorem localSolution_isSolution (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : IsLocalSolution d m hm children state input
      (localSolution d m hm children state input) := by
  intro node width found driver
  have equation := EquationSolution.solution_eq (localSystem d m hm children state input)
    ⟨node, width, found⟩
  change _ = (decodeValue d.design d.wellFormed m hm node width found).eval _ _ _ _ _ _ _
    at equation
  rw [ValueDriver.unique d.design d.wellFormed m hm
    (decodeValue d.design d.wellFormed m hm node width found) driver] at equation
  exact equation

theorem local_solution_unique (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) :
    ∃ values, IsLocalSolution d m hm children state input values ∧
      ∀ other, IsLocalSolution d m hm children state input other → other = values := by
  refine ⟨localSolution d m hm children state input,
    localSolution_isSolution d m hm children state input, ?_⟩
  intro other solution
  have unique := EquationSolution.unique (localSystem d m hm children state input)
    (uncurryValues other) (by
      intro ref
      exact solution ref.node ref.width ref.found
        (decodeValue d.design d.wellFormed m hm ref.node ref.width ref.found))
  exact congrArg curryValues unique

end Silicon.Core.Semantics
