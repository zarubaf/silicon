import Silicon.Core.Semantics.Local
import Silicon.Core.Semantics.Cone

/-! Inputs outside an output's inferred dependencies cannot change that output's value. -/
namespace Silicon.Core.Semantics

def ValueEdge (m : Typed.Module) (node dep : Deps.Node) : Prop :=
  ∃ reads, (node, reads) ∈ m.erase.body.flatMap (Deps.equations m.children) ∧ dep ∈ reads

theorem ValueDriver.eval_deps_congr (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (ia ib : Input m) (a b : Valuation m.ctx) (memories : Memories m.ctx)
    (output : String) (deps : List String)
    (entry : (Deps.infer m.erase m.children).lookup output = some deps)
    (input_agree : ∀ port : PortRef m.ports .input,
      port.val.name ∈ deps → ia port = ib port)
    (driver : ValueDriver m node width)
    (selected : Cone m.erase m.children (.name output) node)
    (agree : ∀ dep width found, ValueEdge m node dep → a dep width found = b dep width found) :
    driver.eval m children state ia a memories (connectionValues d m hm a memories) =
      driver.eval m children state ib b memories (connectionValues d m hm b memories) := by
  cases driver with
  | input port member dir bits =>
    apply congrArg (cast (congrArg TyValue bits))
    apply input_agree
    exact cone_input_inferred m.erase m.children output port.name deps entry
      (input_port_mem m.erase port member dir bits) selected
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
    apply agree dep width found
    exact instance_read_row d m hm index pos name child inputs member
      ⟨port, portMember, dir⟩ input dependency dep read

/-! Dependency cones contain each unfiltered read of their equations. -/
theorem local_solution_cone (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (ia ib : Input m) (output : String) (deps : List String)
    (entry : (Deps.infer m.erase m.children).lookup output = some deps)
    (input_agree : ∀ port : PortRef m.ports .input,
      port.val.name ∈ deps → ia port = ib port)
    (ref : ValueRef m.ctx) (selected : Cone m.erase m.children (.name output) ref.node) :
    localSolution d m hm children state ia ref.node ref.width ref.found =
      localSolution d m hm children state ib ref.node ref.width ref.found := by
  apply EquationSolution.solution_agree_on
    (localSystem d m hm children state ia) (localSystem d m hm children state ib)
    (fun ref => Cone m.erase m.children (.name output) ref.node)
    (fun node dep => ValueEdge m node.node dep.node)
  · intro node dep edge
    obtain ⟨reads, row, read⟩ := edge
    exact valueRank_read m _ row dep.node read
  · intro node dep selected edge
    obtain ⟨reads, row, read⟩ := edge
    exact cone_closed m.erase m.children (typed_graph_unique d.design d.wellFormed m hm)
      (.name output) _ row selected dep.node read
  · intro node selected a b agree
    apply ValueDriver.eval_deps_congr d m hm children state ia ib
      (curryValues a) (curryValues b) (stateMemories m children state) output deps entry
      input_agree _ selected
    intro dep width found edge
    exact agree ⟨dep, width, found⟩ edge
  · exact selected

theorem output_infer_entry (m : Core.Module) (children : String → Option Deps)
    (output : PortRef m.ports .output) :
    ∃ deps, (Deps.infer m children).lookup output.val.name = some deps := by
  exact Deps.infer_output_entry m children output.val output.property.1 output.property.2

/-! Inferred dependencies suffice to determine each declared data output. -/
theorem local_deps_sound (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (ia ib : Input m) (output : PortRef m.ports .output) (width : Nat)
    (found : m.ctx.lookup (.name output.val.name) = some (.value (.bits width)))
    (input_agree : ∀ port : PortRef m.ports .input,
      port.val.name ∈ ((Deps.infer m.erase m.children).lookup output.val.name).getD [] →
        ia port = ib port) :
    localSolution d m hm children state ia (.name output.val.name) width found =
      localSolution d m hm children state ib (.name output.val.name) width found := by
  obtain ⟨deps, entry⟩ := output_infer_entry m.erase m.children output
  apply local_solution_cone d m hm children state ia ib output.val.name deps entry
    (fun port member => input_agree port (by simpa [entry] using member))
    ⟨.name output.val.name, width, found⟩
  exact cone_self m.erase m.children (.name output.val.name)

end Silicon.Core.Semantics
