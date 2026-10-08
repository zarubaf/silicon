import Silicon.Core.Semantics.Driver
import Silicon.Core.Semantics.Ownership

/-!
State and input leaves have rank zero. Equation ranks are one greater than the
checked graph ranks, so every expression read has a smaller semantic rank.
-/
namespace Silicon.Core.Semantics

def valueRank (m : Typed.Module) (node : Deps.Node) : Nat :=
  if node ∈ (Deps.graph m.erase m.children).map Prod.fst then Typed.rank m.ranks node + 1 else 0

private theorem graph_keys (m : Core.Module) (children : String → Option Deps) :
    (Deps.graph m children).map Prod.fst =
      (m.body.flatMap (Deps.equations children)).map Prod.fst := by
  simp [Deps.graph, List.map_map, Function.comp_def]

/-! An unfiltered equation read is either a state leaf or a checked graph edge. -/
theorem valueRank_read (m : Typed.Module) (row : Deps.Node × List Deps.Node)
    (member : row ∈ m.erase.body.flatMap (Deps.equations m.children))
    (dep : Deps.Node) (read : dep ∈ row.2) : valueRank m dep < valueRank m row.1 := by
  have own : row.1 ∈ (Deps.graph m.erase m.children).map Prod.fst := by
    rw [graph_keys]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  unfold valueRank
  rw [ite_eq_left own]
  split
  next active =>
    have equation : (row.1, row.2.filter fun node =>
      ((m.erase.body.flatMap (Deps.equations m.children)).map Prod.fst ++
        (Deps.inputs m.erase).map Deps.Node.name).contains node) ∈
      Deps.graph m.erase m.children := List.mem_map.mpr ⟨row, member, rfl⟩
    have edge : dep ∈ row.2.filter (fun node =>
        ((m.erase.body.flatMap (Deps.equations m.children)).map Prod.fst ++
          (Deps.inputs m.erase).map Deps.Node.name).contains node) := by
      apply List.mem_filter.mpr
      refine ⟨read, ?_⟩
      rw [List.contains_iff_mem]
      apply List.mem_append_left
      rwa [graph_keys] at active
    have less := m.acyclic _ equation dep edge
    dsimp only at less
    omega
  next => omega

theorem let_read_rank (m : Typed.Module) (index : Nat) (pos : Pos) (name : String)
    (width : Nat) (expr : Typed.Expr m.ctx (.bits width))
    (member : Typed.Equation.let_ index pos name width expr ∈ m.body)
    (dep : Deps.Node) (read : dep ∈ Deps.reads expr.erase) :
    valueRank m dep < valueRank m (.name name) := by
  apply valueRank_read m (.name name, Deps.reads expr.erase) _ dep read
  apply List.mem_flatMap.mpr
  refine ⟨Core.Stmt.let_ pos name width expr.erase, ?_, by simp [Deps.equations]⟩
  apply (Ownership.mem_equationsErase m.body _).mpr
  exact ⟨_, member, index, .let_ pos name width expr, by simp [Typed.Equation.parts], rfl⟩

theorem assign_read_rank (m : Typed.Module) (index : Nat) (pos : Pos) (name : String)
    (width : Nat) (target : Typed.valueTy m.ctx name = some (.bits width))
    (expr : Typed.Expr m.ctx (.bits width))
    (member : Typed.Equation.assign index pos name width target expr ∈ m.body)
    (dep : Deps.Node) (read : dep ∈ Deps.reads expr.erase) :
    valueRank m dep < valueRank m (.name name) := by
  apply valueRank_read m (.name name, Deps.reads expr.erase) _ dep read
  apply List.mem_flatMap.mpr
  refine ⟨Core.Stmt.assign pos name expr.erase, ?_, by simp [Deps.equations]⟩
  apply (Ownership.mem_equationsErase m.body _).mpr
  exact ⟨_, member, index, .assign pos name width target expr,
    by simp [Typed.Equation.parts], rfl⟩

end Silicon.Core.Semantics
