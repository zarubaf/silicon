import Silicon.Core.Semantics.Driver
import Silicon.Core.Semantics.Ownership

/-!
State and input leaves have rank zero. Equation ranks are one greater than the
checked graph ranks, so every expression read has a smaller semantic rank.
-/
namespace Silicon.Core.Semantics

abbrev valueRankWith (ranks : List (Deps.Node × Nat)) (active : List Deps.Node)
    (node : Deps.Node) : Nat :=
  if node ∈ active then Typed.rank ranks node + 1 else 0

def valueRank (m : Typed.Module) (node : Deps.Node) : Nat :=
  valueRankWith m.ranks ((Deps.graph m.erase m.children).map Prod.fst) node

/-! An unfiltered equation read is either a state leaf or a checked graph edge. -/
theorem valueRank_read (m : Typed.Module) (row : Deps.Node × List Deps.Node)
    (member : row ∈ m.erase.body.flatMap (Deps.equations m.children))
    (dep : Deps.Node) (read : dep ∈ row.2) : valueRank m dep < valueRank m row.1 := by
  have own : row.1 ∈ (Deps.graph m.erase m.children).map Prod.fst := by
    rw [Deps.graph_keys]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  unfold valueRank valueRankWith
  rw [ite_eq_left own]
  split
  next active =>
    obtain ⟨reads, equation, retained⟩ := Deps.graph_row m.erase m.children row member
    have edge : dep ∈ reads := (retained dep).mpr ⟨read, Or.inl active⟩
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
