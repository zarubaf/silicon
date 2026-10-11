-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Connections
import Silicon.Core.Semantics.Rank

/-! Each declared child dependency lowers the parent's semantic value rank. -/
namespace Silicon.Core.Semantics

theorem instance_read_row (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (output : PortRef (m.interfaces child) .output)
    (input : PortRef (m.interfaces child) .input)
    (dependency : input.val.name ∈
      (((m.children child).getD []).lookup output.val.name).getD [])
    (node : Deps.Node)
    (read : node ∈ Deps.reads
      (connectionExpr d m hm index pos name child inputs hs input).erase) :
    ∃ reads, (Deps.Node.port name output.val.name, reads) ∈
      m.erase.body.flatMap (Deps.equations m.children) ∧ node ∈ reads := by
  cases hd : ((m.children child).getD []).lookup output.val.name with
  | none => simp [hd] at dependency
  | some deps =>
    have pair : List.Mem (output.val.name, deps) ((m.children child).getD []) := by
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hd
      rw [he]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    let raw := inputs.map (fun input => (input.1.val.name, input.2.erase))
    have member : Core.Stmt.inst pos name child raw ∈ m.erase.body := by
      apply (Ownership.mem_equationsErase m.body _).mpr
      exact ⟨_, hs, index, .inst pos name child inputs,
        by simp [Typed.Equation.parts], rfl⟩
    let reads := deps.flatMap fun input => (raw.lookup input).toList.flatMap Deps.reads
    have row : (Deps.Node.port name output.val.name, reads) ∈
        m.erase.body.flatMap (Deps.equations m.children) := by
      apply List.mem_flatMap.mpr
      refine ⟨.inst pos name child raw, member, ?_⟩
      exact List.mem_map.mpr ⟨(output.val.name, deps), pair, rfl⟩
    refine ⟨reads, row, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨input.val.name, by simpa [hd] using dependency, ?_⟩
    change node ∈ (List.lookup input.val.name raw).toList.flatMap Deps.reads
    rw [connectionExpr_lookup d m hm index pos name child inputs hs input]
    simpa using read

theorem instance_read_rank (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (output : PortRef (m.interfaces child) .output)
    (input : PortRef (m.interfaces child) .input)
    (dependency : input.val.name ∈
      (((m.children child).getD []).lookup output.val.name).getD [])
    (node : Deps.Node)
    (read : node ∈ Deps.reads
      (connectionExpr d m hm index pos name child inputs hs input).erase) :
    valueRank m node < valueRank m (.port name output.val.name) := by
  obtain ⟨reads, row, edge⟩ := instance_read_row d m hm index pos name child inputs hs
    output input dependency node read
  exact valueRank_read m _ row node edge

/-! Child contracts turn agreement on lower ranked parent values into output agreement. -/
theorem instance_out_congr (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (output : PortRef (m.interfaces child) .output)
    (children : Children m) (state : LocalState m children)
    (a b : Valuation m.ctx) (memories : Memories m.ctx)
    (agree : ∀ node width found, valueRank m node < valueRank m (.port name output.val.name) →
      a node width found = b node width found) :
    (children ⟨.inst index pos name child inputs, hs⟩).out
        (state ⟨.inst index pos name child inputs, hs⟩)
        (connectionValues d m hm a memories ⟨.inst index pos name child inputs, hs⟩) output =
      (children ⟨.inst index pos name child inputs, hs⟩).out
        (state ⟨.inst index pos name child inputs, hs⟩)
        (connectionValues d m hm b memories ⟨.inst index pos name child inputs, hs⟩) output := by
  apply (children ⟨.inst index pos name child inputs, hs⟩).out_respects
  intro input dependency
  apply connectionValues_congr
  intro node read width found
  apply agree
  exact instance_read_rank d m hm index pos name child inputs hs output input dependency node read

end Silicon.Core.Semantics
