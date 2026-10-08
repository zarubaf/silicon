import Silicon.Core.Deps

/-! Graph reachability connects equation reads to inferred data-input dependencies. -/
namespace Silicon.Core.Deps

open GraphReach

theorem graph_read_reachable (m : Module) (children : String → Option Deps)
    (unique : ((graph m children).map Prod.fst).Nodup)
    (row : Node × List Node) (member : row ∈ m.body.flatMap (equations children))
    (dep : Node) (read : dep ∈ row.2)
    (active : dep ∈ (graph m children).map Prod.fst ∨
      ∃ input, IsInput m input ∧ dep = .name input) :
    GraphReach.Reachable (graph m children) row.1 dep := by
  obtain ⟨reads, entry, retained⟩ := graph_row m children row member
  apply GraphReach.Reachable.edge
  rw [lookup_row_nodup _ _ _ unique entry]
  exact (retained dep).mpr ⟨read, active⟩

theorem infer_lookup_inputs (m : Module) (children : String → Option Deps)
    (output : String) (deps : List String) (entry : (infer m children).lookup output = some deps)
    (input : String) :
    input ∈ deps ↔ IsInput m input ∧
      Reachable (graph m children) (.name output) (.name input) := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp entry
  apply infer_entry_inputs m children output deps ?_ input
  rw [he]
  exact List.mem_append_right _ (List.mem_cons_self ..)

end Silicon.Core.Deps
