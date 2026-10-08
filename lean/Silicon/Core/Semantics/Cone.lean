import Silicon.Core.DepsReach
import Silicon.Core.Semantics.Drivers

/-! An output cone includes reachable values and all state leaves. -/
namespace Silicon.Core.Semantics

open GraphReach

def activeNodes (m : Core.Module) (children : String → Option Deps) : List Deps.Node :=
  (Deps.graph m children).map Prod.fst ++ (Deps.inputs m).map Deps.Node.name

def Cone (m : Core.Module) (children : String → Option Deps)
    (output node : Deps.Node) : Prop :=
  Reachable (Deps.graph m children) output node ∨ node ∉ activeNodes m children

private theorem graph_keys (m : Core.Module) (children : String → Option Deps) :
    (Deps.graph m children).map Prod.fst =
      (m.body.flatMap (Deps.equations children)).map Prod.fst := by
  simp [Deps.graph, List.map_map, Function.comp_def]

theorem cone_closed (m : Core.Module) (children : String → Option Deps)
    (unique : ((Deps.graph m children).map Prod.fst).Nodup)
    (output : Deps.Node) (row : Deps.Node × List Deps.Node)
    (member : row ∈ m.body.flatMap (Deps.equations children))
    (selected : Cone m children output row.1) (dep : Deps.Node) (read : dep ∈ row.2) :
    Cone m children output dep := by
  by_cases active : dep ∈ activeNodes m children
  · have source : row.1 ∈ activeNodes m children := by
      unfold activeNodes
      apply List.mem_append_left
      rw [graph_keys]
      exact List.mem_map.mpr ⟨row, member, rfl⟩
    have reach := selected.resolve_right (fun absent => absent source)
    apply Or.inl
    apply Reachable.trans _ reach
    apply Reachable.edge
    have entry : (row.1, row.2.filter (activeNodes m children).contains) ∈
        Deps.graph m children := by
      have same : activeNodes m children =
          (m.body.flatMap (Deps.equations children)).map Prod.fst ++
            (Deps.inputs m).map Deps.Node.name := by rw [activeNodes, graph_keys]
      rw [same]
      exact List.mem_map.mpr ⟨row, member, rfl⟩
    rw [Check.lookup_row_nodup _ _ _ unique entry]
    exact List.mem_filter.mpr ⟨read, List.contains_iff_mem.mpr active⟩
  · exact Or.inr active

theorem cone_self (m : Core.Module) (children : String → Option Deps) (output : Deps.Node) :
    Cone m children output output := Or.inl (Reachable.refl _ _)

theorem cone_input_reachable (m : Core.Module) (children : String → Option Deps)
    (output : Deps.Node) (input : String) (member : input ∈ Deps.inputs m)
    (selected : Cone m children output (.name input)) :
    Reachable (Deps.graph m children) output (.name input) := by
  apply selected.resolve_right
  intro absent
  exact absent (List.mem_append_right _ (List.mem_map.mpr ⟨input, member, rfl⟩))

theorem cone_input_inferred (m : Core.Module) (children : String → Option Deps)
    (output input : String) (deps : List String)
    (entry : (Deps.infer m children).lookup output = some deps)
    (member : input ∈ Deps.inputs m) (selected : Cone m children (.name output) (.name input)) :
    input ∈ deps := by
  exact (Deps.infer_lookup_inputs m children output deps entry input).mpr
    ⟨member, cone_input_reachable m children (.name output) input member selected⟩

theorem input_port_mem (m : Core.Module) (port : Port) (member : port ∈ m.ports)
    (dir : port.dir = .input) (bits : port.ty = .bits width) : port.name ∈ Deps.inputs m := by
  apply List.mem_filterMap.mpr
  exact ⟨port, member, by simp [dir, bits]⟩

theorem typed_graph_unique (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) :
    ((Deps.graph m.erase m.children).map Prod.fst).Nodup := by
  have children : m.children = Typed.designDeps d.erase (d.erase.items.length + 1) :=
    (d.environments m hm).2.1
  rw [children]
  exact Check.combinational_graph_keys_nodup d.erase m.erase wf.1 wf.2.1
    wf.2.2.2.2.2.1 (module_mem d m hm) _

end Silicon.Core.Semantics
