import Silicon.Core.DepsReach
import Silicon.Core.Semantics.Drivers

/-! An output cone includes reachable values and all state leaves. -/
namespace Silicon.Core.Semantics

open GraphReach

def Active (m : Core.Module) (children : String → Option Deps) (node : Deps.Node) : Prop :=
  node ∈ (Deps.graph m children).map Prod.fst ∨
    ∃ input, Deps.IsInput m input ∧ node = .name input

def Cone (m : Core.Module) (children : String → Option Deps)
    (output node : Deps.Node) : Prop :=
  Reachable (Deps.graph m children) output node ∨ ¬ Active m children node

theorem cone_closed (m : Core.Module) (children : String → Option Deps)
    (unique : ((Deps.graph m children).map Prod.fst).Nodup)
    (output : Deps.Node) (row : Deps.Node × List Deps.Node)
    (member : row ∈ m.body.flatMap (Deps.equations children))
    (selected : Cone m children output row.1) (dep : Deps.Node) (read : dep ∈ row.2) :
    Cone m children output dep := by
  classical
  by_cases active : Active m children dep
  · have source : Active m children row.1 := by
      apply Or.inl
      rw [Deps.graph_keys]
      exact List.mem_map.mpr ⟨row, member, rfl⟩
    have reach := selected.resolve_right (fun absent => absent source)
    apply Or.inl
    apply Reachable.trans _ reach
    exact Deps.graph_read_reachable m children unique row member dep read active
  · exact Or.inr active

theorem cone_self (m : Core.Module) (children : String → Option Deps) (output : Deps.Node) :
    Cone m children output output := Or.inl (Reachable.refl _ _)

theorem cone_input_reachable (m : Core.Module) (children : String → Option Deps)
    (output : Deps.Node) (input : String) (member : Deps.IsInput m input)
    (selected : Cone m children output (.name input)) :
    Reachable (Deps.graph m children) output (.name input) := by
  apply selected.resolve_right
  intro absent
  exact absent (Or.inr ⟨input, member, rfl⟩)

theorem cone_input_inferred (m : Core.Module) (children : String → Option Deps)
    (output input : String) (deps : List String)
    (entry : (Deps.infer m children).lookup output = some deps)
    (member : Deps.IsInput m input) (selected : Cone m children (.name output) (.name input)) :
    input ∈ deps := by
  exact (Deps.infer_lookup_inputs m children output deps entry input).mpr
    ⟨member, cone_input_reachable m children (.name output) input member selected⟩

theorem input_port_mem (m : Core.Module) (port : Port) (member : port ∈ m.ports)
    (dir : port.dir = .input) (bits : port.ty = .bits width) : Deps.IsInput m port.name :=
  ⟨port, member, rfl, dir, width, bits⟩

theorem typed_graph_unique (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) :
    ((Deps.graph m.erase m.children).map Prod.fst).Nodup := by
  have children : m.children = Typed.designDeps d.erase d.erase.depsFuel :=
    (d.environments m hm).2.1
  rw [children]
  exact Check.combinational_graph_keys_nodup d.erase m.erase wf.1 wf.2.1
    wf.2.2.2.2.2.1 (module_mem d m hm) _

end Silicon.Core.Semantics
