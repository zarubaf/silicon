import Silicon.Core.GraphComponents
import Silicon.Core.GraphDFS
import Silicon.Core.GraphFlood
import Silicon.Core.GraphIndex

/-! Two depth-first passes assign a component label to every graph node. -/
namespace Silicon.Core.GraphCycleIndex

open GraphReach

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]

def certificate (g : List (α × List α)) (index : GraphIndex.Index α)
    (lookup : ∀ x, index[x]? = g.lookup x) : GraphSCC.Certificate g :=
  let nodes := GraphIndex.nodes g
  let forward := fun x => (index[x]?).getD []
  let reversed := GraphIndex.reverse index
  let backward := fun x => (reversed[x]?).getD []
  let order := GraphDFS.order forward nodes
  let fill := GraphFlood.fill backward (nodes.length + 1)
  let labels := GraphComponents.components fill order
  have edges : ∀ x y, y ∈ (g.lookup x).getD [] → x ∈ nodes ∧ y ∈ nodes :=
    GraphIndex.edge_nodes g
  have forward_eq : ∀ x, forward x = (g.lookup x).getD [] := by
    intro x
    simp only [forward, lookup]
  have ordered := GraphDFS.order_spec forward forward_eq
    (fun x _ y he => (edges x y he).2)
  have reverse_edges : Reverses g reversed.toList :=
    GraphIndex.reverses_of_lookup g index lookup
  have backward_eq : ∀ x, backward x = (reversed.toList.lookup x).getD [] := by
    intro x
    simp only [backward, GraphIndex.toList_lookup]
  have fill_spec : ∀ seen, GraphComponents.Closed g seen → ∀ root ∈ nodes,
      (∀ n, n ∈ (fill root seen).1 ↔
        seen.contains n = false ∧ Reachable g n root) ∧
      (∀ n, (fill root seen).2.contains n = true ↔
        seen.contains n = true ∨ n ∈ (fill root seen).1) := by
    intro seen closed root hroot
    have hs := GraphFlood.fill_spec backward backward_eq
      (fun x _ y he => (edges y x ((reverse_edges y x).mpr he)).1)
      seen (fun x y hx he => closed y x hx ((reverse_edges y x).mpr he)) root hroot
    refine ⟨?_, hs.2⟩
    intro n
    rw [hs.1 n, ← reachable_reverse_iff reverse_edges n root]
  have spec := GraphComponents.components_spec g nodes order edges ordered.2 fill fill_spec
    ordered.1
  ⟨GraphComponents.label labels, nodes, edges, spec.1, spec.2⟩

end Silicon.Core.GraphCycleIndex
