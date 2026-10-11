-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.GraphComponents
import Silicon.Core.GraphDFSLoop
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

/-! The loop forms of both searches give the same labels with constant native stack depth. -/
private def loopLabels (g : List (α × List α)) (index : GraphIndex.Index α) :
    GraphComponents.Labels α :=
  let nodes := GraphIndex.nodes g
  let forward := fun x => (index[x]?).getD []
  let reversed := GraphIndex.reverse index
  let backward := fun x => (reversed[x]?).getD []
  let space := (Std.HashSet.ofList nodes).toList
  let forwardWeight := (space.map fun x => (forward x).length + 2).sum
  let backwardWeight := (space.map fun x => (backward x).length + 2).sum
  let order := GraphDFS.orderLoop forward nodes (nodes.length + 1 + forwardWeight)
  let fill := fun root seen => GraphDFS.fillLoop backward (nodes.length + 1) root seen
    (backwardWeight + (backward root).length + 4)
  GraphComponents.components fill order

private theorem loopLabels_eq (g : List (α × List α)) (index : GraphIndex.Index α)
    (lookup : ∀ x, index[x]? = g.lookup x) :
    GraphComponents.label (loopLabels g index) = (certificate g index lookup).label := by
  let nodes := GraphIndex.nodes g
  let forward := fun (x : α) => (index[x]?).getD []
  let reversed := GraphIndex.reverse index
  let backward := fun (x : α) => (reversed[x]?).getD []
  let space := (Std.HashSet.ofList nodes).toList
  have inSpace : ∀ x ∈ nodes, x ∈ space := by
    intro x hx
    simpa [space, Std.HashSet.mem_iff_contains, Std.HashSet.contains_ofList] using hx
  have edges : ∀ x y, y ∈ (g.lookup x).getD [] → x ∈ nodes ∧ y ∈ nodes :=
    GraphIndex.edge_nodes g
  have reverse_edges : Reverses g reversed.toList :=
    GraphIndex.reverses_of_lookup g index lookup
  have orderEq := GraphDFS.orderLoop_eq forward nodes space
    (fun x y hy => inSpace y (edges x y (by simpa only [forward, lookup] using hy)).2)
    inSpace _ (Nat.le_refl _)
  have fillEq : (fun root seen => GraphDFS.fillLoop backward (nodes.length + 1) root seen
      ((space.map fun x => (backward x).length + 2).sum + (backward root).length + 4)) =
      GraphFlood.fill backward (nodes.length + 1) := by
    funext root seen
    apply GraphDFS.fillLoop_eq backward space ?_ _ root seen _ (Nat.le_refl _)
    intro x y hy
    have hy : y ∈ (reversed.toList.lookup x).getD [] := by
      simpa only [backward, GraphIndex.toList_lookup] using hy
    exact inSpace y (edges y x ((reverse_edges y x).mpr hy)).1
  unfold loopLabels
  dsimp only
  rw [orderEq, fillEq]
  rfl

private def loopCertificate (g : List (α × List α)) (index : GraphIndex.Index α)
    (lookup : ∀ x, index[x]? = g.lookup x) : GraphSCC.Certificate g :=
  have same := loopLabels_eq g index lookup
  ⟨GraphComponents.label (loopLabels g index), GraphIndex.nodes g, GraphIndex.edge_nodes g,
    same ▸ (certificate g index lookup).edge_order,
    same ▸ (certificate g index lookup).connected⟩

omit [LawfulBEq α] [Hashable α] [LawfulHashable α] in
private theorem certificate_ext {g : List (α × List α)} {c d : GraphSCC.Certificate g}
    (labels : c.label = d.label) (nodes : c.nodes = d.nodes) : c = d := by
  cases c
  cases d
  simp only at labels nodes
  subst labels nodes
  rfl

private theorem loopCertificate_label (g : List (α × List α)) (index : GraphIndex.Index α)
    (lookup : ∀ x, index[x]? = g.lookup x) :
    (loopCertificate g index lookup).label = GraphComponents.label (loopLabels g index) := by
  unfold loopCertificate
  rfl

private theorem loopCertificate_nodes (g : List (α × List α)) (index : GraphIndex.Index α)
    (lookup : ∀ x, index[x]? = g.lookup x) :
    (loopCertificate g index lookup).nodes = GraphIndex.nodes g := by
  unfold loopCertificate
  rfl

private theorem certificate_nodes (g : List (α × List α)) (index : GraphIndex.Index α)
    (lookup : ∀ x, index[x]? = g.lookup x) :
    (certificate g index lookup).nodes = GraphIndex.nodes g := by
  unfold certificate
  rfl

@[csimp] private theorem certificate_loop : @certificate = @loopCertificate := by
  funext α _ _ _ _ g index lookup
  apply certificate_ext
  · rw [loopCertificate_label]
    exact (loopLabels_eq g index lookup).symm
  · rw [loopCertificate_nodes, certificate_nodes]

end Silicon.Core.GraphCycleIndex
