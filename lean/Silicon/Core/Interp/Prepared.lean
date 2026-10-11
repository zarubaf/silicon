-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Interp.Values
import Silicon.Core.Semantics.Step
import Silicon.Core.GraphFlood
import Silicon.Core.GraphIndex

/-! Module preparation stores ordered drivers and one ordered cone for each output. -/
namespace Silicon.Core.Interp

open Semantics

/-! One preparation supplies the ordered nodes and their driver index. -/
structure OrderedValues (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies) where
  nodes : List (ValueRef m.ctx)
  complete : ∀ ref, ref ∈ nodes
  sorted : nodes.Pairwise (fun a b => valueRank m a.node ≤ valueRank m b.node)
  rank : ValueRef m.ctx → Nat
  rank_eq : ∀ ref, rank ref = valueRank m ref.node
  drivers : DriverTable m
  total : ∀ node width (_v : ValueDriver m node width), (drivers.get? (node, width)).isSome

def prepareValues (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (graph : List (Deps.Node × List Deps.Node)) (graph_eq : graph = Deps.graph m.erase m.children) :
    OrderedValues d m hm :=
  let active := graph.map Prod.fst
  let ranks := indexed (fun ref : ValueRef m.ctx => valueRankWith m.ranks active ref.node)
    (valueRefs m.ctx) valueRefs_complete
  { nodes := (valueRefs m.ctx).mergeSort (fun a b => ranks.get a ≤ ranks.get b)
    complete := fun ref => List.mem_mergeSort.mpr (valueRefs_complete ref)
    sorted := by
      simp only [Table.get_eq, active, graph_eq]
      have sorted := List.pairwise_mergeSort
        (le := fun a b : ValueRef m.ctx => decide (valueRank m a.node ≤ valueRank m b.node))
        (by intros; simp_all; omega) (by intros; simp; omega) (valueRefs m.ctx)
      exact sorted.imp (fun h => of_decide_eq_true h)
    rank := ranks.get
    rank_eq := by intro ref; simp [active, graph_eq, valueRank]
    drivers := driverTable m (drivers m)
    total := fun _ _ v => driverTable_total m (drivers m) v (driver_mem m v) }

/-! Every cone search shares the graph index and its finite node bound. -/
structure ConeGraph (m : Typed.Module) where
  graph : List (Deps.Node × List Deps.Node)
  graph_eq : graph = Deps.graph m.erase m.children
  nodes : List Deps.Node
  nodes_eq : nodes = GraphIndex.nodes graph
  nodeCount : Nat
  nodeCount_eq : nodeCount = nodes.length
  edges : Std.HashMap Deps.Node (List Deps.Node)
  edges_eq : ∀ node, edges[node]? = graph.lookup node
  active : Std.HashSet Deps.Node
  active_eq : ∀ node, active.contains node = true ↔ Active m.erase m.children node

def reachableNodes (g : ConeGraph m) (root : Deps.Node) :
    {seen : Std.HashSet Deps.Node //
      ∀ node, seen.contains node = true ↔ GraphReach.Reachable g.graph root node} := by
  let nodes := root :: g.nodes
  let edges := fun node : Deps.Node => (g.edges[node]?).getD []
  let result := GraphFlood.fill edges (g.nodeCount + 2) root ∅
  have spec := GraphFlood.fill_spec (g := g.graph) (nodes := nodes) edges
    (fun node => by simp [edges, g.edges_eq])
    (fun x _ y edge => List.mem_cons_of_mem _ (by
      rw [g.nodes_eq]; exact (GraphIndex.edge_nodes g.graph x y edge).2))
    ∅ (by simp) root (List.mem_cons_self ..)
  refine ⟨result.2, ?_⟩
  intro node
  change (GraphFlood.fill edges (g.nodeCount + 2) root ∅).2.contains node = true ↔ _
  rw [g.nodeCount_eq]
  change (GraphFlood.fill edges (nodes.length + 1) root ∅).2.contains node = true ↔ _
  rw [spec.2 node, spec.1 node]
  simp

structure PortCone (m : Typed.Module) (port : PortRef m.ports .output) where
  contains : Deps.Node → Bool
  spec : ∀ node, contains node = true ↔ Cone m.erase m.children (.name port.val.name) node
  nodes : List (ValueRef m.ctx)
  sorted : nodes.Pairwise (fun a b => valueRank m a.node ≤ valueRank m b.node)
  complete : ∀ ref, contains ref.node = true → ref ∈ nodes

def prepareCone (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (ordered : OrderedValues d m hm) (graph : ConeGraph m)
    (refs : Std.DHashMap Deps.Node (fun _ => Option (ValueRef m.ctx)))
    (refs_eq : ∀ ref : ValueRef m.ctx, (refs.get? ref.node).getD none = some ref)
    (inactive : List (ValueRef m.ctx))
    (inactive_eq : ∀ ref, ref ∈ inactive ↔ graph.active.contains ref.node = false)
    (port : PortRef m.ports .output) : PortCone m port := by
  let reachable := reachableNodes graph (.name port.val.name)
  let selected := fun node => reachable.val.contains node || !graph.active.contains node
  let reached := reachable.val.toList.filterMap (fun node => (refs.get? node).getD none)
  let nodes := (reached ++ inactive).mergeSort (fun a b => ordered.rank a ≤ ordered.rank b)
  refine ⟨selected, ?_, nodes, ?_, ?_⟩
  · intro node
    simp [selected, reachable.property, Cone, ← graph.active_eq, graph.graph_eq]
  · have sorted := List.pairwise_mergeSort
      (le := fun a b : ValueRef m.ctx => decide (ordered.rank a ≤ ordered.rank b))
      (by intros; simp_all; omega) (by intros; simp; omega) (reached ++ inactive)
    exact sorted.imp (fun h => by simpa only [ordered.rank_eq] using of_decide_eq_true h)
  · intro ref hs
    apply List.mem_mergeSort.mpr
    simp only [selected, Bool.or_eq_true_iff] at hs
    rcases hs with hr | hi
    · apply List.mem_append_left
      exact List.mem_filterMap.mpr ⟨ref.node,
        by simpa using hr, refs_eq ref⟩
    · exact List.mem_append_right _ ((inactive_eq ref).mpr (by simpa using hi))

structure Prepared (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    extends OrderedValues d m hm where
  cones : (port : PortRef m.ports .output) → PortCone m port

def prepare (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    Prepared d m hm := by
  let graph := Deps.graph m.erase m.children
  let ordered := prepareValues d m hm graph rfl
  let active := graph.map Prod.fst ++
    m.ports.filterMap (fun p => match p.dir, p.ty with
      | .input, .bits _ => some (Deps.Node.name p.name)
      | _, _ => none)
  have active_eq (node) : node ∈ active ↔ Active m.erase m.children node := by
    simp only [active, List.mem_append, List.mem_filterMap]
    constructor
    · rintro (h | ⟨p, hp, he⟩)
      · exact Or.inl h
      · cases hd : p.dir <;> cases ht : p.ty <;> simp [hd, ht] at he
        next width =>
          subst node
          exact Or.inr ⟨p.name, ⟨p, hp, rfl, hd, width, ht⟩, rfl⟩
    · rintro (h | ⟨name, ⟨p, hp, hn, hd, w, ht⟩, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, hp, by simp [hd, ht, hn]⟩
  letI : BEq (PortRef m.ports .output) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (PortRef m.ports .output) := { eq_of_beq := by simp, rfl := by simp }
  letI : Hashable (PortRef m.ports .output) := ⟨fun p => hash p.val.name⟩
  let ports : List (PortRef m.ports .output) := m.ports.attach.filterMap fun p =>
    if dir : p.val.dir = .output then some ⟨p.val, p.property, dir⟩ else none
  let nodes := GraphIndex.nodes graph
  let indexedGraph : ConeGraph m := ⟨graph, rfl, nodes, rfl, nodes.length, rfl,
    firstIndex graph, firstIndex_lookup graph, Std.HashSet.ofList active, by
      intro node
      simpa only [Std.HashSet.contains_ofList, List.contains_iff_mem] using active_eq node⟩
  let refs := valueRefIndex m.ctx
  let inactive := ordered.nodes.filter (fun ref => !indexedGraph.active.contains ref.node)
  let cones := indexed (prepareCone d m hm ordered indexedGraph refs valueRefIndex_get
    inactive (by intro ref; simp [inactive, ordered.complete ref])) ports (by
    intro p
    apply List.mem_filterMap.mpr
    exact ⟨⟨p.val, p.property.1⟩, List.mem_attach _ _, by simp [p.property.2]⟩)
  exact ⟨ordered, cones.get⟩

end Silicon.Core.Interp
