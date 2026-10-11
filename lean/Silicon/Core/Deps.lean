-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Syntax
import Silicon.Core.GraphReach
import Silicon.Core.Index
import Silicon.Core.List
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
Port dependencies describe input reads in the current cycle.
The graph retains all operand reads. It does not simplify expressions.
-/
namespace Silicon.Core

/-! Outputs and their input lists follow port order. -/
def Deps := List (String × List String)
  deriving Repr, BEq, DecidableEq

namespace Deps

/-! Instance outputs have distinct nodes for each port. -/
inductive Node where
  | name (value : String)
  | port (inst output : String)
  deriving Repr, DecidableEq, BEq

deriving instance ReflBEq, LawfulBEq for Node

instance : Hashable Node where
  hash n := match n with
    | .name s => hash ((s, none) : String × Option String)
    | .port i p => hash ((i, some p) : String × Option String)

instance : LawfulHashable Node :=
  ⟨by intro a b h; exact congrArg hash (eq_of_beq h)⟩

/-! Memory contents come from state. Only the address contributes reads. -/
def reads : Expr → List Node
  | .ref _ n => [.name n]
  | .port _ i p => [.port i p]
  | .const .. => []
  | .un _ _ a | .extract _ a _ _ | .replicate _ a _ | .read _ _ a => reads a
  | .bin _ _ a b | .icmp _ _ a b => reads a ++ reads b
  | .mux _ c a b => reads c ++ reads a ++ reads b

def equations (children : String → Option Deps) : Stmt → List (Node × List Node)
  | .let_ _ n _ e | .assign _ n e => [(.name n, reads e)]
  | .inst _ n child inputs =>
    ((children child).getD []).map fun (output, deps) =>
      (.port n output, deps.flatMap fun input =>
        ((inputs.lookup input).toList.flatMap reads))
  | _ => []

private def inputs (m : Module) : List String :=
  m.ports.filterMap fun p => match p.dir, p.ty with
    | .input, .bits _ => some p.name
    | _, _ => none

/-! Only data input ports can contribute current-cycle dependencies. -/
def IsInput (m : Module) (name : String) : Prop :=
  ∃ port ∈ m.ports, port.name = name ∧ port.dir = .input ∧ ∃ width, port.ty = .bits width

private theorem mem_inputs (m : Module) (name : String) :
    name ∈ inputs m ↔ IsInput m name := by
  simp only [inputs, List.mem_filterMap, IsInput]
  constructor
  · rintro ⟨port, member, found⟩
    cases hd : port.dir <;> cases ht : port.ty <;> simp_all
    exact ⟨port, member, found, hd, _, ht⟩
  · rintro ⟨port, member, rfl, dir, width, bits⟩
    exact ⟨port, member, by simp [dir, bits]⟩

/-!
Each entry lists the direct reads of its node, including input leaves.
Register reads and clocks make no edge. State updates make no equation.
The checker must resolve names and child contracts before it uses this graph.
Missing child contracts supply no equations here.
-/
def graph (m : Module) (children : String → Option Deps) : List (Node × List Node) :=
  let eqs := m.body.flatMap (equations children)
  let nodes := eqs.map Prod.fst ++ (inputs m).map Node.name
  eqs.map fun (n, rs) => (n, rs.filter fun node => nodes.contains node)

theorem graph_keys (m : Module) (children : String → Option Deps) :
    (graph m children).map Prod.fst =
      (m.body.flatMap (equations children)).map Prod.fst := by
  simp [graph, List.map_map, Function.comp_def]

/-! Graph rows retain exactly equation and data-input reads. -/
theorem graph_row (m : Module) (children : String → Option Deps)
    (row : Node × List Node) (member : row ∈ m.body.flatMap (equations children)) :
    ∃ reads, (row.1, reads) ∈ graph m children ∧ ∀ dep,
      dep ∈ reads ↔ dep ∈ row.2 ∧
        (dep ∈ (graph m children).map Prod.fst ∨
          ∃ input, IsInput m input ∧ dep = .name input) := by
  refine ⟨_, List.mem_map.mpr ⟨row, member, rfl⟩, ?_⟩
  intro dep
  simp only [List.mem_filter, List.contains_iff_mem, List.mem_append, graph_keys,
    List.mem_map, mem_inputs]
  simp only [eq_comm]

private def indexedGraph (m : Module) (children : String → Option Deps) :
    List (Node × List Node) :=
  let eqs := m.body.flatMap (equations children)
  let nodes := Std.HashSet.ofList (eqs.map Prod.fst ++ (inputs m).map Node.name)
  eqs.map fun (n, rs) => (n, rs.filter fun node => nodes.contains node)

@[csimp] private theorem graph_indexed : graph = indexedGraph := by
  funext m children
  simp only [graph, indexedGraph, Std.HashSet.contains_ofList]

/-!
A search visits each node at most once. The bound covers every path to an input leaf.
Cycles terminate and keep all reachable inputs. The checker rejects cycles separately.
-/
private def visit (g : List (Node × List Node)) : Nat → List Node → List Node → List Node
  | 0, _, seen => seen
  | fuel + 1, pending, seen =>
    let fresh := pending.foldl (fun acc n =>
      if seen.contains n || acc.contains n then acc else n :: acc) []
    let seen := fresh ++ seen
    let next := fresh.flatMap fun n => (g.lookup n).getD []
    let next := next.filter fun n => !seen.contains n
    if next.isEmpty then seen else visit g fuel next seen

/-!
A path to an input uses at most one edge per equation before it reaches that input.
One extra search step visits the final input. Port filtering removes repeated reads.
-/
def infer (m : Module) (children : String → Option Deps) : Deps :=
  let g := graph m children
  m.ports.filterMap fun p =>
    if p.dir == .output then
      let reached := visit g (g.length + 1) [.name p.name] []
      some (p.name, (inputs m).filter fun n => reached.contains (.name n))
    else none

open GraphReach

private theorem reaches_empty (g : List (Node × List Node)) (target : Node)
    (fuel : Nat) (seen : List Node) : reachesSpec g target fuel [] seen = false := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [reachesSpec, freshNodes] using ih

private theorem visit_mem (g : List (Node × List Node)) (fuel : Nat)
    (pending seen : List Node) (target : Node) :
    target ∈ visit g fuel pending seen ↔
      target ∈ seen ∨ reachesSpec g target fuel pending seen = true := by
  induction fuel generalizing pending seen with
  | zero => simp [visit, reachesSpec]
  | succ fuel ih =>
    change target ∈ (if (frontier g seen pending).isEmpty then updated seen pending
      else visit g fuel (frontier g seen pending) (updated seen pending)) ↔ _
    rw [reachesSpec]
    change _ ↔ target ∈ seen ∨ (if pending.contains target then true
      else reachesSpec g target fuel (frontier g seen pending) (updated seen pending)) = true
    by_cases he : (frontier g seen pending).isEmpty = true
    · have hn : frontier g seen pending = [] := List.isEmpty_iff.mp he
      rw [ite_eq_left he, mem_updated, hn, reaches_empty]
      simp
    · rw [ite_eq_right he, ih, mem_updated]
      by_cases hp : target ∈ pending <;> simp [hp]

private theorem mem_visit_iff_reachable (g : List (Node × List Node))
    (pending : List Node) (target : Node) :
    target ∈ visit g (g.length + 1) pending [] ↔
      ∃ start ∈ pending, Reachable g start target := by
  rw [visit_mem]
  simpa using reaches_graph_iff g target pending

theorem infer_entry_inputs (m : Module) (children : String → Option Deps)
    (output : String) (deps : List String) (entry : List.Mem (output, deps) (infer m children))
    (input : String) :
    input ∈ deps ↔ IsInput m input ∧
      Reachable (graph m children) (.name output) (.name input) := by
  obtain ⟨port, _, hp⟩ := List.mem_filterMap.mp entry
  split at hp
  · have he := Option.some.inj hp
    have hn := congrArg Prod.fst he
    have hd := congrArg Prod.snd he
    simp only at hn hd
    rw [← hd, List.mem_filter, List.contains_iff_mem, mem_visit_iff_reachable]
    simp [hn, mem_inputs]
  · contradiction

theorem infer_output_entry (m : Module) (children : String → Option Deps)
    (port : Port) (member : port ∈ m.ports) (dir : port.dir = .output) :
    ∃ deps, (infer m children).lookup port.name = some deps := by
  have total : ((infer m children).lookup port.name).isSome := by
    apply List.lookup_isSome_iff.mpr
    let g := graph m children
    let reached := visit g (g.length + 1) [.name port.name] []
    let deps := (inputs m).filter fun name => reached.contains (.name name)
    refine ⟨(port.name, deps), ?_, by simp⟩
    apply List.mem_filterMap.mpr
    exact ⟨port, member, by simp [dir, deps, reached, g]⟩
  cases found : (infer m children).lookup port.name with
  | none => simp [found] at total
  | some deps => exact ⟨deps, rfl⟩

theorem graph_perm (m m' : Module) (children children' : String → Option Deps)
    (ports : m.ports = m'.ports)
    (equationsPerm : (m.body.flatMap (equations children)).Perm
      (m'.body.flatMap (equations children'))) :
    (graph m children).Perm (graph m' children') := by
  have nodes := (equationsPerm.map Prod.fst).append_right ((inputs m).map Node.name)
  have inputEq : inputs m = inputs m' := by simp only [inputs, ports]
  rw [inputEq] at nodes
  unfold graph
  rw [inputEq]
  simpa only [nodes.contains_eq] using equationsPerm.map (fun row =>
    (row.1, row.2.filter fun node =>
      ((m'.body.flatMap (equations children')).map Prod.fst ++
        (inputs m').map Node.name).contains node))

/-! Dependency search depends on named graph lookups, not row order. -/
theorem infer_graph_congr (m m' : Module) (children children' : String → Option Deps)
    (ports : m.ports = m'.ports)
    (size : (graph m children).length = (graph m' children').length)
    (lookup : ∀ n, (graph m children).lookup n = (graph m' children').lookup n) :
    infer m children = infer m' children' := by
  have visits : ∀ fuel pending seen,
      visit (graph m children) fuel pending seen =
        visit (graph m' children') fuel pending seen := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro pending seen
      simp only [visit, lookup, ih]
  simp only [infer, visits, size, inputs, ports]
  rfl

/-! Hash sets keep each search linear in the nodes and edges that it reaches. -/
private def indexedFresh (seen : Std.HashSet Node) (pending : List Node) :
    Std.HashSet Node × List Node :=
  pending.foldl (fun (seen, fresh) n =>
    if seen.contains n then (seen, fresh) else (seen.insert n, n :: fresh)) (seen, [])

private def indexedVisit (g : Std.HashMap Node (List Node)) :
    Nat → List Node → Std.HashSet Node → Std.HashSet Node
  | 0, _, seen => seen
  | fuel + 1, pending, seen =>
    let (seen, fresh) := indexedFresh seen pending
    let next := (fresh.flatMap fun n => (g[n]?).getD []).filter fun n => !seen.contains n
    if next.isEmpty then seen else indexedVisit g fuel next seen

private theorem indexedFresh_foldl (pending fresh : List Node) (seen : Std.HashSet Node)
    (x : Node) :
    let out := pending.foldl (fun (seen, fresh) n =>
      if seen.contains n then (seen, fresh) else (seen.insert n, n :: fresh)) (seen, fresh)
    (out.1.contains x = true ↔ seen.contains x = true ∨ x ∈ pending) ∧
      (x ∈ out.2 ↔ x ∈ fresh ∨ x ∈ pending ∧ seen.contains x = false) := by
  induction pending generalizing seen fresh with
  | nil => simp
  | cons n pending ih =>
    simp only [List.foldl_cons]
    by_cases hn : seen.contains n = true
    · simp only [hn, ite_true]
      refine ⟨by rw [(ih fresh seen).1]; grind, ?_⟩
      rw [(ih fresh seen).2]
      grind
    · simp only [hn, Bool.false_eq_true, ite_false]
      refine ⟨?_, ?_⟩
      · rw [(ih (n :: fresh) (seen.insert n)).1, Std.HashSet.contains_insert]
        grind
      · rw [(ih (n :: fresh) (seen.insert n)).2, Std.HashSet.contains_insert]
        grind

private theorem indexedVisit_contains (g : List (Node × List Node)) (fuel : Nat)
    (pending pending' seen : List Node) (index : Std.HashSet Node)
    (hp : ∀ x, x ∈ pending' ↔ x ∈ pending)
    (hs : ∀ x, index.contains x = true ↔ x ∈ seen) (x : Node) :
    (indexedVisit (firstIndex g) fuel pending' index).contains x = true ↔
      x ∈ visit g fuel pending seen := by
  induction fuel generalizing pending pending' seen index with
  | zero => simpa [indexedVisit, visit] using hs x
  | succ fuel ih =>
    have fresh := fun y => indexedFresh_foldl pending' [] index y
    simp only [List.not_mem_nil, false_or] at fresh
    have seen' : ∀ y, (indexedFresh index pending').1.contains y = true ↔
        y ∈ updated seen pending := by
      intro y
      rw [indexedFresh, (fresh y).1, mem_updated, hs, hp]
    have next : ∀ y, y ∈ ((indexedFresh index pending').2.flatMap
        fun n => ((firstIndex g)[n]?).getD []).filter
          (fun n => !(indexedFresh index pending').1.contains n) ↔
        y ∈ frontier g seen pending := by
      intro y
      simp only [frontier, List.mem_filter, List.mem_flatMap, mem_fresh, firstIndex_lookup,
        Bool.not_eq_true', List.not_mem_nil, false_or]
      rw [show ((indexedFresh index pending').1.contains y = false) ↔
          ((updated seen pending).contains y = false) by
        rw [← Bool.not_eq_true, ← Bool.not_eq_true, seen' y, List.contains_iff_mem]]
      constructor
      · rintro ⟨⟨n, hn, hy⟩, hu⟩
        rw [indexedFresh, (fresh n).2, hp, ← Bool.not_eq_true, hs] at hn
        exact ⟨⟨n, hn, hy⟩, hu⟩
      · rintro ⟨⟨n, hn, hy⟩, hu⟩
        refine ⟨⟨n, ?_, hy⟩, hu⟩
        rw [indexedFresh, (fresh n).2, hp, ← Bool.not_eq_true, hs]
        exact hn
    change (indexedVisit (firstIndex g) (fuel + 1) pending' index).contains x = true ↔
      x ∈ (if (frontier g seen pending).isEmpty then updated seen pending
        else visit g fuel (frontier g seen pending) (updated seen pending))
    simp only [indexedVisit]
    have empty : (((indexedFresh index pending').2.flatMap
        fun n => ((firstIndex g)[n]?).getD []).filter
          (fun n => !(indexedFresh index pending').1.contains n)).isEmpty =
        (frontier g seen pending).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem, next]
    rw [empty]
    split
    · exact seen' x
    · exact ih _ _ _ _ next seen'

private theorem zipIdx_ordered (xs : List String) (k : Nat) :
    (xs.zipIdx k).Pairwise fun a b => a.2 < b.2 := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.pairwise_cons]
    exact ⟨fun b hb => List.le_snd_of_mem_zipIdx hb, ih (k + 1)⟩

/-! Sorted input positions avoid a scan of all inputs for each output. -/
private def reachedInputs (positions : Std.HashMap String (List (String × Nat)))
    (reached : Std.HashSet Node) : List String :=
  let found := reached.toList.flatMap fun node => match node with
    | .name n => (positions[n]?).getD []
    | .port .. => []
  (found.mergeSort fun a b => a.2 ≤ b.2).map Prod.fst

private theorem reachedInputs_eq (xs : List String) (reached : Std.HashSet Node) :
    reachedInputs (groupIndex (xs.zipIdx.map fun e => (e.1, e))) reached =
      xs.filter fun n => reached.contains (.name n) := by
  have positions : ∀ n, ((groupIndex (xs.zipIdx.map fun e => (e.1, e)))[n]?).getD [] =
      xs.zipIdx.filter (·.1 == n) := by
    intro n
    rw [groupIndex_values, List.filterMap_map, ← List.filterMap_eq_filter]
    congr 1
  have spec : (xs.filter fun n => reached.contains (.name n)) =
      (xs.zipIdx.filter fun e => reached.contains (.name e.1)).map Prod.fst := by
    conv => lhs; rw [← List.zipIdx_map_fst 0 xs]
    rw [List.filter_map]
    rfl
  have ordered := zipIdx_ordered xs 0
  have distinct : xs.zipIdx.Nodup := ordered.imp fun h he => by subst he; omega
  let f : Node → List (String × Nat) := fun node => match node with
    | .name n => xs.zipIdx.filter (·.1 == n)
    | .port .. => []
  have found : ∀ e, e ∈ reached.toList.flatMap f ↔
      e ∈ xs.zipIdx.filter fun e => reached.contains (.name e.1) := by
    intro e
    simp only [List.mem_flatMap, List.mem_filter, Std.HashSet.mem_toList,
      Std.HashSet.mem_iff_contains]
    constructor
    · rintro ⟨node, hn, he⟩
      cases node with
      | name n =>
        simp only [f, List.mem_filter, beq_iff_eq] at he
        obtain ⟨he, rfl⟩ := he
        exact ⟨he, hn⟩
      | port => simp [f] at he
    · rintro ⟨he, hn⟩
      exact ⟨.name e.1, hn, by simp [f, he]⟩
  rw [spec]
  unfold reachedInputs
  simp only [positions]
  change ((reached.toList.flatMap f).mergeSort fun a b => a.2 ≤ b.2).map Prod.fst = _
  congr 1
  apply List.Perm.eq_of_pairwise (le := fun a b => a.2 ≤ b.2)
  · intro a b ha hb hab hba
    have ha := ((found a).mp ((List.mergeSort_perm _ _).mem_iff.mp ha))
    have ha := List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp ha).1
    have hb := List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hb).1
    have he : a.2 = b.2 := by omega
    rw [he, hb] at ha
    exact Prod.ext (Option.some.inj ha).symm he
  · exact (List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; omega)
      (fun a b => by simp; omega) _).imp (by simp)
  · exact (ordered.filter _).imp Nat.le_of_lt
  · apply (List.mergeSort_perm _ _).trans
    apply (List.perm_ext_iff_of_nodup ?_ (distinct.filter _)).mpr found
    apply List.flatMap_nodup_owners _ _ some (fun e => Node.name e.1)
    · rw [List.filterMap_some]
      exact (Std.HashSet.distinct_toList (m := reached)).imp fun h he => by
        subst he; simp at h
    · intro node _
      cases node with
      | name n => exact distinct.filter _
      | port => simp [f]
    · intro node _ e he
      cases node with
      | name n =>
        simp only [f, List.mem_filter, beq_iff_eq] at he
        rw [he.2]
      | port => simp [f] at he

private def indexedInfer (m : Module) (children : String → Option Deps) : Deps :=
  let g := graph m children
  let index := firstIndex g
  let positions := groupIndex ((inputs m).zipIdx.map fun e => (e.1, e))
  let fuel := g.length + 1
  m.ports.filterMap fun p =>
    if p.dir == .output then
      let reached := indexedVisit index fuel [.name p.name] {}
      some (p.name, reachedInputs positions reached)
    else none

@[csimp] private theorem infer_indexed : infer = indexedInfer := by
  funext m children
  simp only [infer, indexedInfer, reachedInputs_eq]
  congr
  funext p
  split
  · congr 2
    apply List.filter_congr
    intro n _
    apply Bool.eq_iff_iff.mpr
    rw [indexedVisit_contains _ _ [.name p.name] [.name p.name] [] {} (fun _ => Iff.rfl)
      (by simp), List.contains_iff_mem]
  · rfl

end Deps
end Silicon.Core
