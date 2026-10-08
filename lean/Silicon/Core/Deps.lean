import Silicon.Core.Syntax
import Silicon.Core.GraphReach
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

/-! The first source entry wins when a node occurs more than once. -/
def Node.index (entries : List (Node × α)) : Std.HashMap Node α :=
  match entries with
  | [] => {}
  | (n, v) :: rest => (Node.index rest).insert n v

theorem Node.index_lookup (entries : List (Node × α)) (n : Node) :
    (Node.index entries)[n]? = entries.lookup n := by
  induction entries with
  | nil => simp [Node.index]
  | cons a rest ih =>
    rcases a with ⟨k, v⟩
    simp only [Node.index, Std.HashMap.getElem?_insert, List.lookup_cons, ih, beq_iff_eq]
    by_cases h : k = n
    · subst k; simp
    · simp [h, show (n == k) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]

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

end Deps
end Silicon.Core
