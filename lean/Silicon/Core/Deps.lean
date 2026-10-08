import Silicon.Core.Syntax
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

def inputs (m : Module) : List String :=
  m.ports.filterMap fun p => match p.dir, p.ty with
    | .input, .bits _ => some p.name
    | _, _ => none

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
def visit (g : List (Node × List Node)) : Nat → List Node → List Node → List Node
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

end Deps
end Silicon.Core
