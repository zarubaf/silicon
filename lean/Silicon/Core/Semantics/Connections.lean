-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.State
import Silicon.Core.Semantics.Ownership

/-! Certified instance connections supply one typed expression per input port. -/
namespace Silicon.Core.Semantics

abbrev Connection (ctx : Typed.Ctx) (ports : List Port) :=
  (port : {p : Port // p ∈ ports}) × Typed.Expr ctx port.val.ty

/-! The connection rule counts each declared input exactly once. -/
theorem input_connection_count (d : Core.Design) (wf : WellFormed d)
    (m : Core.Module) (hm : m ∈ Typed.modules d)
    (pos : Pos) (name child : String) (inputs : List (String × Core.Expr))
    (hs : Core.Stmt.inst pos name child inputs ∈ m.body)
    (port : PortRef (Typed.portsOf d child) .input) :
    (inputs.filter (fun input => input.1 == port.val.name)).length = 1 := by
  rcases wf with ⟨_, _, _, _, _, _, _, _, _, connections, _, _⟩
  have hp := port.property.1
  cases hf : Rules.findItem d child with
  | none =>
    unfold Rules.findItem at hf
    simp [Typed.portsOf, hf] at hp
  | some item =>
    have ports : Typed.portsOf d child = Item.ports item := by
      unfold Rules.findItem at hf
      simp [Typed.portsOf, hf]
    have hp' := Eq.mp (congrArg (fun ps => port.val ∈ ps) ports) hp
    exact (connections m hm (.inst pos name child inputs) hs item hf port.val hp'
      port.property.2).1

/-! Erasure preserves connection counts because it keeps each port name. -/
theorem typed_input_count (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (port : PortRef (m.interfaces child) .input) :
    (inputs.filter (fun input => input.1.val.name == port.val.name)).length = 1 := by
  have erased : Core.Stmt.inst pos name child
      (inputs.map fun input => (input.1.val.name, input.2.erase)) ∈ m.erase.body := by
    apply (Ownership.mem_equationsErase m.body _).mpr
    exact ⟨_, hs, index, .inst pos name child inputs, by simp [Typed.Equation.parts], rfl⟩
  have interfaces : m.interfaces = Typed.portsOf d.design.erase :=
    (d.design.environments m hm).1
  have hp : port.val ∈ Typed.portsOf d.design.erase child :=
    Eq.mp (congrArg (fun ps => port.val ∈ ps child) interfaces) port.property.1
  have count := input_connection_count d.design.erase d.wellFormed m.erase
    (List.mem_filterMap.mpr ⟨.module m.erase, (d.design.environments m hm).2.2, rfl⟩)
    pos name child _ erased ⟨port.val, hp, port.property.2⟩
  simpa only [List.filter_map, List.length_map, Function.comp_def] using count

/-! The checked count makes the first matching connection a total selection. -/
def selectConnection {ctx : Typed.Ctx} {ports : List Port}
    (inputs : List (Connection ctx ports)) (name : String)
    (count : (inputs.filter (fun input => input.1.val.name == name)).length = 1) :
    {input : Connection ctx ports // input ∈ inputs ∧ input.1.val.name = name} :=
  let found := inputs.find? (fun input => input.1.val.name == name)
  have total : found.isSome := by
    apply List.find?_isSome.mpr
    obtain ⟨input, hi⟩ := List.length_eq_one_iff.mp count
    have hm : input ∈ inputs.filter (fun input => input.1.val.name == name) := by
      rw [hi]; simp
    exact ⟨input, List.mem_filter.mp hm⟩
  let input := found.get total
  have selected : found = some input := (Option.some_get total).symm
  ⟨input, List.mem_of_find?_eq_some selected,
    by simpa using List.find?_some selected⟩

theorem selected_port_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (child : String)
    (port : PortRef (m.interfaces child) .input)
    (input : Connection m.ctx (m.interfaces child))
    (same : input.1.val.name = port.val.name) : input.1.val = port.val := by
  have interfaces : m.interfaces = Typed.portsOf d.design.erase :=
    (d.design.environments m hm).1
  apply Check.interface_unique d.design.erase d.wellFormed.1 child input.1.val
    (Eq.mp (congrArg (fun ps => input.1.val ∈ ps child) interfaces) input.1.property)
    port.val (Eq.mp (congrArg (fun ps => port.val ∈ ps child) interfaces) port.property.1)
    same

private theorem lookup_connection_find {ctx : Typed.Ctx} {ports : List Port}
    (inputs : List (Connection ctx ports)) (name : String) (input : Connection ctx ports)
    (found : inputs.find? (fun input => input.1.val.name == name) = some input) :
    (inputs.map (fun input => (input.1.val.name, input.2.erase))).lookup name =
      some input.2.erase := by
  induction inputs with
  | nil => simp at found
  | cons head tail ih =>
    by_cases hn : head.1.val.name = name
    · have he : head = input := by simpa [List.find?_cons, hn] using found
      subst input
      simp [hn]
    · have hf : tail.find? (fun input => input.1.val.name == name) = some input := by
        simpa [List.find?_cons, hn] using found
      simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hn)] using ih hf

theorem selectConnection_lookup {ctx : Typed.Ctx} {ports : List Port}
    (inputs : List (Connection ctx ports)) (name : String)
    (count : (inputs.filter (fun input => input.1.val.name == name)).length = 1) :
    (inputs.map (fun input => (input.1.val.name, input.2.erase))).lookup name =
      some (selectConnection inputs name count).val.2.erase := by
  apply lookup_connection_find
  unfold selectConnection
  exact (Option.some_get _).symm

def connectionExpr (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (port : PortRef (m.interfaces child) .input) : Typed.Expr m.ctx port.val.ty :=
  let input := selectConnection inputs port.val.name
    (typed_input_count d m hm index pos name child inputs hs port)
  let same := selected_port_eq d m hm child port input.val input.property.2
  (congrArg Port.ty same) ▸ input.val.2

private theorem erase_cast {ctx : Typed.Ctx} {a b : Ty} (same : a = b)
    (expr : Typed.Expr ctx a) : (same ▸ expr).erase = expr.erase := by
  cases same
  rfl

/-! The selected typed expression is the connection recorded in the erased instance. -/
theorem connectionExpr_lookup (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (port : PortRef (m.interfaces child) .input) :
    (inputs.map (fun input => (input.1.val.name, input.2.erase))).lookup port.val.name =
      some (connectionExpr d m hm index pos name child inputs hs port).erase := by
  simp only [connectionExpr, erase_cast]
  exact selectConnection_lookup inputs port.val.name _

/-! Every child input evaluates in the parent's current valuation and memory state. -/
def connectionValues (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (values : Valuation m.ctx) (memories : Memories m.ctx) :
    ConnectionValues m
  | ⟨.inst index pos name child inputs, hs⟩ => fun port =>
    evalExpr values memories (connectionExpr d m hm index pos name child inputs hs port)
  | ⟨.let_ .., _⟩ | ⟨.reg .., _⟩ | ⟨.mem .., _⟩ | ⟨.assign .., _⟩ => ()

/-! A child input changes only when one of its connected expression's reads changes. -/
theorem connectionValues_congr (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (index : Nat) (pos : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (hs : Typed.Equation.inst index pos name child inputs ∈ m.body)
    (port : PortRef (m.interfaces child) .input)
    (a b : Valuation m.ctx) (memories : Memories m.ctx)
    (agree : ∀ node ∈ Deps.reads
      (connectionExpr d m hm index pos name child inputs hs port).erase, ∀ width found,
        a node width found = b node width found) :
    connectionValues d m hm a memories ⟨.inst index pos name child inputs, hs⟩ port =
      connectionValues d m hm b memories ⟨.inst index pos name child inputs, hs⟩ port := by
  exact evalExpr_congr a b memories _ agree

end Silicon.Core.Semantics
