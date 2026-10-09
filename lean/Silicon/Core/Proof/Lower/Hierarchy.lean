import Silicon.Core.Proof.Lower.Module

/-!
Child proofs follow instance paths. They do not need an order on sibling SSA names.
-/
namespace Silicon.Core.LowerProof

theorem corresponds_instance (d : Semantics.CertifiedDesign) (env)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm)
    (s : Semantics.State d env m hm) (σ : Mlir.ModuleState)
    (h : Corresponds d env noExterns m hm s σ)
    (i : Nat) (p : Pos) (name child : String)
    (inputs : List ((port : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx port.val.ty))
    (member : .inst i p name child inputs ∈ m.body) (c : Typed.Module)
    (found : d.design.bodies.find? (·.name == child) = some c) :
    Corresponds d env noExterns c (List.mem_of_find?_eq_some found)
      (cast (Semantics.State_inst_module d env m hm i p name child inputs member c found)
        (s ⟨.inst i p name child inputs, member⟩)) (σ.instance name) := by
  intro path leaf cell state
  apply (cellCorresponds_instance σ name path leaf cell).mpr
  apply h (name :: path) leaf cell
  simpa only [List.cons_append,
    Semantics.namedState_instance d env noExterns m hm s i p name child inputs member c found]
    using state

theorem hierarchy_child (d : Mlir.Design) (m : Mlir.Module) (σ : Mlir.ModuleState)
    (inputs : Mlir.Env) (vals : Mlir.Valuation)
    (h : Mlir.IsHierarchySolution d m σ inputs vals)
    (inst callee : String) (args : List (String × String × Mlir.Ty))
    (member : m.findInstance inst = some (callee, args)) (child : Mlir.Module)
    (found : d.findModule callee = some child) :
    Mlir.IsHierarchySolution d child (σ.instance inst)
      (Mlir.instanceInputs args (vals [])) (fun path => vals (inst :: path)) := by
  constructor
  · obtain ⟨other, otherFound, solved⟩ := h.2 [] m rfl inst callee args member
    have same := Option.some.inj (otherFound.symm.trans found)
    subst other
    exact solved
  · intro path parent parentFound name target connections connectionFound
    have owner : m.atPath d (inst :: path) = some parent := by
      simpa [Mlir.Module.atPath, member, found] using parentFound
    obtain ⟨next, nextFound, solved⟩ :=
      h.2 (inst :: path) parent owner name target connections connectionFound
    exact ⟨next, nextFound, solved⟩

theorem nextHierarchyState_child (d : Mlir.Design) (m : Mlir.Module) (vals : Mlir.Valuation)
    (inst callee : String) (args : List (String × String × Mlir.Ty))
    (member : m.findInstance inst = some (callee, args)) (child : Mlir.Module)
    (found : d.findModule callee = some child) :
    (Mlir.nextHierarchyState d m vals).instance inst =
      Mlir.nextHierarchyState d child (fun path => vals (inst :: path)) := by
  apply congrArg Mlir.ModuleState.mk
  funext path name
  simp [Mlir.nextHierarchyState, Mlir.Module.atPath, member, found]

end Silicon.Core.LowerProof
