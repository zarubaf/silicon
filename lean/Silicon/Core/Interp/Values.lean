import Silicon.Core.Interp.Ordered
import Silicon.Core.Semantics.Local

/-! The typed context supplies all nodes to the ordered evaluator. -/
namespace Silicon.Core.Interp

open Semantics

deriving instance DecidableEq for ValueRef

instance : BEq (ValueRef ctx) := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq (ValueRef ctx) where
  eq_of_beq := by simp
  rfl := by simp
instance : Hashable (ValueRef ctx) := ⟨fun ref => hash ref.node⟩

def valueRefs (ctx : Typed.Ctx) : List (ValueRef ctx) :=
  (ctx.map Prod.fst).filterMap fun node =>
    match found : ctx.lookup node with
    | some (.value (.bits width)) => some ⟨node, width, found⟩
    | _ => none

theorem valueRefs_complete (ref : ValueRef ctx) : ref ∈ valueRefs ctx := by
  obtain ⟨node, width, found⟩ := ref
  have member : node ∈ ctx.map Prod.fst := by
    obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp found
    rw [eq]
    simp
  unfold valueRefs
  apply List.mem_filterMap.mpr
  exact ⟨node, member, by
    split
    next w hw =>
      have eq : w = width := by simpa [found] using hw.symm
      subst w
      rfl
    next h => exact False.elim (h width found)⟩

def orderedSolution (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : Valuation m.ctx :=
  curryValues (ordered (localSystem d m hm children state input) (valueRefs m.ctx))

theorem orderedSolution_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : orderedSolution d m hm children state input =
      localSolution d m hm children state input := by
  unfold orderedSolution localSolution
  rw [ordered_eq_solution _ _ valueRefs_complete]

end Silicon.Core.Interp
