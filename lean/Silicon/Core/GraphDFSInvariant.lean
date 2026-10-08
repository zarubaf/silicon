import Silicon.Core.GraphReach

/-! A finished node reaches only finished nodes or shares a cycle with an active ancestor. -/
namespace Silicon.Core.GraphDFSInvariant

open GraphReach

variable {α : Type} [BEq α]
variable {g : List (α × List α)} {done active : List α} {x : α}

def ClosedNode (g : List (α × List α)) (done : List α) (x : α) : Prop :=
  ∀ y, Reachable g x y → y ∈ done

def Mutual (g : List (α × List α)) (x y : α) : Prop :=
  Reachable g x y ∧ Reachable g y x

def DoneInvariant (g : List (α × List α)) (done active : List α) : Prop :=
  ∀ x ∈ done, ClosedNode g done x ∨ ∃ a ∈ active, Mutual g x a

theorem walk_boundary
    (closed : ∀ f ∈ done, ∀ y ∈ (g.lookup f).getD [], y ∈ done ∨ y ∈ active)
    {length : Nat} {start target : α} (walk : Walk g length start target)
    (hstart : start ∈ done) :
    target ∈ done ∨ ∃ a ∈ active, Reachable g start a := by
  induction walk with
  | refl => exact Or.inl hstart
  | @step start child target length hedge htail ih =>
    rcases closed start hstart child hedge with hchild | hchild
    · rcases ih hchild with htarget | ⟨a, ha, hpath⟩
      · exact Or.inl htarget
      · exact Or.inr ⟨a, ha, Reachable.trans g (Reachable.edge g hedge) hpath⟩
    · exact Or.inr ⟨child, hchild, Reachable.edge g hedge⟩

theorem finish_node
    (closed : ∀ f ∈ x :: done, ∀ y ∈ (g.lookup f).getD [],
      y ∈ x :: done ∨ y ∈ active)
    (ancestors : ∀ a ∈ active, Reachable g a x) :
    ClosedNode g (x :: done) x ∨ ∃ a ∈ active, Mutual g x a := by
  classical
  by_cases h : ∃ a ∈ active, Reachable g x a
  · obtain ⟨a, ha, hr⟩ := h
    exact Or.inr ⟨a, ha, hr, ancestors a ha⟩
  · apply Or.inl
    intro y hy
    obtain ⟨length, hw⟩ := hy
    rcases walk_boundary closed hw (by simp) with hy | ha
    · exact hy
    · exact False.elim (h ha)

theorem DoneInvariant.finish (h : DoneInvariant g done (x :: active))
    (closed : ∀ f ∈ x :: done, ∀ y ∈ (g.lookup f).getD [],
      y ∈ x :: done ∨ y ∈ active)
    (ancestors : ∀ a ∈ active, Reachable g a x) :
    DoneInvariant g (x :: done) active := by
  have hx := finish_node closed ancestors
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hx
  · rcases h f hf with hfclosed | ⟨a, ha, hfa, haf⟩
    · exact Or.inl (fun y hy => List.mem_cons_of_mem _ (hfclosed y hy))
    · rcases List.mem_cons.mp ha with rfl | ha
      · rcases hx with hxclosed | ⟨a, ha, hxa, hax⟩
        · exact Or.inl (fun y hy => hxclosed y (Reachable.trans g haf hy))
        · exact Or.inr ⟨a, ha, Reachable.trans g hfa hxa, Reachable.trans g hax haf⟩
      · exact Or.inr ⟨a, ha, hfa, haf⟩

end Silicon.Core.GraphDFSInvariant
