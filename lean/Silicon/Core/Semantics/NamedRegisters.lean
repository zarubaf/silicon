import Silicon.Core.Semantics.NamedLocal

/-! A checked register has one next equation, independent of statement order. -/
namespace Silicon.Core.Semantics

private theorem unique_filterMap (f : α → Option β) (xs : List α)
    (one : (xs.filterMap f).length = 1) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (va vb : β) (fa : f a = some va) (fb : f b = some vb) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    cases fx : f x with
    | none =>
      have neA : a ≠ x := by intro eq; subst a; rw [fx] at fa; contradiction
      have neB : b ≠ x := by intro eq; subst b; rw [fx] at fb; contradiction
      exact ih (by simpa [fx] using one) (List.mem_of_ne_of_mem neA ha)
        (List.mem_of_ne_of_mem neB hb)
    | some value =>
      have empty : xs.filterMap f = [] := by simpa [fx] using one
      have absent (v : α) (result : β) (hv : f v = some result) : v ∉ xs := by
        intro member
        have hm : result ∈ xs.filterMap f := List.mem_filterMap.mpr ⟨v, member, hv⟩
        simp [empty] at hm
      have ea : a = x := (List.mem_cons.mp ha).resolve_right (absent a va fa)
      have eb : b = x := (List.mem_cons.mp hb).resolve_right (absent b vb fb)
      exact ea.trans eb.symm

theorem next_erase_reorder (d : CertifiedDesign)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies)
    (body : Permuted StmtReorder m.erase.body m'.erase.body)
    (i i' : Nat) (p p' : Pos) (name : String) (width : Nat) (clock clock' : String)
    (target : Typed.valueTy m.ctx name = some (.bits width))
    (target' : Typed.valueTy m'.ctx name = some (.bits width))
    (reset : Option (Typed.Reset m.ctx width)) (reset' : Option (Typed.Reset m'.ctx width))
    (ni ni' : Nat) (np np' : Pos) (next : Typed.Expr m.ctx (.bits width))
    (next' : Typed.Expr m'.ctx (.bits width))
    (member : .reg i p name width clock target reset ni np next ∈ m.body)
    (member' : .reg i' p' name width clock' target' reset' ni' np' next' ∈ m'.body) :
    next.erase = next'.erase := by
  have reg : Core.Stmt.reg p name width clock (reset.map Typed.Reset.erase) ∈ m.erase.body :=
    (Ownership.mem_equationsErase m.body _).mpr
      ⟨_, member, i, .reg p name width clock reset, by simp [Typed.Equation.parts], rfl⟩
  have hn : Core.Stmt.next np name next.erase ∈ m.erase.body :=
    (Ownership.mem_equationsErase m.body _).mpr
      ⟨_, member, ni, .next np name width target next, by simp [Typed.Equation.parts], rfl⟩
  have hn' : Core.Stmt.next np' name next'.erase ∈ m'.erase.body :=
    (Ownership.mem_equationsErase m'.body _).mpr
      ⟨_, member', ni', .next np' name width target' next', by simp [Typed.Equation.parts], rfl⟩
  obtain ⟨s, hs, rel⟩ := body.right hn'
  cases rel
  obtain ⟨_, _, _, _, registers, _⟩ := d.wellFormed
  have one := registers m.erase (module_mem d.design m hm) _ reg
  have eq := unique_filterMap
    (fun s : Core.Stmt => match s with
      | Core.Stmt.next p n _ => if n == name then some p else none
      | _ => none) m.erase.body one _ _ hn hs np np' (by simp) (by simp)
  exact (Core.Stmt.next.inj eq).2.2

end Silicon.Core.Semantics
