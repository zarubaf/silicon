import Silicon.Core.Interp

/-! Unique write ports fix the update order after any source permutation. -/
namespace Silicon.Core.Semantics

private theorem same_key_eq (key : α → Nat) (xs : List α)
    (unique : (xs.map key).Nodup) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp ha with rfl | haTail
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · rfl
      · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨b, hbTail, rfl⟩))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨a, haTail, rfl⟩))
      · exact ih unique.2 haTail hbTail

private theorem sort_key_perm (key : α → Nat) (xs ys : List α) (perm : xs.Perm ys)
    (unique : (xs.map key).Nodup) :
    xs.mergeSort (fun a b => decide (key a ≤ key b)) =
      ys.mergeSort (fun a b => decide (key a ≤ key b)) := by
  have sorted (zs : List α) := List.pairwise_mergeSort
    (le := fun a b : α => decide (key a ≤ key b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) zs
  have left := List.mergeSort_perm xs (fun a b => decide (key a ≤ key b))
  have right := List.mergeSort_perm ys (fun a b => decide (key a ≤ key b))
  apply List.Perm.eq_of_pairwise (le := fun a b => key a ≤ key b)
    (fun a b ha hb ab ba => same_key_eq key xs unique a b
      (left.mem_iff.mp ha) (perm.mem_iff.mpr (right.mem_iff.mp hb)) (Nat.le_antisymm ab ba))
    (by simpa using sorted xs) (by simpa using sorted ys)
  exact left.trans (perm.trans right.symm)

abbrev WriteValues (width : Nat) := Nat × Nat × Value width × Value 1

def evalWrite (values : Valuation ctx) (memories : Memories ctx)
    (write : Typed.Write ctx width depth) : WriteValues width :=
  (write.port, (evalExpr values memories write.addr).toNat,
    evalExpr values memories write.data, evalExpr values memories write.enable)

private theorem nextMemory_evaluated (values : Valuation ctx) (memories : Memories ctx)
    (memory : Fin depth → Value width) (writes : List (Typed.Write ctx width depth)) :
    nextMemory values memories memory writes =
      ((writes.map (evalWrite values memories)).mergeSort (fun a b => a.1 ≤ b.1)).foldl
        (fun current write => memoryWrite current write.2.1 write.2.2.1 write.2.2.2) memory := by
  have commute := List.map_mergeSort
    (r := fun a b : Typed.Write ctx width depth => decide (a.port ≤ b.port))
    (s := fun a b : WriteValues width => decide (a.1 ≤ b.1))
    (f := evalWrite values memories) (l := writes) (by intros; rfl)
  rw [← commute, List.foldl_map]
  rfl

theorem nextMemory_eq_of_evaluated {ctx ctx' : Typed.Ctx}
    (values : Valuation ctx) (values' : Valuation ctx')
    (memories : Memories ctx) (memories' : Memories ctx')
    (memory : Fin depth → Value width) (writes : List (Typed.Write ctx width depth))
    (writes' : List (Typed.Write ctx' width depth))
    (unique : (writes.map Typed.Write.port).Nodup)
    (same : (writes.map (evalWrite values memories)).Perm
      (writes'.map (evalWrite values' memories'))) :
    nextMemory values memories memory writes = nextMemory values' memories' memory writes' := by
  rw [nextMemory_evaluated, nextMemory_evaluated]
  rw [sort_key_perm Prod.fst _ _ same]
  simpa only [List.map_map, Function.comp_def, evalWrite] using unique

theorem typed_write_ports_nodup (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (i : Nat) (p : Pos) (name : String) (width depth : Nat)
    (clock : String) (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body) :
    (writes.map Typed.Write.port).Nodup := by
  let select (part : Nat × Typed.Stmt m.ctx m.interfaces) : Option Nat :=
    match part.2.erase with
    | .write _ n port _ _ _ => if n == name then some port else none
    | _ => none
  have rawMember : Core.Stmt.mem p name width depth clock ∈ m.erase.body := by
    apply (Ownership.mem_equationsErase m.body _).mpr
    exact ⟨.mem i p name width depth clock target writes, member, i,
      .mem p name width depth clock, by simp [Typed.Equation.parts], rfl⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rule, _⟩ := d.wellFormed
  have unique := (rule m.erase (module_mem d.design m hm) _ rawMember).1
  have sorted : (((m.body.flatMap Typed.Equation.parts).mergeSort
      (fun a b => decide (a.1 ≤ b.1))).filterMap select).Nodup := by
    simp only [Rules.writes, Typed.Module.erase, Typed.equationsErase,
      List.map_filterMap, List.filterMap_map, Function.comp_def] at unique
    suffices eq : (fun part : Nat × Typed.Stmt m.ctx m.interfaces =>
        (match part.2.erase with
        | .write p n port _ _ _ => if n == name then some (port, p) else none
        | _ => none).map Prod.fst) = select by
      exact (congrArg (fun f =>
        (((m.body.flatMap Typed.Equation.parts).mergeSort
          (fun a b => decide (a.1 ≤ b.1))).filterMap f).Nodup) eq).mp unique
    funext part
    rcases part with ⟨index, stmt⟩
    cases stmt <;> simp [select, Typed.Stmt.erase]
  have flat := ((List.mergeSort_perm (m.body.flatMap Typed.Equation.parts)
    (fun a b => decide (a.1 ≤ b.1))).filterMap select).nodup_iff.mp sorted
  have sub : (Typed.Equation.mem i p name width depth clock target writes).parts.Sublist
      (m.body.flatMap Typed.Equation.parts) :=
    List.sublist_flatten_of_mem (List.mem_map.mpr
      ⟨.mem i p name width depth clock target writes, member, rfl⟩)
  have own := flat.sublist (sub.filterMap select)
  simpa [Typed.Equation.parts, select, Typed.Stmt.erase, List.filterMap_map, Function.comp_def] using own

end Silicon.Core.Semantics
