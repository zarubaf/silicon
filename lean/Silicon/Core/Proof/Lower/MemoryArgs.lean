-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleSpec

/-!
A memory instance connects each model port once. Read and write ports appear in index order.
-/
namespace Silicon.Core.LowerProof

def renameArg (f : String → String) (arg : String × String × Mlir.Ty) :
    String × String × Mlir.Ty :=
  (arg.1, f arg.2.1, arg.2.2)

theorem find_of_nodup (l : List (String × String × Mlir.Ty)) (unique : (l.map Prod.fst).Nodup)
    (a : String × String × Mlir.Ty) (ha : a ∈ l) : l.find? (fun x => x.1 == a.1) = some a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · have ne : x.1 ≠ a.1 := fun eq => unique.1 (eq ▸ List.mem_map_of_mem ha)
      simp [ne, ih unique.2 ha]

theorem instanceInputs_find (args : List (String × String × Mlir.Ty)) (vals : Mlir.Env)
    (a : String × String × Mlir.Ty) (found : args.find? (fun x => x.1 == a.1) = some a) :
    Mlir.instanceInputs args vals a.1 = vals.typed a.2.1 a.2.2 := by
  simp [Mlir.instanceInputs, found]

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)

abbrev finalState (m : Typed.Module) : Lower.State := Lower.statementState m

theorem memReads_index (memory : String) (k : Nat)
    (hk : k < (memReads (finalState m) memory).length) :
    ((memReads (finalState m) memory)[k]).index = k := by
  have same := reads_indices m memory
  have := congrArg (fun l => l[k]?) same
  simp only [List.getElem?_map, List.getElem?_range hk, List.getElem?_eq_getElem hk,
    Option.map_some, Option.some.injEq] at this
  exact this

theorem memReads_member (r : Lower.ReadPort) (hr : r ∈ (finalState m).reads) :
    ∃ k, ∃ hk : k < (memReads (finalState m) r.memory).length,
      (memReads (finalState m) r.memory)[k] = r := by
  have member : r ∈ memReads (finalState m) r.memory := by
    unfold memReads
    rw [(List.mergeSort_perm _ _).mem_iff]
    exact List.mem_filter.mpr ⟨hr, by simp⟩
  obtain ⟨k, hk, same⟩ := List.mem_iff_getElem.mp member
  exact ⟨k, hk, same⟩

include h hm

theorem memWrites_index (i : Nat) (p : Pos) (memory : String) (w depth : Nat) (clk : String)
    (target) (ws) (he : Typed.Equation.mem i p memory w depth clk target ws ∈ m.body)
    (k : Nat) (hk : k < (memWrites (finalState m) memory).length) :
    ((memWrites (finalState m) memory)[k]).index = k := by
  have stmt := typed_erase_member m (Typed.Stmt.mem p memory w depth clk) _ he
    (i, Typed.Stmt.mem p memory w depth clk) (by simp [Typed.Equation.parts]) rfl
  have same := writes_indices raw t h m hm memory p w depth clk stmt
  have := congrArg (fun l => l[k]?) same
  simp only [List.getElem?_map, List.getElem?_range hk, List.getElem?_eq_getElem hk,
    Option.map_some, Option.some.injEq] at this
  exact this

theorem memArgs_find (i : Nat) (p : Pos) (memory : String) (w depth : Nat) (clk : String)
    (target) (ws) (he : Typed.Equation.mem i p memory w depth clk target ws ∈ m.body)
    (f : String → String) (a : String × String × Mlir.Ty)
    (ha : a ∈ memArgs (finalState m) memory w depth clk) :
    ((memArgs (finalState m) memory w depth clk).map (renameArg f)).find?
      (fun x => x.1 == a.1) = some (renameArg f a) := by
  have stmt := typed_erase_member m (Typed.Stmt.mem p memory w depth clk) _ he
    (i, Typed.Stmt.mem p memory w depth clk) (by simp [Typed.Equation.parts]) rfl
  have sig := memory_sig (finalState m) memory w depth clk (reads_indices m memory)
    (writes_indices raw t h m hm memory p w depth clk stmt)
  have pins : ((memArgs (finalState m) memory w depth clk).map Prod.fst) =
      ((((memConfig (finalState m) memory w depth).ports).filter (·.dir == .input)).map
        Mlir.Port.name) := by
    have := congrArg (List.map Prod.fst) sig.1
    simpa [List.map_map, Function.comp_def] using this
  have unique : (((memArgs (finalState m) memory w depth clk).map (renameArg f)).map
      Prod.fst).Nodup := by
    rw [List.map_map]
    change ((memArgs (finalState m) memory w depth clk).map Prod.fst).Nodup
    rw [pins]
    exact ((memModel_ports _).sublist (List.filter_sublist.map _))
  exact find_of_nodup _ unique _ (List.mem_map_of_mem ha)

end

end Silicon.Core.LowerProof
