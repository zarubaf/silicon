import Silicon.Core.Proof.Lower.Aliases
import Silicon.Core.Proof.Lower.Presence

/-!
A lowered module renames the operands of its raw ops. Its raw ops are the statement ops,
then the memory instances, then the registers.
-/
namespace Silicon.Core.LowerProof

def rename (m : Typed.Module) : String → String :=
  Lower.resolve (finalAliases m) (finalAliases m).size

def rawBody (m : Typed.Module) : List (List String × Mlir.Op) :=
  (Lower.statementState m).body.toList ++
    (Lower.memoryEntries m (Lower.statementState m)).map Prod.fst ++
    Lower.registerEntries m (Lower.statementState m)

theorem module_ports (m : Typed.Module) : (Lower.module m).1.ports = m.ports.map Lower.port :=
  rfl

theorem module_name (m : Typed.Module) : (Lower.module m).1.name = m.name := rfl

theorem module_body (m : Typed.Module) :
    (Lower.module m).1.body =
      (rawBody m).map (fun (names, op) => (names, Lower.substitute (rename m) op)) := by
  let s := Lower.statementState m
  let state := { s with body := s.body ++ ((Lower.memoryEntries m s).map Prod.fst).toArray }
  change (state.body.toList ++ Lower.registerEntries m state).map
    (fun (names, op) => (names, Lower.substitute
      (Lower.resolve state.aliases state.aliases.size) op)) = _
  simp only [state, Array.toList_append]
  rfl

theorem module_outputs (m : Typed.Module) :
    (Lower.module m).1.outputs = m.ports.filterMap fun p =>
      if p.dir == .output then some (rename m p.name) else none := rfl

theorem substitute_resultTypes (f : String → String) (op : Mlir.Op) :
    (Lower.substitute f op).resultTypes = op.resultTypes := by
  cases op <;> rfl

theorem substitute_valid (f : String → String) (op : Mlir.Op) :
    (Lower.substitute f op).Valid ↔ op.Valid := by
  cases op <;> exact Iff.rfl

theorem substitute_operands (f : String → String) (op : Mlir.Op) :
    (Lower.substitute f op).operands = op.operands.map fun o => (f o.1, o.2) := by
  cases op
  case compreg next clk reset ty => cases reset <;> simp [Lower.substitute, Mlir.Op.operands]
  all_goals simp [Lower.substitute, Mlir.Op.operands, Function.comp_def]

theorem lookup_of_mem {l : List (String × Mlir.Ty)} (unique : (l.map Prod.fst).Nodup)
    {key : String} {value : Mlir.Ty} (member : (key, value) ∈ l) : l.lookup key = some value := by
  induction l with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨k, v⟩ := head
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp [List.lookup]
    · have ne : key ≠ k := fun eq => unique.1 (eq ▸ List.mem_map_of_mem member)
      simp [List.lookup, show (key == k) = false from beq_eq_false_iff_ne.mpr ne,
        ih unique.2 member]

end Silicon.Core.LowerProof
