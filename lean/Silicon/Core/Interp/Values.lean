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

abbrev DriverKey := Deps.Node × Nat
abbrev DriverTable (m : Typed.Module) :=
  Std.DHashMap DriverKey (fun key => ValueDriver m key.1 key.2)

def driverTable (m : Typed.Module) (entries : List (PackedDriver m)) : DriverTable m :=
  entries.foldr (fun entry table => table.insert (entry.1, entry.2.1) entry.2.2) ∅

theorem driverTable_total (m : Typed.Module) (entries : List (PackedDriver m))
    (driver : ValueDriver m node width) (member : ⟨node, width, driver⟩ ∈ entries) :
    ((driverTable m entries).get? (node, width)).isSome := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    simp only [driverTable, List.foldr_cons, Std.DHashMap.get?_insert]
    split
    · rfl
    next ne =>
      apply ih
      rcases List.mem_cons.mp member with same | member
      · subst entry
        exact False.elim (ne (by simp))
      · exact member

def indexedDriver (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (table : DriverTable m) (complete : ∀ node width (_v : ValueDriver m node width),
      (table.get? (node, width)).isSome) (ref : ValueRef m.ctx) :
    ValueDriver m ref.node ref.width :=
  (table.get? (ref.node, ref.width)).get (by
    obtain ⟨v⟩ := valueDriver_exists d.design d.wellFormed m hm ref.node ref.width ref.found
    exact complete _ _ v)

theorem indexedDriver_eq (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (table : DriverTable m) (complete : ∀ node width (_v : ValueDriver m node width),
      (table.get? (node, width)).isSome) (ref : ValueRef m.ctx) :
    indexedDriver d m hm table complete ref =
      decodeValue d.design d.wellFormed m hm ref.node ref.width ref.found :=
  ValueDriver.unique d.design d.wellFormed m hm _ _

/-! All comparisons and equation reads use the same graph and driver index. -/
def preparedSystem (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : EquationSolution.System (ValueRef m.ctx) (fun ref => Value ref.width) :=
  let nodes := valueRefs m.ctx
  let active := (Deps.graph m.erase m.children).map Prod.fst
  let ranks := indexed (fun ref : ValueRef m.ctx =>
    if ref.node ∈ active then Typed.rank m.ranks ref.node + 1 else 0) nodes valueRefs_complete
  let table := driverTable m (drivers m)
  let complete := fun node width (v : ValueDriver m node width) =>
    driverTable_total m (drivers m) v (driver_mem m v)
  let driver := indexedDriver d m hm table complete
  { initial := fun _ => 0
    rank := ranks.get
    rhs := fun values ref =>
      let memories := stateMemories m children state
      (driver ref).eval m children state input (curryValues values) memories
        (connectionValues d m hm (curryValues values) memories)
    respects := by
      intro ref a b agree
      apply ValueDriver.eval_rank_congr
      intro dep width found lower
      apply agree ⟨dep, width, found⟩
      simpa only [Table.get_eq, active, valueRank] using lower }

theorem preparedSystem_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : preparedSystem d m hm children state input =
      localSystem d m hm children state input := by
  simp only [preparedSystem, Table.get_eq, indexedDriver_eq]
  rfl

def orderedSolution (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : Valuation m.ctx :=
  curryValues (ordered (preparedSystem d m hm children state input) (valueRefs m.ctx))

theorem orderedSolution_eq (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (children : Children m) (state : LocalState m children)
    (input : Input m) : orderedSolution d m hm children state input =
      localSolution d m hm children state input := by
  unfold orderedSolution localSolution
  rw [preparedSystem_eq]
  rw [ordered_eq_solution _ _ valueRefs_complete]

end Silicon.Core.Interp
