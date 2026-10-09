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

/-! One preparation supplies the ordered nodes and their driver index. -/
structure Prepared (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies) where
  nodes : List (ValueRef m.ctx)
  complete : ∀ ref, ref ∈ nodes
  sorted : nodes.Pairwise (fun a b => valueRank m a.node ≤ valueRank m b.node)
  drivers : DriverTable m
  total : ∀ node width (_v : ValueDriver m node width), (drivers.get? (node, width)).isSome

def prepare (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies) :
    Prepared d m hm :=
  let active := (Deps.graph m.erase m.children).map Prod.fst
  let ranks := indexed (fun ref : ValueRef m.ctx => valueRankWith m.ranks active ref.node)
    (valueRefs m.ctx) valueRefs_complete
  { nodes := (valueRefs m.ctx).mergeSort (fun a b => ranks.get a ≤ ranks.get b)
    complete := fun ref => List.mem_mergeSort.mpr (valueRefs_complete ref)
    sorted := by
      simp only [Table.get_eq]
      have sorted := List.pairwise_mergeSort
        (le := fun a b : ValueRef m.ctx => decide (valueRank m a.node ≤ valueRank m b.node))
        (by intros; simp_all; omega) (by intros; simp; omega) (valueRefs m.ctx)
      exact sorted.imp (fun h => of_decide_eq_true h)
    drivers := driverTable m (drivers m)
    total := fun _ _ v => driverTable_total m (drivers m) v (driver_mem m v) }

end Silicon.Core.Interp
