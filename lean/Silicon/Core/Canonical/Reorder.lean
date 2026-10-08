import Silicon.Core.Typed
import Silicon.Core.Check
import Silicon.Core.Text

/-! Equal name lookups preserve expression types and source equations. -/
namespace Silicon.Core.Typed

variable {ctx ctx' : Ctx}

def Expr.recontext (h : ∀ n, ctx.lookup n = ctx'.lookup n) : Expr ctx ty → Expr ctx' ty
  | .ref p n found => .ref p n ((h n).symm.trans found)
  | .clock p n found => .clock p n ((h (.name n)).symm.trans found)
  | .const p w v => .const p w v
  | .un p op arg => .un p op (arg.recontext h)
  | .bin p op ordinary lhs rhs => .bin p op ordinary (lhs.recontext h) (rhs.recontext h)
  | .concat p lhs rhs bound => .concat p (lhs.recontext h) (rhs.recontext h) bound
  | .icmp p pred lhs rhs => .icmp p pred (lhs.recontext h) (rhs.recontext h)
  | .mux p cond yes no => .mux p (cond.recontext h) (yes.recontext h) (no.recontext h)
  | .extract p arg lo count bound => .extract p (arg.recontext h) lo count bound
  | .replicate p arg count bound => .replicate p (arg.recontext h) count bound
  | .read p n found addr => .read p n ((h (.name n)).symm.trans found) (addr.recontext h)

@[simp] theorem Expr.recontext_erase (h : ∀ n, ctx.lookup n = ctx'.lookup n)
    (e : Expr ctx ty) : (e.recontext h).erase = e.erase := by
  induction e <;> simp_all [Expr.recontext, Expr.erase]
  rename_i node _
  cases node <;> rfl

private def Reset.recontext (h : ∀ n, ctx.lookup n = ctx'.lookup n)
    (r : Reset ctx width) : Reset ctx' width :=
  ⟨r.kind, r.signal.recontext h, r.value.recontext h⟩

private theorem Reset.recontext_erase (h : ∀ n, ctx.lookup n = ctx'.lookup n)
    (r : Reset ctx width) : (r.recontext h).erase = r.erase := by
  simp [Reset.recontext, Reset.erase]

def Stmt.recontext (h : ∀ n, ctx.lookup n = ctx'.lookup n) : Stmt ctx ports → Stmt ctx' ports
  | .let_ p n w e => .let_ p n w (e.recontext h)
  | .reg p n w c r => .reg p n w c (r.map (Reset.recontext h))
  | .next p n w target e => .next p n w
      (by simpa only [valueTy, ← h] using target) (e.recontext h)
  | .mem p n w depth c => .mem p n w depth c
  | .write p n port w depth target addr data enable =>
    .write p n port w depth ((h (.name n)).symm.trans target)
      (addr.recontext h) (data.recontext h) (enable.recontext h)
  | .inst p n child inputs =>
    .inst p n child (inputs.map fun x => ⟨x.1, x.2.recontext h⟩)
  | .assign p n w target e => .assign p n w
      (by simpa only [valueTy, ← h] using target) (e.recontext h)

@[simp] theorem Stmt.recontext_erase (h : ∀ n, ctx.lookup n = ctx'.lookup n)
    (s : Stmt ctx ports) : (s.recontext h).erase = s.erase := by
  cases s <;> simp [Stmt.recontext, Stmt.erase, List.map_map, Function.comp_def]
  rename_i reset
  cases reset <;> simp [Reset.recontext_erase]

end Silicon.Core.Typed

/-! Canonical order preserves the port interface used to type each instance. -/
namespace Silicon.Core

/-! A reorder keeps every equation and permits permutations at each unordered boundary. -/
def Permuted (r : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  ∃ pairs : List (α × β), (pairs.map Prod.fst).Perm xs ∧
    (pairs.map Prod.snd).Perm ys ∧ ∀ pair ∈ pairs, r pair.1 pair.2

inductive StmtReorder : Stmt → Stmt → Prop where
  | same (s : Stmt) : StmtReorder s s
  | inst (p : Pos) (name child : String) (xs ys : List (String × Expr)) :
      xs.Perm ys → StmtReorder (.inst p name child xs) (.inst p name child ys)

inductive ItemReorder : Item → Item → Prop where
  | module (m m' : Module) : m'.pos = m.pos → m'.name = m.name →
      m'.ports = m.ports → Permuted StmtReorder m.body m'.body →
      ItemReorder (.module m) (.module m')
  | extern (e e' : Extern) : e'.pos = e.pos → e'.name = e.name →
      e'.ports = e.ports → e.deps.Perm e'.deps → ItemReorder (.extern e) (.extern e')

/-! A child without an interface has no port order for its connections. -/
def unresolvedStmt (items : List Item) : Stmt → Option Stmt
  | s@(.inst _ _ child _) => if items.any (·.name == child) then none else some s
  | _ => none

def frozenConnections (items : List Item) : Item → List Stmt
  | .module m => m.body.filterMap (unresolvedStmt items)
  | .extern _ => []

def Reorder (d d' : Design) : Prop :=
  d'.top = d.top ∧ d'.topPos = d.topPos ∧
    Permuted (fun a b => ItemReorder a b ∧
      (frozenConnections d.items a).Perm (frozenConnections d.items b)) d.items d'.items

private theorem permuted_map (r : α → β → Prop) (xs : List α) (f : α → β)
    (h : ∀ x ∈ xs, r x (f x)) : Permuted r xs (xs.map f) := by
  refine ⟨xs.map (fun x => (x, f x)), ?_, ?_, ?_⟩
  · simp [Function.comp_def]
  · simp [Function.comp_def]
  · intro pair hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact h x hx

private theorem Permuted.perm_right {r : α → β → Prop} {xs : List α} {ys zs : List β}
    (h : Permuted r xs ys) (p : ys.Perm zs) : Permuted r xs zs := by
  obtain ⟨pairs, left, right, related⟩ := h
  exact ⟨pairs, left, right.trans p, related⟩

private theorem canonicalStmt_reorder (items : List Item) (s : Stmt) :
    StmtReorder s (canonicalStmt items s) := by
  cases s with
  | inst p n child xs =>
    simp only [canonicalStmt]
    split
    · exact .same _
    · exact .inst _ _ _ _ _ (List.mergeSort_perm _ _).symm
  | _ => exact .same _

theorem canonicalize_reorder (d : Design) : Reorder d (canonicalize d) := by
  refine ⟨rfl, rfl, ?_⟩
  unfold canonicalize
  dsimp only
  apply Permuted.perm_right _ (List.mergeSort_perm _ _).symm
  apply permuted_map
  intro item _
  cases item with
  | module m =>
    constructor
    · refine .module _ _ rfl rfl rfl ?_
      exact (permuted_map _ _ _ (fun s _ => canonicalStmt_reorder d.items s)).perm_right
        (List.mergeSort_perm _ _).symm
    · unfold frozenConnections
      apply List.Perm.trans _ ((List.mergeSort_perm _ _).filterMap _).symm
      apply List.Perm.of_eq
      rw [List.filterMap_map]
      dsimp only
      congr 1
      funext stmt
      dsimp only [Function.comp_apply]
      cases stmt <;> try rfl
      rename_i p name child xs
      simp only [canonicalStmt]
      split
      next absent => rfl
      next item found =>
        have present : d.items.any (·.name == child) = true :=
          List.any_eq_true.mpr ⟨item, List.mem_of_find?_eq_some found,
            by simpa using List.find?_some found⟩
        simp [unresolvedStmt, present]
  | extern e =>
    exact ⟨.extern _ _ rfl rfl rfl (List.mergeSort_perm _ _).symm, .refl _⟩

/-! Membership and multiplicity transport the local rules across a reorder. -/
namespace Permuted

theorem left {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, r x y := by
  obtain ⟨pairs, hp, hq, hr⟩ := h
  obtain ⟨pair, member, eq⟩ := List.mem_map.mp (hp.mem_iff.mpr hx)
  exact ⟨pair.2, hq.mem_iff.mp (List.mem_map.mpr ⟨pair, member, rfl⟩), eq ▸ hr _ member⟩

theorem right {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, r x y := by
  obtain ⟨pairs, hp, hq, hr⟩ := h
  obtain ⟨pair, member, eq⟩ := List.mem_map.mp (hq.mem_iff.mpr hy)
  exact ⟨pair.1, hp.mem_iff.mp (List.mem_map.mpr ⟨pair, member, rfl⟩), eq ▸ hr _ member⟩

theorem map {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) (f : α → γ) (g : β → γ)
    (same : ∀ a b, r a b → f a = g b) : (xs.map f).Perm (ys.map g) := by
  obtain ⟨pairs, hp, hq, hr⟩ := h
  apply (hp.map f).symm.trans
  apply List.Perm.trans _ (hq.map g)
  apply List.Perm.of_eq
  simp only [List.map_map]
  apply List.map_congr_left
  intro pair member
  exact same _ _ (hr _ member)

theorem flatMap {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) (f : α → List γ) (g : β → List γ)
    (same : ∀ a b, r a b → (f a).Perm (g b)) : (xs.flatMap f).Perm (ys.flatMap g) := by
  obtain ⟨pairs, hp, hq, hr⟩ := h
  apply (hp.flatMap_right f).symm.trans
  apply List.Perm.trans _ (hq.flatMap_right g)
  simp only [List.flatMap_map]
  clear hp hq
  induction pairs with
  | nil => exact .nil
  | cons pair pairs ih =>
    simp only [List.flatMap_cons]
    exact (same _ _ (hr _ (by simp))).append (ih (fun p h => hr p (by simp [h])))

theorem filterMap {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) (f : α → Option γ) (g : β → Option γ)
    (same : ∀ a b, r a b → f a = g b) : (xs.filterMap f).Perm (ys.filterMap g) := by
  simpa only [List.filterMap_map, Function.comp_def, id_eq] using
    (h.map f g same).filterMap id

end Permuted

theorem Reorder.items {d d' : Design} (h : Reorder d d') :
    Permuted ItemReorder d.items d'.items := by
  obtain ⟨pairs, left, right, related⟩ := h.2.2
  exact ⟨pairs, left, right, fun pair member => (related pair member).1⟩

namespace StmtReorder

theorem definition {s s' : Stmt} (h : StmtReorder s s') :
    Rules.definition s = Rules.definition s' := by cases h <;> rfl

theorem exprs {s s' : Stmt} (h : StmtReorder s s') :
    (Rules.stmtExprs s).Perm (Rules.stmtExprs s') := by
  cases h with
  | same => exact .refl _
  | inst _ _ _ _ _ hp => exact hp.map Prod.snd

end StmtReorder

namespace ItemReorder

theorem name {i i' : Item} (h : ItemReorder i i') :
    Typed.itemName i = Typed.itemName i' := by cases h <;> simp_all [Typed.itemName]

theorem ports {i i' : Item} (h : ItemReorder i i') :
    Typed.itemPorts i = Typed.itemPorts i' := by cases h <;> simp_all [Typed.itemPorts]

theorem scope {i i' : Item} (h : ItemReorder i i') :
    (Rules.scopeNames i).Perm (Rules.scopeNames i') := by
  cases h with
  | module m m' _ _ ports body =>
    unfold Rules.scopeNames
    simp only [Typed.itemPorts, ports]
    apply List.Perm.append_left
    have hp := body.map Rules.definition Rules.definition (fun _ _ h => h.definition)
    simpa only [List.filterMap_map, Function.comp_def, id_eq] using hp.filterMap id
  | extern e e' _ _ ports _ => simp [Rules.scopeNames, Typed.itemPorts, ports]

end ItemReorder

end Silicon.Core
