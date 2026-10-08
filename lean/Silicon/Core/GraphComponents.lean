import Silicon.Core.GraphSCC
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! A reverse graph search assigns one label to each component. -/
namespace Silicon.Core.GraphComponents

open GraphReach

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α]

abbrev Labels (α : Type) [BEq α] [Hashable α] := Std.HashMap α Nat

def label (labels : Labels α) (n : α) : Nat := (labels[n]?).getD 0

def insertNodes (nodes : List α) (value : Nat) (labels : Labels α) : Labels α :=
  nodes.foldl (fun labels n => labels.insert n value) labels

theorem insertNodes_lookup [LawfulHashable α] (nodes : List α) (value : Nat)
    (labels : Labels α) (n : α) :
    (insertNodes nodes value labels)[n]? = if n ∈ nodes then some value else labels[n]? := by
  induction nodes generalizing labels with
  | nil => simp [insertNodes]
  | cons a nodes ih =>
    simp only [insertNodes, List.foldl_cons]
    change (insertNodes nodes value (labels.insert a value))[n]? = _
    rw [ih, Std.HashMap.getElem?_insert]
    by_cases ha : n = a
    · subst a; simp
    · simp [ha, Ne.symm ha]

theorem insertNodes_label [LawfulHashable α] (nodes : List α) (value : Nat)
    (labels : Labels α) (n : α) :
    label (insertNodes nodes value labels) n = if n ∈ nodes then value else label labels n := by
  simp only [label, insertNodes_lookup]
  split <;> rfl

/-! Unseen nodes have label zero. Each completed label identifies one connected component. -/
structure Partial (g : List (α × List α)) (nodes : List α) (seen : Std.HashSet α)
    (labels : Labels α) (next : Nat) : Prop where
  marked : ∀ n, seen.contains n = true ↔ 0 < label labels n
  support : ∀ n, 0 < label labels n → n ∈ nodes
  lower : ∀ n, 0 < label labels n → next < label labels n
  edge_order : ∀ x y, y ∈ (g.lookup x).getD [] → label labels y ≤ label labels x
  connected : ∀ x y, 0 < label labels x → label labels x = label labels y →
    Reachable g x y

variable [LawfulHashable α]
variable {g : List (α × List α)} {nodes : List α} {seen : Std.HashSet α}
variable {labels : Labels α} {next : Nat}

omit [LawfulBEq α] [LawfulHashable α] in
theorem Partial.closed (h : Partial g nodes seen labels next) :
    ∀ x y, seen.contains y = true → y ∈ (g.lookup x).getD [] →
      seen.contains x = true := by
  intro x y hy he
  apply (h.marked x).mpr
  have hy := (h.marked y).mp hy
  have ho := h.edge_order x y he
  omega

omit [LawfulBEq α] [LawfulHashable α] in
theorem Partial.decrease (h : Partial g nodes seen labels (next + 1)) :
    Partial g nodes seen labels next := by
  exact { h with lower := fun n hn => Nat.lt_trans (Nat.lt_succ_self _) (h.lower n hn) }

theorem Partial.extend (h : Partial g nodes seen labels (next + 1))
    (root : α) (fresh : List α) (seen' : Std.HashSet α)
    (members : ∀ n, n ∈ fresh ↔ seen.contains n = false ∧ Reachable g n root)
    (updated : ∀ n, seen'.contains n = true ↔ seen.contains n = true ∨ n ∈ fresh)
    (support : ∀ n ∈ fresh, n ∈ nodes)
    (connected : ∀ n ∈ fresh, Reachable g root n) :
    Partial g nodes seen' (insertNodes fresh (next + 1) labels) next := by
  have fresh_zero (n : α) (hn : n ∈ fresh) : label labels n = 0 := by
    have hs := (members n).mp hn |>.1
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hs' := (h.marked n).mpr hp
    rw [hs] at hs'
    contradiction
  have reach (n : α) (hn : n ∈ fresh) : Reachable g n root := (members n).mp hn |>.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [updated, insertNodes_label]
    by_cases hn : n ∈ fresh
    · simp [hn]
    · simp [hn, h.marked]
  · intro n hn
    rw [insertNodes_label] at hn
    split at hn
    · exact support n (by assumption)
    · exact h.support n hn
  · intro n hn
    rw [insertNodes_label] at hn ⊢
    by_cases hm : n ∈ fresh
    · simp [hm]
    · simp only [hm, ite_false] at hn ⊢
      have := h.lower n hn
      omega
  · intro x y he
    rw [insertNodes_label, insertNodes_label]
    by_cases hx : x ∈ fresh <;> by_cases hy : y ∈ fresh
    · simp [hx, hy]
    · simp only [hx, hy, ite_true, ite_false]
      have hz := fresh_zero x hx
      have ho := h.edge_order x y he
      omega
    · simp only [hx, hy, ite_true, ite_false]
      have hr : Reachable g x root := Reachable.trans g (Reachable.edge g he) (reach y hy)
      have hs : seen.contains x = true := by
        cases hs : seen.contains x
        · exact False.elim (hx ((members x).mpr ⟨hs, hr⟩))
        · rfl
      have := h.lower x ((h.marked x).mp hs)
      omega
    · simpa [hx, hy] using h.edge_order x y he
  · intro x y hx he
    rw [insertNodes_label] at hx
    rw [insertNodes_label, insertNodes_label] at he
    by_cases hxf : x ∈ fresh <;> by_cases hyf : y ∈ fresh
    · exact Reachable.trans g (reach x hxf) (connected y hyf)
    · simp only [hxf, hyf, ite_true, ite_false] at he
      have := h.lower y (by omega)
      omega
    · simp only [hxf, hyf, ite_true, ite_false] at he hx
      have := h.lower x hx
      omega
    · simp only [hxf, hyf, ite_false] at hx he
      exact h.connected x y hx he

/-! The counter decreases once per root, so earlier components keep larger labels. -/
def assign (fill : α → Std.HashSet α → List α × Std.HashSet α) :
    List α → Nat → Std.HashSet α → Labels α → Std.HashSet α × Labels α
  | [], _, seen, labels => (seen, labels)
  | root :: rest, value, seen, labels =>
    if seen.contains root then assign fill rest (value - 1) seen labels else
    let (fresh, seen') := fill root seen
    assign fill rest (value - 1) seen' (insertNodes fresh value labels)

omit [Hashable α] [LawfulBEq α] [LawfulHashable α] in
private theorem source_mem (g : List (α × List α)) (nodes : List α)
    (edges : ∀ x y, y ∈ (g.lookup x).getD [] → x ∈ nodes ∧ y ∈ nodes)
    {x y : α} (hy : y ∈ nodes) (hr : Reachable g x y) : x ∈ nodes := by
  obtain ⟨length, hw⟩ := hr
  cases hw with
  | refl => exact hy
  | step he _ => exact (edges _ _ he).1

def Closed (g : List (α × List α)) (seen : Std.HashSet α) : Prop :=
  ∀ x y, seen.contains y = true → y ∈ (g.lookup x).getD [] → seen.contains x = true

theorem assign_spec (g : List (α × List α)) (nodes order : List α)
    (edges : ∀ x y, y ∈ (g.lookup x).getD [] → x ∈ nodes ∧ y ∈ nodes)
    (order_nodes : ∀ n ∈ order, n ∈ nodes)
    (fill : α → Std.HashSet α → List α × Std.HashSet α)
    (fill_spec : ∀ seen, Closed g seen → ∀ root ∈ nodes,
      (∀ n, n ∈ (fill root seen).1 ↔
        seen.contains n = false ∧ Reachable g n root) ∧
      (∀ n, (fill root seen).2.contains n = true ↔
        seen.contains n = true ∨ n ∈ (fill root seen).1))
    (ready : ∀ pre root post, order = pre ++ root :: post →
      ∀ seen : Std.HashSet α, Closed g seen →
      (∀ n ∈ pre, seen.contains n = true) → seen.contains root = false →
      ∀ y ∈ nodes, seen.contains y = false → Reachable g y root → Reachable g root y)
    (pre roots : List α) (layout : order = pre ++ roots)
    (seen : Std.HashSet α) (labels : Labels α) (value : Nat) (count : value = roots.length)
    (valid : Partial g nodes seen labels value)
    (marked : ∀ n ∈ pre, seen.contains n = true) :
    let out := assign fill roots value seen labels
    Partial g nodes out.1 out.2 0 ∧ ∀ n ∈ order, out.1.contains n = true := by
  induction roots generalizing pre seen labels value with
  | nil =>
    have hv : value = 0 := by simpa using count
    subst value
    refine ⟨valid, ?_⟩
    intro n hn
    exact marked n (by simpa [layout] using hn)
  | cons root rest ih =>
    have hv : value = rest.length + 1 := by simpa using count
    subst value
    have nextlayout : order = (pre ++ [root]) ++ rest := by simpa using layout
    have root_mem : root ∈ nodes := order_nodes root (by simp [layout])
    cases hs : seen.contains root
    · obtain ⟨members, updated⟩ := fill_spec seen valid.closed root root_mem
      have support (n : α) (hn : n ∈ (fill root seen).1) : n ∈ nodes :=
        source_mem g nodes edges root_mem ((members n).mp hn).2
      have connected (n : α) (hn : n ∈ (fill root seen).1) : Reachable g root n :=
        ready pre root rest layout seen valid.closed marked hs n (support n hn)
          ((members n).mp hn).1 ((members n).mp hn).2
      have extended := valid.extend root (fill root seen).1 (fill root seen).2
        members updated support connected
      have marked' : ∀ n ∈ pre ++ [root], (fill root seen).2.contains n = true := by
        intro n hn
        apply (updated n).mpr
        rcases List.mem_append.mp hn with hp | hr
        · exact Or.inl (marked n hp)
        · have he : n = root := by simpa using hr
          subst n
          exact Or.inr ((members root).mpr ⟨hs, Reachable.refl g root⟩)
      simpa [assign, hs] using ih (pre ++ [root]) nextlayout
        (fill root seen).2 (insertNodes (fill root seen).1 (rest.length + 1) labels)
        rest.length rfl extended marked'
    · have marked' : ∀ n ∈ pre ++ [root], seen.contains n = true := by
        intro n hn
        rcases List.mem_append.mp hn with hp | hr
        · exact marked n hp
        · simpa using (show n = root from by simpa using hr) ▸ hs
      simpa [assign, hs] using ih (pre ++ [root]) nextlayout seen labels rest.length rfl
        valid.decrease marked'

theorem Partial.empty (g : List (α × List α)) (nodes : List α) (next : Nat) :
    Partial g nodes {} {} next := by
  constructor <;> simp [label]

def components (fill : α → Std.HashSet α → List α × Std.HashSet α)
    (order : List α) : Labels α := (assign fill order order.length {} {}).2

theorem components_spec (g : List (α × List α)) (nodes order : List α)
    (edges : ∀ x y, y ∈ (g.lookup x).getD [] → x ∈ nodes ∧ y ∈ nodes)
    (order_nodes : ∀ n, n ∈ order ↔ n ∈ nodes)
    (fill : α → Std.HashSet α → List α × Std.HashSet α)
    (fill_spec : ∀ seen, Closed g seen → ∀ root ∈ nodes,
      (∀ n, n ∈ (fill root seen).1 ↔
        seen.contains n = false ∧ Reachable g n root) ∧
      (∀ n, (fill root seen).2.contains n = true ↔
        seen.contains n = true ∨ n ∈ (fill root seen).1))
    (ready : GraphSCC.ReadyOrder g nodes order) :
    let labels := components fill order
    (∀ x y, y ∈ (g.lookup x).getD [] → label labels y ≤ label labels x) ∧
    (∀ x ∈ nodes, ∀ y ∈ nodes, label labels x = label labels y → Reachable g x y) := by
  have prepared : ∀ pre root post, order = pre ++ root :: post →
      ∀ seen : Std.HashSet α, Closed g seen →
      (∀ n ∈ pre, seen.contains n = true) → seen.contains root = false →
      ∀ y ∈ nodes, seen.contains y = false → Reachable g y root → Reachable g root y := by
    intro pre root post layout seen closed marked unmarked y hy fresh reach
    apply ready (fun n => seen.contains n = true) ?_ pre root post layout marked
      (by simp [unmarked]) y hy (by simp [fresh]) reach
    intro x z hx hz
    obtain ⟨length, hw⟩ := hz
    induction hw with
    | refl => exact hx
    | step he _ ih => exact closed _ _ (ih hx) he
  have spec := assign_spec g nodes order edges (fun n hn => (order_nodes n).mp hn)
    fill fill_spec prepared [] order (by simp) {} {} order.length rfl
    (Partial.empty g nodes order.length) (by simp)
  refine ⟨spec.1.edge_order, ?_⟩
  intro x hx y _ he
  apply spec.1.connected x y ?_ he
  exact (spec.1.marked x).mp (spec.2 x ((order_nodes x).mpr hx))

end Silicon.Core.GraphComponents
