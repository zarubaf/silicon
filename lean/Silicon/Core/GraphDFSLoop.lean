import Silicon.Core.GraphDFS
import Silicon.Core.GraphFlood

/-!
An explicit frame stack runs the depth-first visit as a loop.
Deep graphs then use heap memory, not native stack frames.
-/
namespace Silicon.Core.GraphDFS

variable {α : Type} [BEq α] [Hashable α]

/-! A frame visits its pending nodes with its fuel. Then it finishes its node, if any. -/
structure Frame (α : Type) where
  node : Option α
  fuel : Nat
  pending : List α

def finish : Option α → State α → State α
  | none, state => state
  | some x, state => { state with order := x :: state.order }

/-! Each step consumes one unit of the step bound. All calls are tail calls. -/
def run (edges : α → List α) : Nat → List (Frame α) → State α → Option (State α)
  | _, [], state => some state
  | 0, _ :: _, _ => none
  | steps + 1, ⟨node, _, []⟩ :: rest, state => run edges steps rest (finish node state)
  | steps + 1, ⟨node, fuel, x :: xs⟩ :: rest, state =>
    if state.seen.contains x then run edges steps (⟨node, fuel, xs⟩ :: rest) state else
    match fuel with
    | 0 => none
    | fuel + 1 => run edges steps (⟨some x, fuel, edges x⟩ :: ⟨node, fuel + 1, xs⟩ :: rest)
        { state with seen := state.seen.insert x }

/-! The recursive visit gives the meaning of a frame stack. -/
def frames (edges : α → List α) : List (Frame α) → State α → Option (State α)
  | [], state => some state
  | ⟨node, fuel, pending⟩ :: rest, state => do
    let out ← visits (visit edges fuel) pending state
    frames edges rest (finish node out)

/-! Unseen nodes pay for the frames that they can push later. -/
def weight (edges : α → List α) (space : List α) (state : State α) : Nat :=
  ((space.filter fun x => !state.seen.contains x).map fun x => (edges x).length + 2).sum

def potential (edges : α → List α) (space : List α) (stack : List (Frame α))
    (state : State α) : Nat :=
  (stack.map fun f => f.pending.length + 1).sum + weight edges space state

variable [LawfulBEq α] [LawfulHashable α]

omit [LawfulHashable α] in
private theorem sum_insert (w : α → Nat) (seen : Std.HashSet α) (x : α) (space : List α) :
    ((space.filter fun y => !(x == y || seen.contains y)).map w).sum +
      (if x ∈ space ∧ seen.contains x = false then w x else 0) ≤
    ((space.filter fun y => !seen.contains y).map w).sum := by
  induction space with
  | nil => simp
  | cons y ys ih =>
    have mono : ((ys.filter fun y => !(x == y || seen.contains y)).map w).sum ≤
        ((ys.filter fun y => !seen.contains y).map w).sum := by
      split at ih <;> omega
    by_cases he : x = y
    · subst he
      cases hs : seen.contains x <;>
        simp only [List.filter_cons, BEq.rfl, Bool.true_or,
          Bool.not_true, Bool.false_eq_true, ite_false, hs, Bool.not_false, ite_true,
          List.map_cons, List.sum_cons, List.mem_cons, true_or, true_and,
          Bool.true_eq_false] <;> omega
    · have hb : (x == y) = false := by simp [he]
      have hm : (x ∈ y :: ys ∧ seen.contains x = false) ↔
          (x ∈ ys ∧ seen.contains x = false) := by simp [he]
      simp only [List.filter_cons, hb, Bool.false_or, hm]
      split
      · simp only [List.map_cons, List.sum_cons]
        omega
      · omega

private theorem weight_insert (edges : α → List α) (space : List α) (state : State α)
    (x : α) :
    weight edges space { state with seen := state.seen.insert x } +
      (if x ∈ space ∧ state.seen.contains x = false then (edges x).length + 2 else 0) ≤
    weight edges space state := by
  simpa only [weight, Std.HashSet.contains_insert] using
    sum_insert (fun x => (edges x).length + 2) state.seen x space

omit [LawfulBEq α] [LawfulHashable α] in
private theorem weight_finish (edges : α → List α) (space : List α) (node : Option α)
    (state : State α) : weight edges space (finish node state) = weight edges space state := by
  cases node <;> rfl

omit [LawfulBEq α] [LawfulHashable α] in
private theorem visit_seen (edges : α → List α) (fuel : Nat) (x : α) (state : State α)
    (h : state.seen.contains x = true) : visit edges fuel x state = some state := by
  unfold visit
  simp [h]

omit [LawfulBEq α] [LawfulHashable α] in
private theorem visit_unseen (edges : α → List α) (fuel : Nat) (x : α) (state : State α)
    (h : state.seen.contains x = false) : visit edges fuel x state = match fuel with
      | 0 => none
      | fuel + 1 => (visits (visit edges fuel) (edges x)
          { state with seen := state.seen.insert x }).bind
            fun out => some { out with order := x :: out.order } := by
  conv => lhs; unfold visit
  simp only [h, Bool.false_eq_true, ite_false]
  cases fuel <;> rfl

theorem run_eq (edges : α → List α) (space : List α)
    (closed : ∀ x, ∀ y ∈ edges x, y ∈ space) :
    ∀ steps stack state, (∀ f ∈ stack, ∀ x ∈ f.pending, x ∈ space) →
      potential edges space stack state ≤ steps →
      run edges steps stack state = frames edges stack state := by
  intro steps
  induction steps with
  | zero =>
    intro stack state _ bound
    cases stack with
    | nil => rfl
    | cons f rest =>
      simp only [potential, List.map_cons, List.sum_cons] at bound
      omega
  | succ steps ih =>
    intro stack state support bound
    match stack with
    | [] => rfl
    | ⟨node, fuel, []⟩ :: rest =>
      simp only [run, frames, visits, bind, Option.bind_some]
      apply ih
      · exact fun f hf => support f (List.mem_cons_of_mem _ hf)
      · simp only [potential, List.map_cons, List.sum_cons, List.length_nil,
          weight_finish] at bound ⊢
        omega
    | ⟨node, fuel, x :: xs⟩ :: rest =>
      have hx : x ∈ space := support ⟨node, fuel, x :: xs⟩ (by simp) x (by simp)
      by_cases hs : state.seen.contains x = true
      · simp only [run, hs, ite_true]
        rw [ih]
        · simp only [frames, visits, visit_seen edges fuel x state hs, bind, Option.bind_some]
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact fun y hy => support ⟨node, fuel, x :: xs⟩ (by simp) y
              (List.mem_cons_of_mem _ hy)
          · exact support f (List.mem_cons_of_mem _ hf)
        · simp only [potential, List.map_cons, List.sum_cons, List.length_cons] at bound ⊢
          omega
      · simp only [Bool.not_eq_true] at hs
        cases fuel with
        | zero => simp [run, hs, frames, visits, visit_unseen edges 0 x state hs]
        | succ fuel =>
          simp only [run, hs, Bool.false_eq_true, ite_false]
          rw [ih]
          · simp only [frames, visits, visit_unseen edges (fuel + 1) x state hs, bind]
            cases visits (visit edges fuel) (edges x)
                { state with seen := state.seen.insert x } <;> rfl
          · intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | rfl | hf
            · exact closed x
            · exact fun y hy => support ⟨node, fuel + 1, x :: xs⟩ (by simp) y
                (List.mem_cons_of_mem _ hy)
            · exact support f (List.mem_cons_of_mem _ hf)
          · have hw := weight_insert edges space state x
            simp only [hx, hs, and_self, ite_true] at hw
            simp only [potential, List.map_cons, List.sum_cons, List.length_cons] at bound ⊢
            omega

omit [LawfulBEq α] [LawfulHashable α] in
private theorem weight_le (edges : α → List α) (space : List α) (state : State α) :
    weight edges space state ≤ (space.map fun x => (edges x).length + 2).sum := by
  induction space with
  | nil => simp [weight]
  | cons y ys ih =>
    simp only [weight, List.filter_cons, List.map_cons, List.sum_cons] at ih ⊢
    split
    · simp only [List.map_cons, List.sum_cons]
      omega
    · omega

/-! The step bound covers the frames and the weight of every node of the space. -/
def orderLoop (edges : α → List α) (nodes : List α) (steps : Nat) : List α :=
  ((run edges steps [⟨none, nodes.length + 1, nodes⟩] { seen := {}, order := [] }).map
    State.order).getD []

theorem orderLoop_eq (edges : α → List α) (nodes space : List α)
    (closed : ∀ x, ∀ y ∈ edges x, y ∈ space) (support : ∀ x ∈ nodes, x ∈ space)
    (steps : Nat)
    (bound : nodes.length + 1 + (space.map fun x => (edges x).length + 2).sum ≤ steps) :
    orderLoop edges nodes steps = order edges nodes := by
  have hw := weight_le edges space { seen := {}, order := [] }
  rw [orderLoop, run_eq edges space closed steps _ _ (by simpa using support)
    (by simp only [potential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil];
        omega)]
  simp only [frames, bind, order]
  cases visits (visit edges (nodes.length + 1)) nodes { seen := {}, order := [] } <;> rfl

def fillLoop (edges : α → List α) (fuel : Nat) (root : α) (seen : Std.HashSet α)
    (steps : Nat) : List α × Std.HashSet α :=
  let out := (run edges steps [⟨none, fuel, [root]⟩] { seen := seen, order := [] }).getD
    { seen := {}, order := [] }
  (out.order, out.seen)

theorem fillLoop_eq (edges : α → List α) (space : List α)
    (closed : ∀ x, ∀ y ∈ edges x, y ∈ space) (fuel : Nat) (root : α)
    (seen : Std.HashSet α) (steps : Nat)
    (bound : (space.map fun x => (edges x).length + 2).sum + (edges root).length + 4 ≤
      steps) :
    fillLoop edges fuel root seen steps = GraphFlood.fill edges fuel root seen := by
  have hw := weight_le edges (root :: space) { seen := seen, order := [] }
  simp only [List.map_cons, List.sum_cons] at hw
  rw [fillLoop, run_eq edges (root :: space)
    (fun x y hy => List.mem_cons_of_mem _ (closed x y hy)) steps _ _ (by simp)
    (by simp only [potential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.length_singleton]
        omega)]
  simp only [frames, visits, bind, GraphFlood.fill]
  cases visit edges fuel root { seen := seen, order := [] } <;> rfl

end Silicon.Core.GraphDFS
