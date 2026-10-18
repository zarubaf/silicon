-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Elab
import Silicon.Source.Proof.Fuel.Inst

/-!
The fuel of the elaborator: a part of the theorem `eval_cost` of section 10.3 of the front-end
spec. The result of `Elab.elaborate` does not depend on spare fuel, and less fuel than an
elaboration uses gives `S015`.

The statement walk and the instantiations are in the mutual block of `Eval`, so
`Eval.Fuel.follows_all` covers them (`Proof.Fuel.Inst`). `observe_budget` is the budget boundary
of `Elab.observe` by `Eval.Fuel.observe_budget`. `elaborate_budget` is its projection to the
result.
-/
namespace Silicon.Source.Elab.Fuel

open Eval Eval.Fuel

/--
The budget boundary of `observe`. If the elaboration uses `u` units, each fuel from `u` gives
the same records, design, and units, and each fuel below `u` gives `S015`.
-/
theorem observe_budget {budget : Budget} {items : Array Resolve.Item}
    {digest : String → String} {pos : Pos} {top : Nat} {xs : List Resolve.Expr}
    {rs : Array Record} {d : Design} {u : Nat}
    (h : observe budget items digest pos top xs = (rs, .ok (d, u))) (F : Nat) :
    (u ≤ F → observe { budget with fuel := F } items digest pos top xs = (rs, .ok (d, u))) ∧
    (F < u → ∃ p m,
      (observe { budget with fuel := F } items digest pos top xs).2 = .error ⟨.S015, p, m⟩) := by
  refine Eval.Fuel.observe_budget (fun n n' => ?_) h F
  follows [(follows_all n).1 n', static_f, need_f, instantiate_f ((follows_all n).2.2.2 n'),
    arguments_f ((follows_all n).1 n') ((follows_all n).2.1 n')]

/--
The budget boundary of `elaborate`. If the elaboration uses `u` units, each fuel from `u` gives
the same design and units, and each fuel below `u` gives `S015`.
-/
theorem elaborate_budget {budget : Budget} {items : Array Resolve.Item}
    {digest : String → String} {pos : Pos} {top : Nat} {xs : List Resolve.Expr} {d : Design}
    {u : Nat} (h : elaborate budget items digest pos top xs = .ok (d, u)) (F : Nat) :
    (u ≤ F → elaborate { budget with fuel := F } items digest pos top xs = .ok (d, u)) ∧
    (F < u → ∃ p m,
      elaborate { budget with fuel := F } items digest pos top xs = .error ⟨.S015, p, m⟩) :=
  have r := observe_budget
    (Prod.ext rfl h : observe budget items digest pos top xs = (_, .ok (d, u))) F
  ⟨fun hu => congrArg Prod.snd (r.1 hu), r.2⟩

end Silicon.Source.Elab.Fuel
