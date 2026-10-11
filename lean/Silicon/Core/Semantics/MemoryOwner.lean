-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Ownership

/-! Every typed memory read names a declared memory equation. -/
namespace Silicon.Core.Semantics.Ownership

open Typed

theorem memory_origin (m : Typed.Module) (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth)) :
    ∃ pos clock, Core.Stmt.mem pos name width depth clock ∈ m.erase.body := by
  rw [m.context_eq] at found
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp found
  have hm : (Deps.Node.name name, Kind.memory width depth) ∈
      contextFromPorts m.interfaces m.erase := by
    rw [show contextFromPorts m.interfaces m.erase = _ from he]
    simp
  simp only [contextFromPorts, List.mem_append] at hm
  rcases hm with hp | hs
  · obtain ⟨p, _, he⟩ := List.mem_map.mp hp
    split at he <;> cases he
  · obtain ⟨stmt, hs, he⟩ := List.mem_flatMap.mp hs
    cases stmt <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    case mem pos n w d clock =>
      cases he
      exact ⟨pos, clock, hs⟩
    case inst pos n child inputs =>
      obtain ⟨p, _, he⟩ := List.mem_filterMap.mp he
      split at he <;> cases he
    all_goals cases he

theorem mem_equation {ctx : Ctx} {ports : String → List Port}
    (body : List (Equation ctx ports)) (pos : Pos) (name : String)
    (width depth : Nat) (clock : String)
    (hm : Core.Stmt.mem pos name width depth clock ∈ equationsErase body) :
    ∃ index target writes,
      Equation.mem index pos name width depth clock target writes ∈ body := by
  obtain ⟨eq, he, index, typed, hp, hs⟩ := (mem_equationsErase body _).mp hm
  cases eq <;> simp only [Equation.parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  case reg i p n w clock target reset ni np ne =>
    rcases hp with hp | hp <;> cases hp <;> cases hs
  case mem i p n w depth clock target writes =>
    rcases hp with hp | hp
    · cases hp
      cases hs
      exact ⟨_, _, _, he⟩
    · obtain ⟨wr, _, hp⟩ := List.mem_map.mp hp
      cases hp
      cases hs
  all_goals cases hp; cases hs

theorem memory_equation (m : Typed.Module) (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth)) :
    ∃ index pos clock target writes,
      Equation.mem index pos name width depth clock target writes ∈ m.body := by
  obtain ⟨pos, clock, hm⟩ := memory_origin m name width depth found
  obtain ⟨index, target, writes, he⟩ := mem_equation m.body pos name width depth clock hm
  exact ⟨index, pos, clock, target, writes, he⟩

end Silicon.Core.Semantics.Ownership
