import Silicon.Core.Proof.Lower.StatementImage

/-!
Distinct core value nodes of a checked module have distinct MLIR names. The core value at a
name is therefore well defined.
-/
namespace Silicon.Core.LowerProof

open Semantics

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

theorem scope_legal (x : String) (hx : x ∈ Rules.scopeNames (.module m.erase)) :
    Rules.invalidName x = false :=
  ((module_wf raw t h).1.2 (.module m.erase) (module_item raw t h m hm)).2 x hx

/-- Each name and instance owner in the context is a source name. -/
theorem ctx_owner_legal (node : Deps.Node) (kind : Typed.Kind)
    (found : m.ctx.lookup node = some kind) : match node with
      | .name x => Rules.invalidName x = false
      | .port i _ => Rules.invalidName i = false := by
  have member := lookup_member _ _ _ found
  rw [m.context_eq] at member
  rcases context_member _ _ _ _ member with ⟨p, hp, same, _⟩ | ⟨stmt, hs, decl⟩
  · subst same
    exact scope_legal raw t h m hm _ (List.mem_append_left _ (List.mem_map_of_mem hp))
  · have defined (n : String) (hn : Rules.definition stmt = some n) :
        Rules.invalidName n = false :=
      scope_legal raw t h m hm _ (List.mem_append_right _ (List.mem_filterMap.mpr ⟨stmt, hs, hn⟩))
    cases stmt with
    | let_ _ n _ _ | reg _ n _ _ _ =>
      obtain ⟨rfl, _⟩ := decl
      exact defined n rfl
    | mem _ n _ _ _ =>
      obtain ⟨rfl, _⟩ := decl
      exact defined n rfl
    | inst _ n _ _ =>
      obtain ⟨_, _, _, rfl, _⟩ := decl
      exact defined n rfl
    | _ => exact decl.elim

theorem valueName_injective (a b : Deps.Node) (ka kb : Typed.Kind)
    (fa : m.ctx.lookup a = some ka) (fb : m.ctx.lookup b = some kb)
    (same : Lower.valueName (Lower.registers m) a = Lower.valueName (Lower.registers m) b) :
    a = b := by
  have la := ctx_owner_legal raw t h m hm a ka fa
  have lb := ctx_owner_legal raw t h m hm b kb fb
  cases a with
  | name x =>
    cases b with
    | name y =>
      simp only at la lb
      simp only [Lower.valueName] at same
      split at same <;> split at same
      · rw [register_name_injective same]
      · exact absurd same.symm (source_ne_register y x lb)
      · exact absurd same (source_ne_register x y la)
      · rw [same]
    | port i q =>
      simp only at la lb
      simp only [Lower.valueName] at same
      split at same
      · exact absurd same (register_ne_result x i q la)
      · exact absurd same (source_ne_result x i q la)
  | port i q =>
    cases b with
    | name y =>
      simp only at la lb
      simp only [Lower.valueName] at same
      split at same
      · exact absurd same.symm (register_ne_result y i q lb)
      · exact absurd same.symm (source_ne_result y i q lb)
    | port j r =>
      simp only at la lb
      simp only [Lower.valueName] at same
      obtain ⟨rfl, rfl⟩ := result_name_injective la lb same
      rfl

end

/-- The core value at an MLIR name of a core node. Other names get a clock. -/
noncomputable def coreAt (m : Typed.Module) (values : Valuation m.ctx) (y : String) :
    Mlir.Value := by
  classical
  exact if h : ∃ r : ValueRef m.ctx, Lower.valueName (Lower.registers m) r.node = y then
    .bits h.choose.width (values h.choose.node h.choose.width h.choose.found) else .clock

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)
include h hm

theorem coreAt_node (values : Valuation m.ctx) (node : Deps.Node) (w : Nat)
    (found : m.ctx.lookup node = some (.value (.bits w))) :
    coreAt m values (Lower.valueName (Lower.registers m) node) = .bits w (values node w found) := by
  classical
  have ex : ∃ r : ValueRef m.ctx, Lower.valueName (Lower.registers m) r.node =
      Lower.valueName (Lower.registers m) node := ⟨⟨node, w, found⟩, rfl⟩
  unfold coreAt
  split
  case isFalse absent => exact absurd ex absent
  rename_i ex
  have pick (r : ValueRef m.ctx) (hr : r.node = node) :
      Mlir.Value.bits r.width (values r.node r.width r.found) = .bits w (values node w found) := by
    obtain ⟨n, w', found'⟩ := r
    simp only at hr
    subst hr
    rw [found] at found'
    cases found'
    rfl
  exact pick _ (valueName_injective raw t h m hm _ node _ _ ex.choose.found found ex.choose_spec)

omit h hm in
theorem clock_port (y : String) (found : m.ctx.lookup (.name y) = some .clock) :
    ∃ p ∈ m.ports, p.name = y ∧ p.dir = .input ∧ p.ty = .clock := by
  have member := lookup_member _ _ _ found
  rw [m.context_eq] at member
  rcases context_member _ _ _ _ member with ⟨p, hp, same, kind⟩ | ⟨stmt, hs, decl⟩
  · cases same
    unfold portKind at kind
    split at kind
    · rename_i hc
      have hc' : p.ty = .clock ∧ p.dir = .input := by simpa using hc
      exact ⟨p, hp, rfl, hc'.2, hc'.1⟩
    · cases kind
  · cases stmt with
    | let_ | reg => obtain ⟨_, kind⟩ := decl; cases kind
    | mem => obtain ⟨_, kind⟩ := decl; cases kind
    | inst => obtain ⟨_, _, _, same, _⟩ := decl; cases same
    | _ => exact decl.elim

theorem coreAt_clock (values : Valuation m.ctx) (y : String)
    (found : m.ctx.lookup (.name y) = some .clock) : coreAt m values y = .clock := by
  classical
  unfold coreAt
  split
  case isFalse => rfl
  rename_i ex
  exfalso
  obtain ⟨r, hr⟩ := ex
  obtain ⟨p, hp, rfl, _, _⟩ := clock_port m y found
  have plain := valueName_plain (Lower.registers m) p.name (port_not_register raw t h m hm p hp)
  rw [← plain] at hr
  have same := valueName_injective raw t h m hm r.node (.name p.name) _ _ r.found found hr
  have := r.found
  rw [same, found] at this
  cases this

end

end Silicon.Core.LowerProof
