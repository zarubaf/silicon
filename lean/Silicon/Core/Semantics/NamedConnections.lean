import Silicon.Core.Semantics.NamedChild

/-! A permutation preserves the one expression connected to each input port. -/
namespace Silicon.Core.Semantics

private theorem lookup_perm_single (xs ys : List (String × α)) (perm : xs.Perm ys)
    (name : String) (one : (xs.filter (fun x => x.1 == name)).length = 1)
    (a b : α) (ha : xs.lookup name = some a) (hb : ys.lookup name = some b) : a = b := by
  have member (zs : List (String × α)) (v : α) (h : zs.lookup name = some v) :
      (name, v) ∈ zs := by
    obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp h
    simp
  have ma : (name, a) ∈ xs.filter (fun x => x.1 == name) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]
    exact member xs a ha
  have mb : (name, b) ∈ xs.filter (fun x => x.1 == name) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]
    exact perm.mem_iff.mpr (member ys b hb)
  obtain ⟨entry, h⟩ := List.length_eq_one_iff.mp one
  rw [h] at ma mb
  exact congrArg Prod.snd ((List.eq_of_mem_singleton ma).trans
    (List.eq_of_mem_singleton mb).symm)

theorem connectionExpr_erase_reorder (d d' : CertifiedDesign)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (i i' : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    (member' : .inst i' p name child inputs' ∈ m'.body)
    (perm : (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)))
    (port : Port) (hp : port ∈ m.interfaces child) (hp' : port ∈ m'.interfaces child)
    (dir : port.dir = .input) :
    (connectionExpr d m hm i p name child inputs member ⟨port, hp, dir⟩).erase =
      (connectionExpr d' m' hm' i' p name child inputs' member' ⟨port, hp', dir⟩).erase := by
  apply lookup_perm_single _ _ perm port.name
    (by simpa only [List.filter_map, List.length_map, Function.comp_def] using
      typed_input_count d m hm i p name child inputs member ⟨port, hp, dir⟩)
  · exact connectionExpr_lookup d m hm i p name child inputs member ⟨port, hp, dir⟩
  · exact connectionExpr_lookup d' m' hm' i' p name child inputs' member' ⟨port, hp', dir⟩

theorem connectionValues_reorder (d d' : CertifiedDesign)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (lookup : ∀ node, m.ctx.lookup node = m'.ctx.lookup node)
    (values : NamedValues) (memories : NamedMemories)
    (i i' : Nat) (p : Pos) (name child : String)
    (inputs : List (Connection m.ctx (m.interfaces child)))
    (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    (member' : .inst i' p name child inputs' ∈ m'.body)
    (perm : (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)))
    (port : Port) (hp : port ∈ m.interfaces child) (hp' : port ∈ m'.interfaces child)
    (dir : port.dir = .input) :
    connectionValues d m hm (values.valuation m.ctx) (memories.typed m.ctx)
      ⟨.inst i p name child inputs, member⟩ ⟨port, hp, dir⟩ =
    connectionValues d' m' hm' (values.valuation m'.ctx) (memories.typed m'.ctx)
      ⟨.inst i' p name child inputs', member'⟩ ⟨port, hp', dir⟩ := by
  apply evalExpr_erase_eq lookup
  exact connectionExpr_erase_reorder d d' m m' hm hm' i i' p name child inputs inputs'
    member member' perm port hp hp' dir

theorem portValues_heq {ports ports' : List Port} {dir : PortDir}
    (same : ports = ports') (a : PortValues ports dir) (b : PortValues ports' dir)
    (agree : ∀ p hp hp' hd, a ⟨p, hp, hd⟩ = b ⟨p, hp', hd⟩) : HEq a b := by
  subst ports'
  apply heq_of_eq
  funext p
  exact agree p.val p.property.1 p.property.1 p.property.2

theorem portValues_eq_of_heq {ports ports' : List Port} {dir : PortDir}
    (same : ports = ports') (a : PortValues ports dir) (b : PortValues ports' dir)
    (agree : HEq a b) (p : Port) (hp : p ∈ ports) (hp' : p ∈ ports') (hd : p.dir = dir) :
    a ⟨p, hp, hd⟩ = b ⟨p, hp', hd⟩ := by
  subst ports'
  cases agree
  rfl

end Silicon.Core.Semantics
