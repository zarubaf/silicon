import Silicon.Core.Semantics.NamedLocal

/-! Memory write syntax follows its owner and its explicit priority port. -/
namespace Silicon.Core.Semantics

theorem write_member_iff (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name : String) (width depth : Nat) (clock : String)
    (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body)
    (pos : Pos) (port : Nat) (addr data enable : Core.Expr) :
    Core.Stmt.write pos name port addr data enable ∈ m.erase.body ↔
      ∃ write ∈ writes, writeSyntax name write = .write pos name port addr data enable := by
  constructor
  · intro raw
    obtain ⟨equation, he, index, stmt, part, erased⟩ :=
      (Ownership.mem_equationsErase m.body _).mp raw
    cases equation <;> simp only [Typed.Equation.parts, List.mem_cons, List.not_mem_nil,
      or_false] at part
    case reg i p n w clock target reset ni np next =>
      rcases part with part | part <;> cases part <;> cases erased
    case mem j q n w size clock' target' writes' =>
      rcases part with part | part
      · cases part; cases erased
      · obtain ⟨write, hw, part⟩ := List.mem_map.mp part
        cases part
        have fields := Core.Stmt.write.inj erased
        have names : n = name := fields.2.1
        subst n
        have eq := equation_unique d.design d.wellFormed m hm _ _ he member rfl
        cases eq
        exact ⟨write, hw, erased⟩
    all_goals cases part; cases erased
  · rintro ⟨write, hw, erased⟩
    exact (Ownership.mem_equationsErase m.body _).mpr
      ⟨_, member, write.index,
        .write write.pos name write.port width depth target write.addr write.data write.enable,
        by exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨write, hw, rfl⟩), erased⟩

private theorem syntax_nodup (name : String) (writes : List (Typed.Write ctx width depth))
    (unique : (writes.map Typed.Write.port).Nodup) :
    (writes.map (writeSyntax name)).Nodup := by
  simp only [List.Nodup, List.pairwise_map] at unique ⊢
  apply unique.imp
  intro a b ne eq
  exact ne (Core.Stmt.write.inj eq).2.2.1

theorem writeSyntax_perm (d d' : CertifiedDesign) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (body : Permuted StmtReorder m.erase.body m'.erase.body)
    (i i' : Nat) (p p' : Pos) (name : String) (width depth : Nat) (clock clock' : String)
    (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (target' : m'.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (writes' : List (Typed.Write m'.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body)
    (member' : .mem i' p' name width depth clock' target' writes' ∈ m'.body) :
    (writes.map (writeSyntax name)).Perm (writes'.map (writeSyntax name)) := by
  apply (List.perm_ext_iff_of_nodup
    (syntax_nodup name writes (typed_write_ports_nodup d m hm i p name width depth clock
      target writes member))
    (syntax_nodup name writes' (typed_write_ports_nodup d' m' hm' i' p' name width depth clock'
      target' writes' member'))).mpr
  intro stmt
  constructor
  · intro hs
    obtain ⟨write, hw, rfl⟩ := List.mem_map.mp hs
    have raw := (write_member_iff d m hm i p name width depth clock target writes member
      write.pos write.port write.addr.erase write.data.erase write.enable.erase).mpr
        ⟨write, hw, rfl⟩
    obtain ⟨s, hs, rel⟩ := body.left raw
    cases rel
    obtain ⟨write', hw', eq⟩ := (write_member_iff d' m' hm' i' p' name width depth clock'
      target' writes' member' _ _ _ _ _).mp hs
    exact List.mem_map.mpr ⟨write', hw', eq⟩
  · intro hs
    obtain ⟨write, hw, rfl⟩ := List.mem_map.mp hs
    have raw := (write_member_iff d' m' hm' i' p' name width depth clock' target' writes' member'
      write.pos write.port write.addr.erase write.data.erase write.enable.erase).mpr
        ⟨write, hw, rfl⟩
    obtain ⟨s, hs, rel⟩ := body.right raw
    cases rel
    obtain ⟨write', hw', eq⟩ := (write_member_iff d m hm i p name width depth clock
      target writes member _ _ _ _ _).mp hs
    exact List.mem_map.mpr ⟨write', hw', eq⟩

private def evalWriteSyntax (ctx : Typed.Ctx) (values : NamedValues) (memories : NamedMemories)
    (width depth : Nat) : Core.Stmt → WriteValues width
  | .write _ _ port addr data enable =>
    (port, (evalNamedExpr ctx values memories addr (Typed.addressWidth depth)).getD 0,
      BitVec.ofNat width ((evalNamedExpr ctx values memories data width).getD 0),
      BitVec.ofNat 1 ((evalNamedExpr ctx values memories enable 1).getD 0))
  | _ => (0, 0, 0, 0)

private theorem evalWriteSyntax_typed (values : NamedValues) (memories : NamedMemories)
    (name : String) (write : Typed.Write ctx width depth) :
    evalWriteSyntax ctx values memories width depth (writeSyntax name write) =
      evalWrite (values.valuation ctx) (memories.typed ctx) write := by
  simp [evalWriteSyntax, writeSyntax, evalNamedExpr_typed, evalWrite]

theorem evalWrites_perm {ctx ctx' : Typed.Ctx}
    (lookup : ∀ node, ctx.lookup node = ctx'.lookup node)
    (values : NamedValues) (memories : NamedMemories) (name : String)
    (writes : List (Typed.Write ctx width depth)) (writes' : List (Typed.Write ctx' width depth))
    (perm : (writes.map (writeSyntax name)).Perm (writes'.map (writeSyntax name))) :
    (writes.map (evalWrite (values.valuation ctx) (memories.typed ctx))).Perm
      (writes'.map (evalWrite (values.valuation ctx') (memories.typed ctx'))) := by
  have mapped := perm.map (evalWriteSyntax ctx values memories width depth)
  have congr : evalWriteSyntax ctx values memories width depth =
      evalWriteSyntax ctx' values memories width depth := by
    funext stmt
    cases stmt <;> simp only [evalWriteSyntax]
    simp only [evalNamedExpr_lookup_congr lookup]
  simp only [List.map_map, Function.comp_def] at mapped
  have left : (writes.map fun write =>
      evalWriteSyntax ctx values memories width depth (writeSyntax name write)) =
      writes.map (evalWrite (values.valuation ctx) (memories.typed ctx)) :=
    List.map_congr_left fun write _ => evalWriteSyntax_typed values memories name write
  have right : (writes'.map fun write =>
      evalWriteSyntax ctx values memories width depth (writeSyntax name write)) =
      writes'.map (evalWrite (values.valuation ctx') (memories.typed ctx')) := by
    apply List.map_congr_left
    intro write _
    rw [congr, evalWriteSyntax_typed]
  rw [left, right] at mapped
  exact mapped

end Silicon.Core.Semantics
