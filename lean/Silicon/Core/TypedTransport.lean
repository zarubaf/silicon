import Silicon.Core.Typed

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
