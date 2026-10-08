import Silicon.Core.Semantics.NamedExpression
import Silicon.Core.Semantics.WriteOrder

/-! Register updates use the same erased reset and next equations at each name. -/
namespace Silicon.Core.Semantics

theorem nextRegister_erase_eq {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (reset : Option (Typed.Reset ctx width))
    (reset' : Option (Typed.Reset ctx' width)) (next : Typed.Expr ctx (.bits width))
    (next' : Typed.Expr ctx' (.bits width))
    (resetEq : reset.map Typed.Reset.erase = reset'.map Typed.Reset.erase)
    (nextEq : next.erase = next'.erase) :
    nextRegister (values.valuation ctx) (memories.typed ctx) reset next =
      nextRegister (values.valuation ctx') (memories.typed ctx') reset' next' := by
  have nextValue := evalExpr_erase_eq lookup values memories next next' nextEq
  cases reset with
  | none =>
    cases reset' with
    | none => exact nextValue
    | some => cases resetEq
  | some reset =>
    cases reset' with
    | none => cases resetEq
    | some reset' =>
      have same := Option.some.inj resetEq
      have signal := congrArg Core.Reset.signal same
      have value := congrArg Core.Reset.value same
      have signalEq := evalExpr_erase_eq lookup values memories reset.signal reset'.signal signal
      have valueEq := evalExpr_erase_eq lookup values memories reset.value reset'.value value
      simp only [nextRegister, signalEq, valueEq, nextValue]

/-! A write ignores source indices and retains its explicit priority port. -/
def writeSyntax (name : String) (write : Typed.Write ctx width depth) : Core.Stmt :=
  .write write.pos name write.port write.addr.erase write.data.erase write.enable.erase

theorem evalWrite_erase_eq {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (name : String) (a : Typed.Write ctx width depth)
    (b : Typed.Write ctx' width depth) (same : writeSyntax name a = writeSyntax name b) :
    evalWrite (values.valuation ctx) (memories.typed ctx) a =
      evalWrite (values.valuation ctx') (memories.typed ctx') b := by
  have fields := Core.Stmt.write.inj same
  have addr := evalExpr_erase_eq lookup values memories a.addr b.addr fields.2.2.2.1
  have data := evalExpr_erase_eq lookup values memories a.data b.data fields.2.2.2.2.1
  have enable := evalExpr_erase_eq lookup values memories a.enable b.enable fields.2.2.2.2.2
  simp only [evalWrite, fields.2.2.1, addr, data, enable]

end Silicon.Core.Semantics
