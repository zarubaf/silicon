import Silicon.Core.Proof.Lower.Expressions

/-!
Register operands use the current-cycle values, including memory reads in reset values.
Core solution uniqueness supplies the last step of a back-translation proof.
-/
namespace Silicon.Core.LowerProof

theorem next_register (vals : Mlir.Env) (values : Semantics.Valuation ctx)
    (memories : Semantics.Memories ctx) (next : Typed.Expr ctx (.bits width))
    (nextName clk : String) (clock : vals clk = some .clock)
    (operand : vals nextName = some (.bits width (Semantics.evalExpr values memories next))) :
    (Mlir.Op.compreg nextName clk none (.int width)).nextValue vals =
      some (.bits width (Semantics.nextRegister values memories none next)) := by
  simp [Mlir.Op.nextValue, Mlir.Env.typed, Mlir.Value.ty, clock, operand,
    Semantics.nextRegister]

theorem next_register_reset (vals : Mlir.Env) (values : Semantics.Valuation ctx)
    (memories : Semantics.Memories ctx) (next : Typed.Expr ctx (.bits width))
    (reset : Typed.Reset ctx width) (nextName clk signal value : String)
    (clock : vals clk = some .clock)
    (operand : vals nextName = some (.bits width (Semantics.evalExpr values memories next)))
    (resetSignal : vals signal = some (.bits 1 (Semantics.evalExpr values memories reset.signal)))
    (resetValue : vals value =
      some (.bits width (Semantics.evalExpr values memories reset.value))) :
    (Mlir.Op.compreg nextName clk (some (signal, value)) (.int width)).nextValue vals =
      some (.bits width (Semantics.nextRegister values memories (some reset) next)) := by
  simp [Mlir.Op.nextValue, Mlir.Env.typed, Mlir.Env.bits, Mlir.Value.ty, Mlir.Value.asBits,
    clock, operand, resetSignal, resetValue, Semantics.nextRegister, Semantics.evalMux]
  split <;> rfl

theorem backTranslation_eq_solution (d : Semantics.CertifiedDesign) (env)
    (m : Typed.Module) (hm) (s : Semantics.State d env m hm) (input : Semantics.Input m)
    (back : Semantics.Valuation m.ctx) (solves : Semantics.IsSolution d env m hm s input back) :
    back = Semantics.solution d env m hm s input := by
  obtain ⟨_, _, unique⟩ := Semantics.solution_unique d env m hm s input
  exact (unique back solves).trans
    (unique _ (Semantics.localSolution_isSolution d m hm
      (Semantics.designChildren d env m hm) s input)).symm

end Silicon.Core.LowerProof
