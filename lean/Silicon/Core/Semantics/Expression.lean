import Silicon.Core.Semantics.Value
import Silicon.Core.Typed

/-!
Expression evaluation uses the declared widths of all references.
Memory reads and writes check addresses against the declared depth.
-/
namespace Silicon.Core.Semantics

abbrev Valuation (ctx : Typed.Ctx) :=
  (node : Deps.Node) → (width : Nat) →
    ctx.lookup node = some (.value (.bits width)) → Value width

abbrev Memories (ctx : Typed.Ctx) :=
  (name : String) → (width depth : Nat) →
    ctx.lookup (.name name) = some (.memory width depth) → Fin depth → Value width

abbrev TyValue : Ty → Type
  | .clock => Unit
  | .bits width => Value width

/-! Clocks carry no data value. Each cycle has one edge. -/
def evalExpr (values : Valuation ctx) (memories : Memories ctx) :
    Typed.Expr ctx ty → TyValue ty
  | .ref _ node found => values node _ found
  | .clock .. => ()
  | .const _ width value => BitVec.ofNat width value
  | .un _ .not arg => ~~~(evalExpr values memories arg)
  | .bin _ op ordinary lhs rhs =>
    evalOp op ordinary (evalExpr values memories lhs) (evalExpr values memories rhs)
  | .concat _ lhs rhs _ => (evalExpr values memories lhs).append (evalExpr values memories rhs)
  | .icmp _ pred lhs rhs =>
    evalPred pred (evalExpr values memories lhs) (evalExpr values memories rhs)
  | .mux _ cond yes no =>
    if evalExpr values memories cond = 1 then evalExpr values memories yes
    else evalExpr values memories no
  | .extract _ arg lo count _ => (evalExpr values memories arg).extractLsb' lo count
  | .replicate _ arg count _ => (evalExpr values memories arg).replicate count
  | .read _ name found addr => memoryRead (memories name _ _ found)
      (evalExpr values memories addr).toNat

/-! An expression depends only on its named reads and the current memory state. -/
theorem evalExpr_congr (a b : Valuation ctx) (memories : Memories ctx)
    (e : Typed.Expr ctx ty)
    (agree : ∀ node ∈ Deps.reads e.erase, ∀ width found,
      a node width found = b node width found) :
    evalExpr a memories e = evalExpr b memories e := by
  induction e with
  | ref p node found =>
    apply agree node
    cases node <;> simp [Typed.Expr.erase, Deps.reads]
  | clock => rfl
  | const => rfl
  | un p op arg ih =>
    cases op
    simp only [evalExpr, ih agree]
  | bin p op ordinary lhs rhs il ir =>
    have hl := il (fun node hn => agree node (List.mem_append_left _ hn))
    have hr := ir (fun node hn => agree node (List.mem_append_right _ hn))
    simp only [evalExpr, hl, hr]
  | concat p lhs rhs bound il ir =>
    have hl := il (fun node hn => agree node (List.mem_append_left _ hn))
    have hr := ir (fun node hn => agree node (List.mem_append_right _ hn))
    simp only [evalExpr, hl, hr]
  | icmp p pred lhs rhs il ir =>
    have hl := il (fun node hn => agree node (List.mem_append_left _ hn))
    have hr := ir (fun node hn => agree node (List.mem_append_right _ hn))
    simp only [evalExpr, hl, hr]
  | mux p cond yes no ic iy ino =>
    have hc := ic (fun node hn => agree node
      (List.mem_append_left _ (List.mem_append_left _ hn)))
    have hy := iy (fun node hn => agree node
      (List.mem_append_left _ (List.mem_append_right _ hn)))
    have hn := ino (fun node hn => agree node (List.mem_append_right _ hn))
    simp only [evalExpr, hc, hy, hn]
  | extract p arg lo count bound ih => simp only [evalExpr, ih agree]
  | replicate p arg count bound ih => simp only [evalExpr, ih agree]
  | read p name found addr ih => simp only [evalExpr, ih agree]

/-! Reset values take priority over the next-state expression at the clock edge. -/
def nextRegister (values : Valuation ctx) (memories : Memories ctx)
    (reset : Option (Typed.Reset ctx width)) (next : Typed.Expr ctx (.bits width)) :
    Value width :=
  match reset with
  | some r => if evalExpr values memories r.signal = 1 then evalExpr values memories r.value
    else evalExpr values memories next
  | none => evalExpr values memories next

/-! Higher write ports run last. All operands read the same current-cycle valuation. -/
def nextMemory (values : Valuation ctx) (memories : Memories ctx)
    (memory : Fin depth → Value width) (writes : List (Typed.Write ctx width depth)) :
    Fin depth → Value width :=
  (writes.mergeSort (fun a b => a.port ≤ b.port)).foldl
    (fun current (write : Typed.Write ctx width depth) =>
    memoryWrite current (evalExpr values memories write.addr).toNat
      (evalExpr values memories write.data) (evalExpr values memories write.enable)) memory

end Silicon.Core.Semantics
