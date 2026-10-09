import Silicon.Core.Proof.Lower.Names

/-!
Operand substitution changes names without changing values.
The operation lemmas use the same bit-vector functions as core expressions.
-/
namespace Silicon.Core.LowerProof

open Mlir

theorem substitute_eval (rename : String → String) (op : Mlir.Op) (env : Mlir.Env) :
    (Lower.substitute rename op).eval env = op.eval (env ∘ rename) := by
  cases op <;> rfl

theorem substitute_nextValue (rename : String → String) (op : Mlir.Op) (env : Mlir.Env) :
    (Lower.substitute rename op).nextValue env = op.nextValue (env ∘ rename) := by
  cases op with
  | compreg next clk reset ty => cases reset <;> rfl
  | _ => rfl

theorem eval_constant (env : Mlir.Env) (w n : Nat) (bound : n < 2 ^ w) :
    (Op.constant w n).eval env = some (.bits w (BitVec.ofNat w n)) := by
  simp [Op.eval, bound]

theorem eval_binary (env : Mlir.Env) (op : BinOp) (ordinary : op ≠ .concat)
    (a b : String) (x y : BitVec w)
    (ha : env a = some (.bits w x)) (hb : env b = some (.bits w y)) :
    (Op.comb (Lower.binary op ordinary) a b w).eval env =
      some (.bits w (Semantics.evalOp op ordinary x y)) := by
  simp [Op.eval, Env.bits, Value.asBits, ha, hb]

theorem eval_not (env : Mlir.Env) (a ones : String) (x : BitVec w)
    (ha : env a = some (.bits w x))
    (ho : env ones = some (.bits w (BitVec.ofNat w (2 ^ w - 1)))) :
    (Op.comb .xor a ones w).eval env = some (.bits w (~~~x)) := by
  have h := eval_binary env .xor (by decide) a ones x
    (BitVec.ofNat w (2 ^ w - 1)) ha ho
  have ones_eq : BitVec.ofNat w (2 ^ w - 1) = BitVec.allOnes w := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) (by decide : 0 < 1))]
  simpa [Lower.binary, Semantics.evalOp, ones_eq] using h

theorem eval_predicate (env : Mlir.Env) (pred : Core.Pred) (a b : String) (x y : BitVec w)
    (ha : env a = some (.bits w x)) (hb : env b = some (.bits w y)) :
    (Op.icmp (Lower.predicate pred) a b w).eval env =
      some (.bits 1 (Semantics.evalPred pred x y)) := by
  simp [Op.eval, Env.bits, Value.asBits, ha, hb]

theorem eval_mux (env : Mlir.Env) (cond a b : String) (c : BitVec 1) (x y : BitVec w)
    (hc : env cond = some (.bits 1 c))
    (ha : env a = some (.bits w x)) (hb : env b = some (.bits w y)) :
    (Op.mux cond a b (.int w)).eval env = some (.bits w (Semantics.evalMux c x y)) := by
  simp [Op.eval, Env.bits, Env.typed, Value.asBits, Value.ty, hc, ha, hb,
    Semantics.evalMux]
  split <;> rfl

theorem eval_concat (env : Mlir.Env) (a b : String) (x : BitVec wa) (y : BitVec wb)
    (ha : env a = some (.bits wa x)) (hb : env b = some (.bits wb y)) :
    (Op.concat a b wa wb).eval env = some (.bits (wa + wb) (Semantics.evalConcat x y)) := by
  simp [Op.eval, Env.bits, Value.asBits, ha, hb]

theorem eval_extract (env : Mlir.Env) (a : String) (x : BitVec w) (lo count : Nat)
    (ha : env a = some (.bits w x)) (bound : lo + count ≤ w) :
    (Op.extract a lo w count).eval env = some (.bits count (Semantics.evalExtract x lo count)) := by
  simp [Op.eval, Env.bits, Value.asBits, ha, bound]

theorem eval_replicate (env : Mlir.Env) (a : String) (x : BitVec w) (count : Nat)
    (ha : env a = some (.bits w x)) (positive : 0 < w) :
    (Op.replicate a w (w * count)).eval env =
      some (.bits (w * count) (Semantics.evalReplicate x count)) := by
  simp [Op.eval, Env.bits, Value.asBits, ha, Nat.mul_div_cancel_left count positive, positive]
  apply eq_of_heq
  apply HEq.trans (eqRec_heq _ _)
  have same (n k : Nat) (h : n = k) :
      HEq (Semantics.evalReplicate x n) (Semantics.evalReplicate x k) := by
    cases h
    rfl
  exact same _ _ (Nat.mul_div_cancel_left count positive)

theorem guarded_read (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (memory : Fin c.depth → BitVec c.width) (agree : MemModelProof.Agrees c words memory)
    (address : BitVec (Typed.addressWidth c.depth)) :
    (if address.toNat < c.depth then Semantics.memoryRead words address.toNat else 0) =
      Semantics.memoryRead memory address.toNat := by
  by_cases h : address.toNat < c.depth
  · simp only [h, ↓reduceIte, Semantics.memoryRead,
      Nat.lt_of_lt_of_le h (MemModelProof.depth_bound c), ↓reduceDIte]
    exact agree ⟨address.toNat, h⟩
  · simp [Semantics.memoryRead, h]

theorem guard_bound (depth : Nat) (guard : depth ≠ 2 ^ Typed.addressWidth depth) :
    depth < 2 ^ Typed.addressWidth depth :=
  Nat.lt_of_le_of_ne (MemModelProof.depth_bound ⟨depth, 0, 0, 0⟩) guard

theorem guard_value (depth : Nat) (guard : depth ≠ 2 ^ Typed.addressWidth depth)
    (address : BitVec (Typed.addressWidth depth)) :
    Semantics.evalPred .ult address (BitVec.ofNat (Typed.addressWidth depth) depth) =
      BitVec.ofBool (address.toNat < depth) := by
  simp [Semantics.evalPred, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (guard_bound depth guard)]

theorem full_depth_read (c : MemConfig)
    (words : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width)
    (memory : Fin c.depth → BitVec c.width) (agree : MemModelProof.Agrees c words memory)
    (full : c.depth = 2 ^ Typed.addressWidth c.depth)
    (address : BitVec (Typed.addressWidth c.depth)) :
    Semantics.memoryRead words address.toNat = Semantics.memoryRead memory address.toNat := by
  have h : address.toNat < c.depth := Nat.lt_of_lt_of_eq address.isLt full.symm
  simpa [h] using guarded_read c words memory agree address

end Silicon.Core.LowerProof
