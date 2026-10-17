-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Flatten
import Silicon.Core.Semantics.Expression
import Silicon.Source.Proof.StaticOps.Spine

/-!
The finite static operations of the evaluator agree with the core (section 7.4 of the front-end
spec). Each statement names a core row `e` with constant leaves and makes two claims:

- The static operation gives the value of `e`. `evalExpr` evaluates `e` in each context.
- `Flatten.lower` emits the erasure of `e` for the hardware node of the operation. Its
  operands are the literals that `Eval.lit` makes. `lower` runs in a state monad with the fuel.
  The claim is thus about its run from each state with enough fuel.

The evaluator runs `&&` and `||` by a short circuit in `Eval.eval`, not by `Eval.binary`. Their
statement thus gives the static result as `a && b` and `a || b`.

A shift count is static: an `Int` or a `UInt`. `Eval.hwShift` makes an `Int` literal of both,
and `Flatten.lower` takes that literal as a constant. A `resize` row needs `1 ≤ w` for a sign
extension, and a result of at most 65536 bits for an extension. `Eval.family` gives both bounds
to each finite type.

The rows that walk an aggregate by leaf take a list of hardware pairs with constant leaves. `==`
gives the chain `E` of `Eval.aggEq`, `!=` adds its `xor` node, and a hardware `if` gives one
`mux` node for each pair. The static result of `==` is the conjunction of the result `s` of the
static pairs and the static `==` of each hardware pair. `Flatten.lower` takes the chain as one
left spine (`Spine.runs_chain`). The claim about `lower` holds for at most 60 pairs. Then the
spine stays below the height 64, so the height rule binds no temporary. The condition of an `if`
is a constant here, so it gets no shared mark. The statements take the pairs and `s` as given:
no proof here ties them to the walk of `Eval.eqWalk` and `Eval.armWalk` (#286).

The rows of enums that unpack bits take a constant operand: the bits of `reinterpret(E, b)`, and
the payload of a binder leaf. `Eval.recast` and `Value.unpack` give the static result. A literal
gets no shared mark, so the hardware nodes read the constant directly.

The rows of a hardware `match` take a constant selector and the key constant of `keyLit`. A
select is the `icmp eq` node of `Eval.matchHw`, and the static `match` compares `Value.key`.
The row of `rest` takes the selects as constants. `lowerMatch` builds its `or` chain in a loop
(`ok_rest`), and the claim about `lower` holds for at most 60 selects. Then the chain stays
below the height 64, so the height rule binds no temporary. The row of `onehot` takes constant
selects, at most one of them 1, and constant values. `lowerMatch` lowers its operands in one loop
(`ok_push`) and builds its `or` chain in a second loop (`ok_onehot`). The claim about `lower`
holds for at most 30 arms. The statements take the selects and the values as given: no proof
here ties them to the walk of `Eval.matchHw` and `Eval.armWalk` (#286). Each select of
`Eval.matchHw` can have a shared mark (`Eval.shared`), and the rows here have none.
-/
namespace Silicon.Source.StaticOps

open Eval Flatten
open Core.Semantics (Valuation Memories)

local notation "ev" => Core.Semantics.evalExpr

/-! The typed core expression of the width `w`. -/
local notation "Ex" ctx:max w:max => Core.Typed.Expr ctx (Core.Ty.bits w)

/-! The finite type of a signedness and a width. -/
def finiteTy (s : Bool) (w : Nat) : Ty := if s then .sint w else .uint w

/-! A literal node, as `Eval.lit` and `Eval.hwShift` make it. -/
def litHw (p : Pos) (t : Ty) (v : Value) : Hw := Hw.mk p t (.lit v) []

/-! A literal node of a finite value. -/
def leaf (p : Pos) (s : Bool) (w : Nat) (x : BitVec w) : Hw := litHw p (finiteTy s w) (finite s w x)

/-!
`lower` emits the row `e` for the node `h`. Each run from a state with at least `n` units of
fuel succeeds with the expression `e`. This holds for each target and each root flag.
-/
def Lowers (h : Hw) (n : Nat) (e : Core.Expr) : Prop :=
  ∀ (target : Names.Path) (root : Bool) (st : Flatten.St), n ≤ st.fuel →
    ∃ lo st', (lower target root h).run st = .ok (lo, st') ∧ lo.expr = e

/-! A static operation and its row: each operand, the step, and the result. -/

/-- `+%`, `-%`, `*%`, `&`, `|`, and `^`: the row `bin c a b`. -/
def BinAgrees : Prop :=
  ∀ (op : BinOp) (c : Core.BinOp) (hk : c ≠ .concat) (s : Bool) (w : Nat) (x y : BitVec w)
    (st : Step) (v : Value), coreOp op = some c →
    binary op (finite s w x) (finite s w y) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .bin q c hk (.const q w x.toNat) (.const q w y.toNat)
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.bin op) [leaf p s w x, leaf p s w y]) 3
        (e (cpos p)).erase

/-- `==`, `!=`, `<`, `<=`, `>`, and `>=` on finite integers: the row `icmp k a b`. -/
def CmpAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (k : Core.Pred) (w : Nat) (x y : BitVec w) (st : Step)
    (v : Value), binOp op s = some (.inr k) →
    binary op (finite s w x) (finite s w y) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .icmp q k (.const q w x.toNat) (.const q w y.toNat)
    (∀ q, ∃ b, v = .bool b ∧ ev vals mems (e q) = BitVec.ofBool b) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin op) [leaf p s w x, leaf p s w y]) 3 (e (cpos p)).erase

/-! The constant of a Boolean. -/
local notation "bit" b:max => (if b then 1 else 0 : Nat)

/-- `==` and `!=` on `Bool`: the row `icmp k a b`. -/
def BoolCmpAgrees : Prop :=
  ∀ (op : BinOp) (k : Core.Pred) (a b : Bool) (st : Step) (v : Value),
    (op = .eq ∨ op = .ne) → binOp op false = some (.inr k) →
    binary op (.bool a) (.bool b) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .icmp q k (.const q 1 (bit a)) (.const q 1 (bit b))
    (∀ q, ∃ r, v = .bool r ∧ ev vals mems (e q) = BitVec.ofBool r) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin op) [litHw p .bool (.bool a), litHw p .bool (.bool b)])
        3 (e (cpos p)).erase

/-- `&&` and `||` on `Bool`: the row `bin c a b`. -/
def LogicAgrees : Prop :=
  ∀ (op : BinOp) (c : Core.BinOp) (hk : c ≠ .concat) (a b : Bool),
    (op = .land ∨ op = .lor) → binOp op false = some (.inl c) →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .bin q c hk (.const q 1 (bit a)) (.const q 1 (bit b))
    (∀ q, ev vals mems (e q) = BitVec.ofBool (if op = .land then a && b else a || b)) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin op) [litHw p .bool (.bool a), litHw p .bool (.bool b)])
        3 (e (cpos p)).erase

/-- `~`: the row `not a`. -/
def InvAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    unary .inv (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .un q .not (.const q w x.toNat)
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.un .inv) [leaf p s w x]) 2 (e (cpos p)).erase

/-- Unary `-`: the row `sub (const w 0) a`. -/
def NegAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    unary .neg (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w :=
      .bin q .sub (by decide) (.const q w 0) (.const q w x.toNat)
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.un .neg) [leaf p s w x]) 3 (e (cpos p)).erase

/-- `!` on `Bool`: the row `xor a (const 1 1)`. -/
def NotAgrees : Prop :=
  ∀ (b : Bool) (st : Step) (v : Value),
    unary .not (.bool b) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .bin q .xor (by decide) (.const q 1 (bit b)) (.const q 1 1)
    (∀ q, ∃ r, v = .bool r ∧ ev vals mems (e q) = BitVec.ofBool r) ∧
      ∀ p, Lowers (Hw.mk p .bool (.un .not) [litHw p .bool (.bool b)]) 3 (e (cpos p)).erase

/--
`<<` and `>>` with a static count `k`, an `Int` or a `UInt` operand `b`: the row
`c a (const w (min k w))`. `Eval.hwShift` makes the literal `Int` `k` of both counts.
-/
def ShiftAgrees : Prop :=
  ∀ (op : BinOp) (s : Bool) (c : Core.BinOp) (hk : c ≠ .concat) (w : Nat) (x : BitVec w)
    (b : Value) (k : Nat) (st : Step) (v : Value), (op = .shl ∨ op = .shr) →
    c = (if op == .shl then .shl else if s then .shrs else .shru) →
    (b = .int k ∨ ∃ (u : Nat) (y : BitVec u), b = .uint u y ∧ k = y.toNat) →
    binary op (finite s w x) b = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .bin q c hk (.const q w x.toNat) (.const q w (min k w))
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.bin op) [leaf p s w x, litHw p .int (.int k)]) 3
        (e (cpos p)).erase

/-- `resize` to the same width: the row is the operand. -/
def ResizeSameAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    resize (finiteTy s w) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .const q w x.toNat
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) .resize [leaf p s w x]) 1 (e (cpos p)).erase

/-- `resize` to a smaller width `n`: the row `extract a 0 n`. -/
def ResizeTruncAgrees : Prop :=
  ∀ (s : Bool) (n w : Nat) (hn : n < w) (x : BitVec w) (st : Step) (v : Value),
    resize (finiteTy s n) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx n := .extract q (.const q w x.toNat) 0 n (by omega)
    (∀ q, v = finite s n (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s n) .resize [leaf p s w x]) 2 (e (cpos p)).erase

/-- `resize` of a `UInt` to a larger width `n`: the row `concat (const (n - w) 0) a`. -/
def ResizeZextAgrees : Prop :=
  ∀ (n w : Nat) (hn : w < n) (hb : n ≤ 65536) (x : BitVec w) (st : Step) (v : Value),
    resize (.uint n) (.uint w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx (n - w + w) :=
      .concat q (.const q (n - w) 0) (.const q w x.toNat) (by omega)
    (∀ q, v = .uint n ((ev vals mems (e q)).cast (by omega))) ∧
      ∀ p, Lowers (Hw.mk p (.uint n) .resize [leaf p false w x]) 3 (e (cpos p)).erase

/--
`resize` of an `SInt` to a larger width `n`: the row
`concat (replicate (extract a (w - 1) 1) (n - w)) a`. The row uses the constant `a` twice.
-/
def ResizeSextAgrees : Prop :=
  ∀ (n w : Nat) (h0 : 1 ≤ w) (hn : w < n) (hb : n ≤ 65536) (x : BitVec w) (st : Step)
    (v : Value),
    resize (.sint n) (.sint w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let a (q : Core.Pos) : Ex ctx w := .const q w x.toNat
    let e (q : Core.Pos) : Ex ctx (1 * (n - w) + w) :=
      .concat q (.replicate q (.extract q (a q) (w - 1) 1 (by omega)) (n - w) (by omega)) (a q)
        (by omega)
    (∀ q, v = .sint n ((ev vals mems (e q)).cast (by omega))) ∧
      ∀ p, Lowers (Hw.mk p (.sint n) .resize [leaf p true w x]) 5 (e (cpos p)).erase

/-- `reinterpret` keeps the width: the row is the operand. -/
def ReinterpretAgrees : Prop :=
  ∀ (s r : Bool) (w : Nat) (x : BitVec w) (st : Step) (v : Value),
    reinterpret (finiteTy r w) (finite s w x) = .ok st → st.run () = .ok v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .const q w x.toNat
    (∀ q, v = finite r w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy r w) .reinterpret [leaf p s w x]) 1 (e (cpos p)).erase

/-! A pair of constant leaves of one type: two `Bool` leaves, or two finite leaves. -/
inductive Pair where
  | bool (a b : Bool)
  | fin (s : Bool) (w : Nat) (x y : BitVec w)

namespace Pair

def ty : Pair → Ty
  | .bool .. => .bool
  | .fin s w .. => finiteTy s w

def width : Pair → Nat
  | .bool .. => 1
  | .fin _ w .. => w

/-! The static values of the two leaves. -/
def left : Pair → Value
  | .bool a _ => .bool a
  | .fin s w x _ => finite s w x

def right : Pair → Value
  | .bool _ b => .bool b
  | .fin s w _ y => finite s w y

/-! The constants of the two leaves. -/
def lc : Pair → Nat
  | .bool a _ => bit a
  | .fin _ _ x _ => x.toNat

def rc : Pair → Nat
  | .bool _ b => bit b
  | .fin _ _ _ y => y.toNat

/-! The static value of a leaf of the pair with the bits `x`. -/
def value : (pr : Pair) → BitVec pr.width → Value
  | .bool .., x => .bool (x == 1)
  | .fin s w .., x => finite s w x

/-! The `icmp eq` node of the pair, as `Eval.leafPair` makes it. -/
def eqHw (pr : Pair) (p : Pos) : Hw :=
  Hw.mk p .bool (.bin .eq) [litHw p pr.ty pr.left, litHw p pr.ty pr.right]

/-! The row `icmp eq a_i b_i` of the pair. -/
def eqRow (pr : Pair) (q : Core.Pos) : Ex ctx 1 :=
  .icmp q .eq (.const q pr.width pr.lc) (.const q pr.width pr.rc)

end Pair

/-! The `and` node of the chain of `Eval.aggEq`. -/
def andHw (p : Pos) (e z : Hw) : Hw := Hw.mk p .bool (.bin .and) [e, z]

/--
The hardware value of `==` that `Eval.aggEq` makes from the pairs `ps`. `s` is the result of the
static pairs, if any exist. `E_0` is then the literal `s`, else the node of the first pair. Each
other node joins with `and`, in walk order.
-/
def eqHw (p : Pos) (s : Option Bool) (ps : List Pair) : Hw :=
  match s, ps.map (·.eqHw p) with
  | some b, ns => ns.foldl (andHw p) (litHw p .bool (.bool b))
  | none, n :: ns => ns.foldl (andHw p) n
  | none, [] => litHw p .bool (.bool true)

/-! The row `E` of `==`: `E_0` is `(const 1 s)` or `icmp eq a_0 b_0`, then the `and` chain. -/
def eqRow (q : Core.Pos) (s : Option Bool) (ps : List Pair) : Ex ctx 1 :=
  let andRow (e z : Ex ctx 1) : Ex ctx 1 := .bin q .and (by decide) e z
  match s, ps.map (·.eqRow q) with
  | some b, ns => ns.foldl andRow (.const q 1 (bit b))
  | none, n :: ns => ns.foldl andRow n
  | none, [] => .const q 1 1

/-! The static `==` of each pair of `ps` gives the matching Boolean of `rs`. -/
def PairsEqual : List Pair → List Bool → Prop
  | [], [] => True
  | pr :: ps, r :: rs =>
    (∃ st, binary .eq pr.left pr.right = .ok st ∧ st.run () = .ok (.bool r)) ∧ PairsEqual ps rs
  | _, _ => False

/--
`==` of an aggregate by leaf: the row `E`. `ps` holds the hardware pairs with constant leaves, and
`s` the result of the static pairs. The static result is the conjunction of `s` and the static
`==` of each pair. The claim about `lower` holds for at most 60 pairs: then the chain stays below
the height 64.
-/
def EqLeavesAgrees : Prop :=
  ∀ (s : Option Bool) (ps : List Pair) (rs : List Bool), ps ≠ [] → PairsEqual ps rs →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    (∀ q, ev vals mems (eqRow q s ps) = BitVec.ofBool (s.getD true && rs.all id)) ∧
      (ps.length ≤ 60 →
        ∀ p, Lowers (eqHw p s ps) (4 * ps.length + 1) (eqRow (ctx := ctx) (cpos p) s ps).erase)

/-- `!=` of an aggregate by leaf: the row `xor E (const 1 1)`, with `E` the row of `==`. -/
def NeLeavesAgrees : Prop :=
  ∀ (s : Option Bool) (ps : List Pair) (rs : List Bool), ps ≠ [] → PairsEqual ps rs →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .bin q .xor (by decide) (eqRow q s ps) (.const q 1 1)
    (∀ q, ev vals mems (e q) = BitVec.ofBool !(s.getD true && rs.all id)) ∧
      (ps.length ≤ 60 →
        ∀ p, Lowers (Hw.mk p .bool (.bin .xor) [eqHw p s ps, litHw p .bool (.bool true)])
          (4 * ps.length + 3) (e (cpos p)).erase)

/--
A hardware `if` by leaf: the row `mux c a_i b_i` of each hardware pair, with a constant
condition `c`. The static `if` gives the leaf of the arm that `c` selects.
-/
def IfLeafAgrees : Prop :=
  ∀ (c : Bool) (pr : Pair) {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx pr.width :=
      .mux q (.const q 1 (bit c)) (.const q pr.width pr.lc) (.const q pr.width pr.rc)
    (∀ q, (if c then pr.left else pr.right) = pr.value (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p pr.ty .mux [litHw p .bool (.bool c), litHw p pr.ty pr.left,
        litHw p pr.ty pr.right]) 4 (e (cpos p)).erase

/--
`reinterpret(E, b)`: the `tag` row `extract b 0 W` and the `payload` row `extract b W P`. The
static `reinterpret` of `Eval.recast` gives the enum value of the two rows. The claim about
`lower` needs `P` not 0: with `P` 0, `recast` gives `b` itself as the tag, with no node.
-/
def UnpackEnumAgrees : Prop :=
  ∀ (pos : Pos) (t : Ty) (w pw : Nat) (x : BitVec (w + pw)) (c : Eval.Ctx) (s s' : Eval.St)
    (v : Value),
    s.specs.widths t = some (w, pw) →
    recast pos t (.static (.uint (w + pw) x)) c s = .ok (.static v, s') →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let tag (q : Core.Pos) : Ex ctx w :=
      .extract q (.const q (w + pw) x.toNat) 0 w (by omega)
    let pay (q : Core.Pos) : Ex ctx pw :=
      .extract q (.const q (w + pw) x.toNat) w pw (by omega)
    (∀ q, v = .enum t w (ev vals mems (tag q)) pw (ev vals mems (pay q))) ∧
      (0 < pw → ∀ p, Lowers (Hw.mk p (.uint w) (.extract 0 w) [leaf p false (w + pw) x]) 2
          (tag (cpos p)).erase ∧
        Lowers (Hw.mk p (.uint pw) (.extract w pw) [leaf p false (w + pw) x]) 2
          (pay (cpos p)).erase)

/--
A finite leaf of a binder: the row `extract y o w` of the payload `y` of `P` bits, at the
offset `o` of the leaf. The static unpack `Value.unpack` of a static payload gives its value.
-/
def BinderLeafAgrees : Prop :=
  ∀ (specs : Specs) (d : Nat) (s : Bool) (w pw off : Nat) (h : off + w ≤ pw) (y : BitVec pw)
    (v : Value), Value.unpack specs y.toNat (d + 1) (finiteTy s w) off = some v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx w := .extract q (.const q pw y.toNat) off w h
    (∀ q, v = finite s w (ev vals mems (e q))) ∧
      ∀ p, Lowers (Hw.mk p (finiteTy s w) (.extract off w) [leaf p false pw y]) 2
        (e (cpos p)).erase

/-- A `Bool` leaf of a binder: the row `extract y o 1`, as for a finite leaf. -/
def BinderBoolAgrees : Prop :=
  ∀ (specs : Specs) (d pw off : Nat) (h : off + 1 ≤ pw) (y : BitVec pw) (v : Value),
    Value.unpack specs y.toNat (d + 1) .bool off = some v →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 := .extract q (.const q pw y.toNat) off 1 h
    (∀ q, ∃ r, v = .bool r ∧ ev vals mems (e q) = BitVec.ofBool r) ∧
      ∀ p, Lowers (Hw.mk p .bool (.extract off 1) [leaf p false pw y]) 2 (e (cpos p)).erase

/--
The select of a key `k` of a hardware `match` on a finite selector: the row `icmp eq a c`, with `c`
the constant of `keyLit`. The key is a value of the selector type, as the coverage check of
`matchArms` makes sure: it keeps its value through `BitVec.ofInt`. The static `match` compares
`Value.key` of the selector with `k`. A tag of an enum is a `UInt` selector.
-/
def SelectAgrees : Prop :=
  ∀ (s : Bool) (w : Nat) (x : BitVec w) (k : Int),
    Value.key (finite s w (BitVec.ofInt w k)) = some k →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 :=
      .icmp q .eq (.const q w x.toNat) (.const q w (BitVec.ofInt w k).toNat)
    (∀ q, ev vals mems (e q) = BitVec.ofBool (Value.key (finite s w x) == some k)) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin .eq) [leaf p s w x, keyLit p (finiteTy s w) k]) 3
        (e (cpos p)).erase

/-- The select of a key `k` of a hardware `match` on a `Bool` selector, as for a finite one. -/
def SelectBoolAgrees : Prop :=
  ∀ (b : Bool) (k : Int), (k = 0 ∨ k = 1) →
    ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    let e (q : Core.Pos) : Ex ctx 1 :=
      .icmp q .eq (.const q 1 (bit b)) (.const q 1 (bit (k == 1)))
    (∀ q, ev vals mems (e q) = BitVec.ofBool (Value.key (.bool b) == some k)) ∧
      ∀ p, Lowers (Hw.mk p .bool (.bin .eq) [litHw p .bool (.bool b), keyLit p .bool k]) 3
        (e (cpos p)).erase

/-! The `or` chain of constant bits over the row `e`, in list order. -/
def orRow (q : Core.Pos) (e : Ex ctx 1) (bs : List Bool) : Ex ctx 1 :=
  bs.foldl (fun e b => .bin q .or (by decide) e (.const q 1 (bit b))) e

/-! The node `rest` of `Eval.matchHw` over the constant selects `bs`. -/
def restHw (p : Pos) (bs : List Bool) : Hw :=
  Hw.mk p .bool .rest (bs.map fun b => litHw p .bool (.bool b))

/-! The row of `rest`: `xor (or (... (or s_0 s_1) ...) s_(n-1)) (const 1 1)`. -/
def restRow (q : Core.Pos) : List Bool → Ex ctx 1
  | [] => .const q 1 1
  | b :: bs => .bin q .xor (by decide) (orRow q (.const q 1 (bit b)) bs) (.const q 1 1)

/--
The select of the arm `_` of a hardware `match`: the row of `rest` over the constant selects `bs`
of the keys. The static `match` takes the arm `_` when no key matches, thus when no select is 1.
The claim about `lower` holds for at most 60 selects, as for the rows by leaf. Then the `or`
chain stays below the height 64, so `lowerMatch` binds no temporary.
-/
def RestAgrees : Prop :=
  ∀ (bs : List Bool), bs ≠ [] → ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    (∀ q, ev vals mems (restRow q bs) = BitVec.ofBool !(bs.any id)) ∧
      (bs.length ≤ 60 →
        ∀ p, Lowers (restHw p bs) (2 * bs.length + 1) (restRow (ctx := ctx) (cpos p) bs).erase)

/-! The type of a constant leaf of a hardware `match`: `Bool`, or a finite type. -/
inductive Leaf where
  | bool
  | fin (s : Bool) (w : Nat)

namespace Leaf

def ty : Leaf → Ty
  | .bool => .bool
  | .fin s w => finiteTy s w

def width : Leaf → Nat
  | .bool => 1
  | .fin _ w => w

/-! The static value of the bits `x`, as for `Pair.value`. -/
def value : (k : Leaf) → BitVec k.width → Value
  | .bool, x => .bool (x == 1)
  | .fin s w, x => finite s w x

end Leaf

/-! The node `onehot` of `Eval.onehotLeaf` over the arms `as`: each with its select and value. -/
def onehotHw (p : Pos) (k : Leaf) (as : List (Bool × BitVec k.width)) : Hw :=
  Hw.mk p k.ty .onehot (as.map (fun a => litHw p .bool (.bool a.1)) ++
    as.map fun a => litHw p k.ty (k.value a.2))

/-! The row `and (replicate s w) v` of an arm with the select `s` and the value `v`. -/
def armRow (q : Core.Pos) (w : Nat) (hb : w ≤ 65536) (a : Bool × BitVec w) : Ex ctx w :=
  .bin q .and (by decide)
    (Nat.one_mul w ▸ .replicate q (.const q 1 (bit a.1)) w (by omega)) (.const q w a.2.toNat)

/-! The row of `onehot`: `or (... (or a_0 a_1) ...) a_(m-1)`, with `a_j` the row of arm `j`. -/
def onehotRow (q : Core.Pos) (w : Nat) (hb : w ≤ 65536) : List (Bool × BitVec w) → Ex ctx w
  | [] => .const q w 0
  | a :: as =>
    as.foldl (fun e a => .bin q .or (by decide) e (armRow q w hb a)) (armRow q w hb a)

/--
A result leaf of a hardware `match`: the row of `onehot` over the arms `as`, each with a constant
select and a constant value. At most one select is 1, as the keys of the arms differ. The row
gives the value of the arm whose select is 1, and 0 when no select is 1. The static `match`
gives the value of that arm. The claim about `lower` holds for at most 30 arms. Then the node
has at most 60 operands, as the rows by leaf have at most 60 pairs. The heights alone allow 61
arms: the chain of `m` arms has the height `m + 2`, below 64, so `lowerMatch` binds no temporary.
-/
def OnehotAgrees : Prop :=
  ∀ (k : Leaf) (hb : k.width ≤ 65536) (as : List (Bool × BitVec k.width)), as ≠ [] →
    (as.filter (·.1)).length ≤ 1 → ∀ {ctx} (vals : Valuation ctx) (mems : Memories ctx),
    (∀ q, ev vals mems (onehotRow q k.width hb as) = ((as.find? (·.1)).map (·.2)).getD 0) ∧
      (as.length ≤ 30 → ∀ p, Lowers (onehotHw p k as) (5 * as.length)
        (onehotRow (ctx := ctx) (cpos p) k.width hb as).erase)

/-! Facts about the lift and the operands. -/

private theorem finitePair_finite (s : Bool) (w : Nat) (x y : BitVec w) :
    finitePair (finite s w x) (finite s w y) = some (s, ⟨w, x, y⟩) := by
  cases s <;> simp [finite, finitePair]

private theorem natCast_lt_zero (k : Nat) : ((k : Int) < 0) = False :=
  eq_false (by omega)

private theorem ofBool_beq_one (b : Bool) : (BitVec.ofBool b == 1#1) = b := by
  cases b <;> rfl

/-!
The loop over the left spine of a node stops at once when its left operand is a constant. It
thus leaves its start value.
-/
private theorem forIn_range_done (l : List Nat) (init : β)
    (f : Nat → β → FM (ForInStep β)) (h : ∀ i, f i init = pure (.done init)) :
    ForIn.forIn l init f = pure init := by
  cases l with
  | nil => rfl
  | cons x xs => rw [List.forIn_cons, h]; rfl

/--
`lower` on a small node: it splits the fuel into the charge and a rest, then computes the run.
-/
syntax "lowers" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| lowers) => `(tactic| lowers [])
  | `(tactic| lowers [$ts,*]) => `(tactic| (
    intro target root st hf
    obtain ⟨fuel, temps, count⟩ := st
    obtain ⟨rest, hrest⟩ := Nat.exists_eq_add_of_le' hf
    simp only at hrest
    subst hrest
    simp +arith +decide [lower, litHw, leaf, Hw.mk, Hw.ty, Flatten.charge, deep, binOp,
      finiteTy, signed, finite, width, constOf, twice, Core.Typed.Expr.erase, forIn_range_done,
      binExpr, $[$ts:term],*]
    all_goals exact ⟨_, ⟨_, rfl⟩, rfl⟩))

/-! The proofs, one per row family. -/

theorem static_bin_agrees : BinAgrees := by
  intro op c hk s w x y st v hc h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases op <;> simp [coreOp] at hc <;> subst hc <;>
      simp [binary, finitePair_finite, coreOp, finiteOp] at h1 <;> subst h1 <;>
      simp at h2 <;> simp [← h2, Core.Semantics.evalExpr]
  · cases op <;> simp [coreOp] at hc <;> subst hc <;> cases s <;> lowers

theorem static_cmp_agrees : CmpAgrees := by
  intro op s k w x y st v hc h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> cases op <;> simp [binOp, pred] at hc <;> subst hc <;>
      simp [binary, equal, order, finite, finitePair, bind, Except.bind] at h1 <;> subst h1 <;>
      simp at h2 <;> subst h2 <;> refine ⟨_, rfl, ?_⟩ <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalPred, pred, ofBool_beq_one, bne]
  · cases s <;> cases op <;> simp [binOp, pred] at hc <;> subst hc <;> lowers

theorem static_bool_cmp_agrees : BoolCmpAgrees := by
  intro op k a b st v hop hc h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;>
      simp [binary, equal, bind, Except.bind] at h1 <;> subst h1 <;>
      simp at h2 <;> subst h2 <;> refine ⟨_, rfl, ?_⟩ <;> cases a <;> cases b <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalPred]
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;> lowers

theorem static_logic_agrees : LogicAgrees := by
  intro op c hk a b hop hc ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;> cases a <;> cases b <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalOp]
  · rcases hop with rfl | rfl <;> simp [binOp] at hc <;> subst hc <;> lowers

theorem static_inv_agrees : InvAgrees := by
  intro s w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [unary, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      simp [← h2, Core.Semantics.evalExpr, finite]
  · cases s <;> lowers

theorem static_neg_agrees : NegAgrees := by
  intro s w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [unary, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      simp [← h2, Core.Semantics.evalExpr, Core.Semantics.evalOp, finite]
  · cases s <;> lowers

theorem static_not_agrees : NotAgrees := by
  intro b st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [unary] at h1; subst h1; simp at h2
    refine ⟨!b, h2.symm, ?_⟩
    cases b <;> simp [Core.Semantics.evalExpr, Core.Semantics.evalOp] <;> rfl
  · lowers

theorem static_shift_agrees : ShiftAgrees := by
  intro op s c hk w x b k st v hop hc hb h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hop with rfl | rfl <;> cases s <;> subst hc <;>
      rcases hb with rfl | ⟨u, y, rfl, rfl⟩ <;>
      simp +decide [binary, shift, finite, bind, Except.bind, natCast_lt_zero] at h1 <;>
      subst h1 <;> simp at h2 <;> subst h2 <;>
      simp +decide [Core.Semantics.evalExpr, finiteOp, finite, amount]
  · rcases hop with rfl | rfl <;> cases s <;> subst hc <;> lowers

theorem static_resize_same_agrees : ResizeSameAgrees := by
  intro s w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [resize, finiteTy, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      subst h2 <;> simp [Core.Semantics.evalExpr, finite]
  · cases s <;> lowers

theorem static_resize_trunc_agrees : ResizeTruncAgrees := by
  intro s n w hn x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [resize, finiteTy, finite] at h1 <;> subst h1 <;> simp at h2 <;>
      subst h2 <;>
      simp [Core.Semantics.evalExpr, Core.Semantics.evalExtract, finite,
        BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_of_lt hn),
        BitVec.setWidth_eq_extractLsb' (Nat.le_of_lt hn)]
  · cases s <;> lowers [Nat.ne_of_lt hn, hn]

theorem static_resize_zext_agrees : ResizeZextAgrees := by
  intro n w hn hb x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [resize] at h1; subst h1; simp at h2; subst h2
    simp [Core.Semantics.evalExpr, Core.Semantics.evalConcat,
      BitVec.setWidth_eq_append (Nat.le_of_lt hn)]
  · lowers [Nat.ne_of_gt hn, Nat.not_lt_of_gt hn]

theorem static_resize_sext_agrees : ResizeSextAgrees := by
  intro n w h0 hn hb x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [resize] at h1; subst h1; simp at h2; subst h2
    simp only [Core.Semantics.evalExpr, Core.Semantics.evalConcat,
      Core.Semantics.evalReplicate, Core.Semantics.evalExtract, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    congr 1
    ext i hi
    rw [BitVec.getElem_cast, BitVec.append_eq, BitVec.getElem_append, BitVec.getElem_signExtend]
    by_cases hw : i < w
    · simp [hw]
    · simp [hw, BitVec.getElem_replicate, BitVec.msb_eq_getLsbD_last, Nat.mod_one]
  · lowers [Nat.ne_of_gt hn, Nat.not_lt_of_gt hn]

theorem static_reinterpret_agrees : ReinterpretAgrees := by
  intro s r w x st v h1 h2 ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> cases r <;> simp [reinterpret, finiteTy, finite] at h1 <;> subst h1 <;>
      simp at h2 <;> subst h2 <;> simp [Core.Semantics.evalExpr, finite]
  · cases s <;> cases r <;> lowers

/-! The proofs of the rows by leaf. -/

open Spine in
private theorem runs_litHw (p : Pos) (t : Ty) (v : Value) (c : Core.Expr)
    (hc : constOf (cpos p) v = pure c) : Runs (litHw p t v) 1 c 1 :=
  runs_lit p t _ v c fun st => by rw [hc]; rfl

/-! The row `icmp eq` of a pair, erased. -/
def Pair.eqCore (pr : Pair) (q : Core.Pos) : Core.Expr :=
  .icmp q .eq (.const q pr.width pr.lc) (.const q pr.width pr.rc)

theorem Pair.eqRow_erase (pr : Pair) (q : Core.Pos) :
    (pr.eqRow (ctx := ctx) q).erase = pr.eqCore q := rfl

private theorem Pair.const_left (pr : Pair) (p : Pos) :
    constOf (cpos p) pr.left = pure (.const (cpos p) pr.width pr.lc) := by
  cases pr with
  | bool a b => rfl
  | fin s w x y => cases s <;> rfl

private theorem Pair.const_right (pr : Pair) (p : Pos) :
    constOf (cpos p) pr.right = pure (.const (cpos p) pr.width pr.rc) := by
  cases pr with
  | bool a b => rfl
  | fin s w x y => cases s <;> rfl

/-! The link of the `icmp eq` node of a pair over its left leaf. -/
def Pair.eqLk (pr : Pair) (p : Pos) : Spine.Lk :=
  { pos := p, ty := .bool, op := .eq, core := .inr .eq, right := litHw p pr.ty pr.right,
    fuel := 1, expr := .const (cpos p) pr.width pr.rc }

/-! The link of an `and` node with the `icmp eq` node of a pair as its right operand. -/
def Pair.andLk (pr : Pair) (p : Pos) : Spine.Lk :=
  { pos := p, ty := .bool, op := .and, core := .inl .and, right := pr.eqHw p, fuel := 3,
    expr := pr.eqCore (cpos p) }

open Spine in
private theorem Pair.eqLk_good (pr : Pair) (p : Pos) : (pr.eqLk p).Good 1 :=
  ⟨fun sg => by cases sg <;> rfl, runs_litHw _ _ _ _ (pr.const_right p)⟩

open Spine in
private theorem Pair.runs_eq (pr : Pair) (p : Pos) : Runs (pr.eqHw p) 3 (pr.eqCore (cpos p)) 2 :=
  runs_chain (runs_litHw p pr.ty pr.left _ (pr.const_left p)) 1 (Nat.le_refl _) [pr.eqLk p]
    (by simp [pr.eqLk_good p]) (by simp)

open Spine in
private theorem Pair.andLk_good (pr : Pair) (p : Pos) : (pr.andLk p).Good 2 :=
  ⟨fun sg => by cases sg <;> rfl, pr.runs_eq p⟩

/-! The static `==` of a pair and its row agree, by `static_cmp_agrees`. -/
private theorem Pair.eval_eq (pr : Pair) {r : Bool}
    (h : ∃ st, binary .eq pr.left pr.right = .ok st ∧ st.run () = .ok (.bool r))
    {ctx} (vals : Valuation ctx) (mems : Memories ctx) (q : Core.Pos) :
    ev vals mems (pr.eqRow q) = BitVec.ofBool r := by
  obtain ⟨st, h1, h2⟩ := h
  cases pr with
  | bool a b =>
    obtain ⟨r', hr, he⟩ :=
      (static_bool_cmp_agrees .eq .eq a b st _ (.inl rfl) rfl h1 h2 vals mems).1 q
    cases hr
    exact he
  | fin s w x y =>
    obtain ⟨r', hr, he⟩ :=
      (static_cmp_agrees .eq s .eq w x y st _ (by cases s <;> rfl) h1 h2 vals mems).1 q
    cases hr
    exact he

private theorem eval_andChain {ctx} (vals : Valuation ctx) (mems : Memories ctx) (q : Core.Pos) :
    ∀ (ps : List Pair) (rs : List Bool) (e : Ex ctx 1) (b : Bool), PairsEqual ps rs →
      ev vals mems e = BitVec.ofBool b →
      ev vals mems ((ps.map (·.eqRow q)).foldl (fun e z => .bin q .and (by decide) e z) e) =
        BitVec.ofBool (b && rs.all id)
  | [], [], _, b, _, he => by simpa using he
  | pr :: ps, r :: rs, e, b, ⟨hr, hs⟩, he => by
    simp only [List.map_cons, List.foldl_cons, List.all_cons]
    rw [eval_andChain vals mems q ps rs _ (b && r) hs]
    · simp [Bool.and_assoc]
    · simp [Core.Semantics.evalExpr, Core.Semantics.evalOp, he, pr.eval_eq hr]
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

private theorem eval_eqRow (s : Option Bool) (ps : List Pair) (rs : List Bool) (hne : ps ≠ [])
    (hs : PairsEqual ps rs) {ctx} (vals : Valuation ctx) (mems : Memories ctx) (q : Core.Pos) :
    ev vals mems (eqRow q s ps) = BitVec.ofBool (s.getD true && rs.all id) := by
  cases s with
  | some b =>
    exact eval_andChain vals mems q ps rs _ b hs (by cases b <;> rfl)
  | none =>
    match ps, rs, hs with
    | pr :: ps, r :: rs, ⟨hr, hs⟩ =>
      simpa [eqRow] using eval_andChain vals mems q ps rs _ r hs (pr.eval_eq hr vals mems q)

private theorem erase_andFold {ctx} {α : Type} (q : Core.Pos) (h : Core.BinOp.and ≠ .concat)
    (f : α → Ex ctx 1) : ∀ (xs : List α) (e : Ex ctx 1),
      (xs.foldl (fun e x => .bin q .and h e (f x)) e).erase =
        xs.foldl (fun e x => .bin q .and e (f x).erase) e.erase
  | [], _ => rfl
  | x :: xs, e => by simp [erase_andFold q h f xs, Core.Typed.Expr.erase]

open Spine in
private theorem lowers_of_runs {h n m e H} (hr : Runs h n e H) (hnm : n ≤ m) : Lowers h m e :=
  fun target root st hf => by
    obtain ⟨lo, st', h1, h2, -⟩ := hr target root st (by omega)
    exact ⟨lo, st', h1, h2⟩

/-!
The hardware value of `==` is a spine over a constant: the literal `s`, or the left leaf of the
first pair. Each link has a right operand of a height of at most 2.
-/
open Spine in
private theorem eqHw_chain (p : Pos) (s : Option Bool) (ps : List Pair) (hne : ps ≠ []) :
    ∃ (pb : Pos) (tb : Ty) (sb : Nat) (v : Value) (eb : Core.Expr) (R : List Lk),
      Runs (Hw.node pb tb sb (.lit v) []) 1 eb 1 ∧ (∀ l ∈ R, l.Good 2) ∧
      R.length = ps.length ∧ chainFuel R ≤ 4 * ps.length + 1 ∧
      eqHw p s ps = chain (Hw.node pb tb sb (.lit v) []) R ∧
      ∀ ctx, chainExpr eb R = (eqRow (ctx := ctx) (cpos p) s ps).erase := by
  cases s with
  | some b =>
    refine ⟨p, .bool, _, .bool b, .const (cpos p) 1 (bit b), (ps.map (·.andLk p)).reverse,
      runs_litHw p .bool (.bool b) _ rfl, ?_, by simp, ?_, ?_, fun ctx => ?_⟩
    · intro l hl
      simp only [List.mem_reverse, List.mem_map] at hl
      obtain ⟨pr, -, rfl⟩ := hl
      exact pr.andLk_good p
    · simp [chainFuel_eq, List.map_reverse, Pair.andLk, Function.comp_def, List.map_const',
        List.sum_replicate_nat]
      omega
    · rw [← chain_foldl]
      simp [eqHw, List.foldl_map, andHw, Pair.andLk, litHw]
      rfl
    · rw [chainExpr_foldl]
      simp [eqRow, erase_andFold, List.foldl_map, Pair.andLk, binExpr, Pair.eqRow_erase,
        Core.Typed.Expr.erase]
  | none =>
    obtain ⟨pr, ps, rfl⟩ : ∃ pr ps', ps = pr :: ps' := by
      cases ps with
      | nil => exact absurd rfl hne
      | cons pr ps => exact ⟨pr, ps, rfl⟩
    refine ⟨p, pr.ty, _, pr.left, .const (cpos p) pr.width pr.lc,
      (pr.eqLk p :: ps.map (·.andLk p)).reverse,
      runs_litHw p pr.ty pr.left _ (pr.const_left p), ?_, by simp, ?_, ?_, fun ctx => ?_⟩
    · intro l hl
      simp only [List.mem_reverse, List.mem_cons, List.mem_map] at hl
      rcases hl with rfl | ⟨pr', -, rfl⟩
      · exact (pr.eqLk_good p).mono (by decide)
      · exact pr'.andLk_good p
    · simp [chainFuel_eq, List.map_reverse, Pair.andLk, Pair.eqLk,
        Function.comp_def, List.map_const', List.sum_replicate_nat]
      omega
    · rw [← chain_foldl]
      simp [eqHw, List.foldl_map, andHw, Pair.andLk, Pair.eqLk, Pair.eqHw, litHw]
      rfl
    · rw [chainExpr_foldl]
      simp [eqRow, erase_andFold, List.foldl_map, Pair.andLk, Pair.eqLk, binExpr,
        Pair.eqRow_erase, Pair.eqCore]

theorem static_eq_leaves_agrees : EqLeavesAgrees := by
  intro s ps rs hne hs ctx vals mems
  refine ⟨eval_eqRow s ps rs hne hs vals mems, fun hlen p => ?_⟩
  obtain ⟨pb, tb, sb, v, eb, R, hb, hR, hl, hf, he, hx⟩ := eqHw_chain p s ps hne
  rw [he, ← hx ctx]
  exact lowers_of_runs (Spine.runs_chain hb 2 (by decide) R hR (by omega)) hf

theorem static_ne_leaves_agrees : NeLeavesAgrees := by
  intro s ps rs hne hs ctx vals mems
  refine ⟨fun q => ?_, fun hlen p => ?_⟩
  · have := eval_eqRow s ps rs hne hs vals mems q
    simp only [Core.Semantics.evalExpr, Core.Semantics.evalOp, this]
    cases (s.getD true && rs.all id) <;> rfl
  · obtain ⟨pb, tb, sb, v, eb, R, hb, hR, hl, hf, he, hx⟩ := eqHw_chain p s ps hne
    let top : Spine.Lk :=
      ⟨p, .bool, .xor, .inl .xor, litHw p .bool (.bool true), 1, .const (cpos p) 1 1⟩
    have htop : top.Good 2 :=
      ⟨fun sg => by cases sg <;> rfl, (runs_litHw p .bool (.bool true) _ rfl).mono (by decide)⟩
    have hr := Spine.runs_chain hb 2 (by decide) (top :: R)
      (by simpa [htop] using hR) (by simp; omega)
    simp only [Spine.chain, Spine.chainExpr, Spine.chainFuel, ← he, hx ctx] at hr
    exact lowers_of_runs hr (by simp [top]; omega)

theorem static_if_leaf_agrees : IfLeafAgrees := by
  intro c pr ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases pr with
    | bool a b =>
      cases c <;> cases a <;> cases b <;>
        simp [Pair.left, Pair.right, Pair.value, Pair.lc, Pair.rc, Pair.width,
          Core.Semantics.evalExpr, Core.Semantics.evalMux]
    | fin s w x y =>
      cases c <;> simp [Pair.left, Pair.right, Pair.value, Pair.lc, Pair.rc, Pair.width,
        Core.Semantics.evalExpr, Core.Semantics.evalMux]
  · cases pr with
    | bool a b => lowers [Pair.ty, Pair.left, Pair.right, Pair.lc, Pair.rc, Pair.width]
    | fin s w x y => cases s <;> lowers [Pair.ty, Pair.left, Pair.right, Pair.lc, Pair.rc,
        Pair.width]

/-! The proofs of the rows of enums. -/

theorem static_binder_leaf_agrees : BinderLeafAgrees := by
  intro specs d s w pw off h y v hv ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · cases s <;> simp [Value.unpack, finiteTy] at hv <;> subst hv <;>
      simp [Core.Semantics.evalExpr, Core.Semantics.evalExtract, finite, BitVec.extractLsb']
  · cases s <;> lowers [lowerPack, Flatten.bounded]

theorem static_binder_bool_agrees : BinderBoolAgrees := by
  intro specs d pw off h y v hv ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · simp [Value.unpack] at hv; subst hv
    refine ⟨_, rfl, ?_⟩
    simp [Core.Semantics.evalExpr, Core.Semantics.evalExtract, BitVec.extractLsb']
    ext i hi
    obtain rfl : i = 0 := by omega
    simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  · lowers [lowerPack, Flatten.bounded]

theorem static_unpack_enum_agrees : UnpackEnumAgrees := by
  intro pos t w pw x c s s' v hw hr ctx vals mems
  refine ⟨fun q => ?_, fun _ p => ⟨?_, ?_⟩⟩
  · obtain ⟨i, n, m, rfl⟩ : ∃ i n m, t = .enum i n m := by
      cases t <;> simp [Specs.widths] at hw ⊢
    revert hr
    simp [recast, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, hw, pure, Except.pure, ReaderT.pure, StateT.pure, liftM, monadLift,
      MonadLift.monadLift]
    split
    · simp
    · split
      · simp
      · simp only [Except.ok.injEq, Prod.mk.injEq, Val.static.injEq]
        rintro ⟨rfl, -⟩
        simp [Core.Semantics.evalExpr, Core.Semantics.evalExtract, BitVec.extractLsb']
  · lowers [lowerPack, Flatten.bounded]
  · lowers [lowerPack, Flatten.bounded]

theorem static_select_agrees : SelectAgrees := by
  intro s w x k hk ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · generalize BitVec.ofInt w k = y at hk ⊢
    simp only [Core.Semantics.evalExpr, Core.Semantics.evalPred, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    cases s <;> simp only [finite, Value.key, Bool.false_eq_true, ite_true, ite_false,
      Option.some.injEq] at hk ⊢ <;> subst hk <;> congr 1
    · rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, Option.some.injEq]
      exact ⟨fun h => h ▸ rfl, fun h => BitVec.eq_of_toNat_eq (by exact_mod_cast h)⟩
    · rw [Bool.eq_iff_iff]; simp [BitVec.toInt_inj]
  · cases s <;> lowers [keyLit]

theorem static_select_bool_agrees : SelectBoolAgrees := by
  intro b k hk ctx vals mems
  refine ⟨fun q => ?_, fun p => ?_⟩
  · rcases hk with rfl | rfl <;> cases b <;>
      simp +decide [Core.Semantics.evalExpr, Core.Semantics.evalPred, Value.key]
  · lowers [keyLit]

/-! The proofs of the rows of a hardware `match`. -/

private theorem eval_orRow {ctx} (vals : Valuation ctx) (mems : Memories ctx) (q : Core.Pos) :
    ∀ (bs : List Bool) (e : Ex ctx 1) (b : Bool), ev vals mems e = BitVec.ofBool b →
      ev vals mems (orRow q e bs) = BitVec.ofBool (b || bs.any id)
  | [], _, b, he => by simpa [orRow] using he
  | c :: bs, e, b, he => by
    simp only [orRow, List.foldl_cons, List.any_cons]
    rw [← orRow, eval_orRow vals mems q bs _ (b || c)]
    · simp [Bool.or_assoc]
    · cases b <;> cases c <;>
        simp [Core.Semantics.evalExpr, Core.Semantics.evalOp, he] <;> rfl

private theorem erase_orRow {ctx} (q : Core.Pos) : ∀ (bs : List Bool) (e : Ex ctx 1),
    (orRow q e bs).erase =
      bs.foldl (fun e b => .bin q .or e (.const q 1 (bit b))) e.erase
  | [], _ => rfl
  | b :: bs, e => by
    simp only [orRow, List.foldl_cons]
    rw [← orRow, erase_orRow q bs]
    rfl

private theorem const_bool (q : Core.Pos) (b : Bool) :
    constOf q (.bool b) = pure (.const q 1 (bit b)) := rfl

private theorem map_bounded (xs : List Hw) (b : Nat) (h : sizeOf xs < b) :
    (Flatten.bounded xs b h).map (·.1) = xs := by
  rw [Flatten.bounded, List.map_map]
  exact List.attach_map_subtype_val xs

open Spine in
/-- The loop of `rest` over the selects after the first: one `or` node for each select. -/
private theorem ok_rest {b : Nat} (p : Pos) (target : Names.Path)
    (g : {x : Hw // sizeOf x < b} → Option Low → FM (ForInStep (Option Low)))
    (hg : ∀ x lo, g x (some lo) = (do
      let lo ← deep p target 1 false lo
      Flatten.charge p 1
      let r ← lower target false x.1
      pure (.yield (some ⟨.bin (cpos p) .or lo.expr r.expr, none, max lo.height r.height + 1⟩)))) :
    ∀ (bs : List Bool) (ys : List {x : Hw // sizeOf x < b}) (lo : Low) (h : Nat)
      (st : Flatten.St) (Q : Option Low → Flatten.St → Prop),
      ys.map (·.1) = bs.map (fun c => litHw p .bool (.bool c)) → lo.height ≤ h → 1 ≤ h →
      h + bs.length < 64 → 2 * bs.length ≤ st.fuel →
      (∀ lo', lo'.expr = bs.foldl (fun e c => .bin (cpos p) .or e (.const (cpos p) 1 (bit c)))
          lo.expr → lo'.height ≤ h + bs.length →
        Q (some lo') { st with fuel := st.fuel - 2 * bs.length }) →
      Ok (forIn ys (some lo) g) st Q
  | [], [], lo, h, st, Q, _, hl, _, _, _, hq => by
    have hst : st = { st with fuel := st.fuel - 2 * 0 } := by simp
    exact ok_pure (hst ▸ hq lo rfl (by simpa using hl))
  | [], _ :: _, _, _, _, _, hv, _, _, _, _, _ => by simp at hv
  | _ :: _, [], _, _, _, _, hv, _, _, _, _, _ => by simp at hv
  | c :: bs, y :: ys, lo, h, st, Q, hv, hl, h1, hh, hf, hq => by
    simp only [List.map_cons, List.cons.injEq] at hv
    obtain ⟨hy, hv⟩ := hv
    simp only [List.length_cons] at hh hf
    rw [List.forIn_cons, hg, hy]
    refine ok_bind (ok_bind (ok_deep (by omega) (ok_bind (ok_charge (by omega) ?_))))
    refine ok_bind ((runs_litHw p .bool (.bool c) _ (const_bool _ c)).ok (by simp; omega)
      fun r he hrh => ok_pure ?_)
    refine ok_rest p target g hg bs ys _ (h + 1) _ Q hv (by simp; omega) (by omega) (by omega)
      (by simp; omega) fun lo' he' hh' => ?_
    rw [fuel_sub, fuel_sub]
    have hx := hq lo' (by simpa [he] using he') (by simp; omega)
    simp only [List.length_cons] at hx
    rwa [show 2 * (bs.length + 1) = 1 + (1 + 2 * bs.length) by omega] at hx

theorem static_rest_agrees : RestAgrees := by
  intro bs hne ctx vals mems
  obtain ⟨c, bs, rfl⟩ : ∃ c bs', bs = c :: bs' := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons c bs => exact ⟨c, bs, rfl⟩
  refine ⟨fun q => ?_, fun hlen p => ?_⟩
  · have := eval_orRow vals mems q bs (.const q 1 (bit c)) c (by cases c <;> rfl)
    simp only [restRow, Core.Semantics.evalExpr, Core.Semantics.evalOp, this, List.any_cons,
      id_eq]
    cases (c || bs.any id) <;> rfl
  · intro target root st hf
    simp only [List.length_cons] at hlen hf
    simp only [restHw, Hw.mk]
    rw [lower.eq_def]
    simp only [lowerMatch]
    change Spine.Ok _ st fun (lo : Low) _ => lo.expr = _
    generalize hL : Flatten.bounded _ _ _ = L
    have hm : L.map (·.1) = _ := hL ▸ map_bounded _ _ _
    obtain ⟨y, ys, rfl, hy, hv⟩ : ∃ y ys, L = y :: ys ∧ y.1 = litHw p .bool (.bool c) ∧
        ys.map (·.1) = bs.map fun b => litHw p .bool (.bool b) := by
      cases L with
      | nil => simp at hm
      | cons y ys => simp only [List.map_cons, List.cons.injEq] at hm; exact ⟨y, ys, rfl, hm⟩
    refine Spine.ok_bind (Spine.ok_bind (Spine.ok_charge (by omega) (Spine.ok_bind ?_)))
    rw [List.forIn_cons]
    refine Spine.ok_bind (Spine.ok_bind ?_)
    rw [hy]
    refine (runs_litHw p .bool (.bool c) _ (const_bool _ c)).ok (by simp; omega)
      fun r he hrh => Spine.ok_pure ?_
    refine ok_rest p target _ (fun _ _ => rfl) bs ys r 1 _ _ hv hrh (Nat.le_refl _)
      (by omega) (by simp; omega) fun lo' he' hh' => ?_
    refine Spine.ok_bind (Spine.ok_deep (by omega) (Spine.ok_pure
      (Spine.ok_deep (by simp; omega) ?_)))
    simp [restRow, erase_orRow, he', he, Core.Typed.Expr.erase]

/-! The bits of an arm: its value when its select is 1, else 0. -/
def armBits {w : Nat} (a : Bool × BitVec w) : BitVec w := if a.1 then a.2 else 0

private theorem eval_cast {ctx} (vals : Valuation ctx) (mems : Memories ctx) :
    ∀ {a b : Nat} (h : a = b) (e : Ex ctx a),
      ev vals mems (h ▸ e : Ex ctx b) = (ev vals mems e).cast h
  | _, _, rfl, _ => rfl

private theorem erase_cast {ctx} : ∀ {a b : Nat} (h : a = b) (e : Ex ctx a),
    (h ▸ e : Ex ctx b).erase = e.erase
  | _, _, rfl, _ => rfl

private theorem eval_armRow {ctx} (vals : Valuation ctx) (mems : Memories ctx) (q : Core.Pos)
    (w : Nat) (hb : w ≤ 65536) (a : Bool × BitVec w) :
    ev vals mems (armRow q w hb a) = armBits a := by
  obtain ⟨c, x⟩ := a
  simp only [armRow, Core.Semantics.evalExpr, Core.Semantics.evalOp, eval_cast,
    Core.Semantics.evalReplicate, armBits]
  cases c <;> ext i hi <;> simp [BitVec.getElem_replicate, Nat.mod_one]

private theorem eval_orArms {ctx} (vals : Valuation ctx) (mems : Memories ctx) (q : Core.Pos)
    (w : Nat) (hb : w ≤ 65536) : ∀ (as : List (Bool × BitVec w)) (e : Ex ctx w),
      ev vals mems (as.foldl (fun e a => .bin q .or (by decide) e (armRow q w hb a)) e) =
        ev vals mems e ||| as.foldr (fun a r => armBits a ||| r) 0
  | [], e => by simp
  | a :: as, e => by
    simp only [List.foldl_cons, List.foldr_cons]
    rw [eval_orArms vals mems q w hb as]
    simp [Core.Semantics.evalExpr, Core.Semantics.evalOp, eval_armRow, BitVec.or_assoc]

private theorem orArms_none {w : Nat} : ∀ (as : List (Bool × BitVec w)),
    (as.filter (·.1)).length = 0 → as.foldr (fun a r => armBits a ||| r) 0 = 0
  | [], _ => rfl
  | ⟨c, x⟩ :: as, h => by
    cases c
    · simp only [List.filter_cons, Bool.false_eq_true, ite_false] at h
      rw [List.foldr_cons, orArms_none as h]
      simp [armBits]
    · simp at h

private theorem orArms_find {w : Nat} : ∀ (as : List (Bool × BitVec w)),
    (as.filter (·.1)).length ≤ 1 →
      as.foldr (fun a r => armBits a ||| r) 0 = ((as.find? (·.1)).map (·.2)).getD 0
  | [], _ => rfl
  | ⟨c, x⟩ :: as, h => by
    cases c
    · simp only [List.filter_cons, Bool.false_eq_true, ite_false] at h
      rw [List.foldr_cons, orArms_find as h]
      simp [armBits]
    · simp only [List.filter_cons, ite_true, List.length_cons] at h
      rw [List.foldr_cons, orArms_none as (by omega)]
      simp [armBits]

private theorem Leaf.const_value (k : Leaf) (q : Core.Pos) (x : BitVec k.width) :
    constOf q (k.value x) = pure (.const q k.width x.toNat) := by
  cases k with
  | bool => rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;> rfl
  | fin s w => cases s <;> rfl

private theorem Leaf.width_ty (k : Leaf) : Flatten.width k.ty = k.width := by
  cases k with
  | bool => rfl
  | fin s w => cases s <;> rfl

private theorem q_fuel {Q : Flatten.St → Prop} {st : Flatten.St} {a b : Nat} (h : a = b)
    (hq : Q { st with fuel := st.fuel - a }) : Q { st with fuel := st.fuel - b } := h ▸ hq

open Spine in
/-- The first loop of `onehot`: it lowers each operand, in order, into an array. -/
private theorem ok_push {b : Nat} (target : Names.Path)
    (g : {x : Hw // sizeOf x < b} → Array Low → FM (ForInStep (Array Low)))
    (hg : ∀ x arr, g x arr = (do
      let d ← lower target false x.1
      pure (.yield (arr.push d)))) :
    ∀ (ys : List {x : Hw // sizeOf x < b}) (xs : List (Hw × Core.Expr)) (arr : Array Low)
      (st : Flatten.St) (Q : Array Low → Flatten.St → Prop),
      ys.map (·.1) = xs.map (·.1) → (∀ x ∈ xs, Runs x.1 1 x.2 1) → xs.length ≤ st.fuel →
      (∀ arr' (ls : List Low), arr'.toList = arr.toList ++ ls → ls.map (·.expr) = xs.map (·.2) →
        (∀ l ∈ ls, l.height ≤ 1) → Q arr' { st with fuel := st.fuel - xs.length }) →
      Ok (forIn ys arr g) st Q
  | [], [], arr, st, Q, _, _, _, hq => by
    have hst : st = { st with fuel := st.fuel - 0 } := by simp
    exact ok_pure (hst ▸ hq arr [] (by simp) rfl (by simp))
  | [], _ :: _, _, _, _, hv, _, _, _ => by simp at hv
  | _ :: _, [], _, _, _, hv, _, _, _ => by simp at hv
  | y :: ys, x :: xs, arr, st, Q, hv, hr, hf, hq => by
    simp only [List.map_cons, List.cons.injEq] at hv
    obtain ⟨hy, hv⟩ := hv
    simp only [List.length_cons] at hf
    rw [List.forIn_cons, hg, hy]
    refine ok_bind (ok_bind ((hr x (by simp)).ok (by omega) fun d he hh => ok_pure ?_))
    refine ok_push target g hg ys xs _ _ Q hv (fun z hz => hr z (by simp [hz])) (by simp; omega)
      fun arr' ls harr hls hlh => ?_
    rw [fuel_sub]
    refine q_fuel (Q := Q arr') (by simp; omega) (hq arr' (d :: ls) (by simp [harr]) ?_ ?_)
    · simp [he, hls]
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hh, hlh⟩

/-! The row `and (replicate s w) v` of an arm with the rows `s` and `v`. -/
def armCore (q : Core.Pos) (w : Nat) (e : Core.Expr × Core.Expr) : Core.Expr :=
  .bin q .and (.replicate q e.1 w) e.2

open Spine in
/-- The second loop of `onehot`, after the first arm: one `or` node for each arm. -/
private theorem ok_onehot (p : Pos) (target : Names.Path) (w : Nat)
    (g : Low × Low → Option Low → FM (ForInStep (Option Low)))
    (hg : ∀ x lo, g x (some lo) = (do
      Flatten.charge p 1
      let r ← deep p target w false ⟨.replicate (cpos p) x.1.expr w, none, x.1.height + 1⟩
      Flatten.charge p 1
      let a ← deep p target w false
        ⟨.bin (cpos p) .and r.expr x.2.expr, none, max r.height x.2.height + 1⟩
      let lo ← deep p target w false lo
      Flatten.charge p 1
      pure (.yield (some ⟨.bin (cpos p) .or lo.expr a.expr, none, max lo.height a.height + 1⟩)))) :
    ∀ (prs : List (Low × Low)) (lo : Low) (h : Nat) (st : Flatten.St)
      (Q : Option Low → Flatten.St → Prop),
      (∀ x ∈ prs, x.1.height ≤ 1 ∧ x.2.height ≤ 1) → lo.height ≤ h → 3 ≤ h →
      h + prs.length < 64 → 3 * prs.length ≤ st.fuel →
      (∀ lo', lo'.expr = prs.foldl
          (fun e x => .bin (cpos p) .or e (armCore (cpos p) w (x.1.expr, x.2.expr))) lo.expr →
        lo'.height ≤ h + prs.length →
        Q (some lo') { st with fuel := st.fuel - 3 * prs.length }) →
      Ok (forIn prs (some lo) g) st Q
  | [], lo, h, st, Q, _, hl, _, _, _, hq => by
    have hst : st = { st with fuel := st.fuel - 3 * 0 } := by simp
    exact ok_pure (hst ▸ hq lo rfl (by simpa using hl))
  | x :: prs, lo, h, st, Q, hx, hl, h3, hh, hf, hq => by
    obtain ⟨hx1, hx2⟩ := hx x (by simp)
    simp only [List.length_cons] at hh hf
    rw [List.forIn_cons, hg]
    refine ok_bind (ok_bind (ok_charge (by omega) (ok_bind (ok_deep (by simp; omega)
      (ok_bind (ok_charge (by simp; omega) (ok_bind (ok_deep (by simp; omega)
      (ok_bind (ok_deep (by omega) (ok_bind (ok_charge (by simp; omega) (ok_pure ?_)))))))))))))
    refine ok_onehot p target w g hg prs _ (h + 1) _ Q (fun y hy => hx y (by simp [hy]))
      (by simp; omega) (by omega) (by omega) (by simp; omega) fun lo' he' hh' => ?_
    dsimp only
    simp only [Nat.sub_sub]
    refine q_fuel (Q := Q (some lo')) (by simp; omega) (hq lo' ?_ (by simp; omega))
    simpa [armCore] using he'

private theorem armRow_erase {ctx} (q : Core.Pos) (w : Nat) (hb : w ≤ 65536)
    (a : Bool × BitVec w) :
    (armRow (ctx := ctx) q w hb a).erase =
      armCore q w (.const q 1 (bit a.1), .const q w a.2.toNat) := by
  simp [armRow, Core.Typed.Expr.erase, erase_cast, armCore]

private theorem erase_orArms {ctx} (q : Core.Pos) (w : Nat) (hb : w ≤ 65536) :
    ∀ (as : List (Bool × BitVec w)) (e : Ex ctx w),
      (as.foldl (fun e a => .bin q .or (by decide) e (armRow q w hb a)) e).erase =
        as.foldl (fun e a => .bin q .or e (armRow (ctx := ctx) q w hb a).erase) e.erase
  | [], _ => rfl
  | a :: as, e => by simp [erase_orArms q w hb as, Core.Typed.Expr.erase]

theorem static_onehot_agrees : OnehotAgrees := by
  intro k hb as hne hone ctx vals mems
  obtain ⟨a, as, rfl⟩ : ∃ a as', as = a :: as' := by
    cases as with
    | nil => exact absurd rfl hne
    | cons a as => exact ⟨a, as, rfl⟩
  refine ⟨fun q => ?_, fun hlen p => ?_⟩
  · rw [onehotRow, eval_orArms, eval_armRow, ← orArms_find _ hone]
    simp
  · intro target root st hf
    simp only [List.length_cons] at hlen hf
    simp only [onehotHw, Hw.mk]
    rw [lower.eq_def]
    simp only [lowerMatch]
    change Spine.Ok _ st fun (lo : Low) _ => lo.expr = _
    generalize hL : Flatten.bounded _ _ _ = L
    have hm : L.map (·.1) = _ := hL ▸ map_bounded _ _ _
    have hLl : L.length = 2 * (as.length + 1) := by
      have := congrArg List.length hm
      simp at this
      omega
    rw [hLl]
    simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), bne_self_eq_false,
      Bool.false_eq_true, ite_false, Leaf.width_ty]
    let selE (a : Bool × BitVec k.width) : Core.Expr := .const (cpos p) 1 (bit a.1)
    let valE (a : Bool × BitVec k.width) : Core.Expr := .const (cpos p) k.width a.2.toNat
    obtain ⟨xs, hx⟩ : ∃ xs : List (Hw × Core.Expr), xs =
        (a :: as).map (fun a => (litHw p .bool (.bool a.1), selE a)) ++
          (a :: as).map (fun a => (litHw p k.ty (k.value a.2), valE a)) := ⟨_, rfl⟩
    have hxl : xs.length = 2 * (as.length + 1) := by simp [hx]; omega
    have hxs : L.map (·.1) = xs.map (·.1) := by rw [hm, hx]; simp [Function.comp_def]
    have hruns : ∀ x ∈ xs, Spine.Runs x.1 1 x.2 1 := by
      intro x hm'
      simp only [hx, List.mem_append, List.mem_map] at hm'
      rcases hm' with ⟨b, -, rfl⟩ | ⟨b, -, rfl⟩
      · exact runs_litHw _ _ _ _ (const_bool _ _)
      · exact runs_litHw _ _ _ _ (Leaf.const_value _ _ _)
    refine Spine.ok_bind (Spine.ok_bind (ok_push target _ (fun _ _ => rfl) L xs #[] st _ hxs hruns
      (by omega) fun arr ls harr hls hlh => Spine.ok_bind ?_))
    rw [show arr.toList = ls by simpa using harr]
    have hls' : ls.map (·.expr) = (a :: as).map selE ++ (a :: as).map valE := by
      rw [hls, hx]; simp [Function.comp_def]
    have hll : ls.length = 2 * (as.length + 1) := by
      have := congrArg List.length hls'
      simp at this
      omega
    have h1 : (ls.take (as.length + 1)).map (·.expr) = (a :: as).map selE := by
      rw [List.map_take, hls', List.take_left' (by simp)]
    have h2 : (ls.drop (as.length + 1)).map (·.expr) = (a :: as).map valE := by
      rw [List.map_drop, hls', List.drop_left' (by simp)]
    generalize hP : (ls.take (as.length + 1)).zip (ls.drop (as.length + 1)) = prs
    have F1 : prs.map (fun x => (x.1.expr, x.2.expr)) =
        (a :: as).map fun a => (selE a, valE a) := by
      rw [← hP, show ((a :: as).map fun a => (selE a, valE a)) =
        ((a :: as).map selE).zip ((a :: as).map valE) from List.zip_map'.symm, ← h1, ← h2,
        List.zip_map]
      rfl
    have F2 : ∀ x ∈ prs, x.1.height ≤ 1 ∧ x.2.height ≤ 1 := by
      intro x hxm
      rw [← hP] at hxm
      obtain ⟨m1, m2⟩ := List.of_mem_zip hxm
      exact ⟨hlh _ (List.mem_of_mem_take m1), hlh _ (List.mem_of_mem_drop m2)⟩
    obtain ⟨x0, prs, rfl⟩ : ∃ x0 prs', prs = x0 :: prs' := by
      cases prs with
      | nil => simp at F1
      | cons x0 prs' => exact ⟨_, _, rfl⟩
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at F1
    obtain ⟨⟨hs0, hv0⟩, F1⟩ := F1
    have hpl : prs.length = as.length := by
      have := congrArg List.length F1
      simpa using this
    obtain ⟨hx1, hx2⟩ := F2 x0 (by simp)
    rw [List.forIn_cons]
    refine Spine.ok_bind (Spine.ok_bind (Spine.ok_charge (by simp; omega)
      (Spine.ok_bind (Spine.ok_deep (by simp; omega) (Spine.ok_bind (Spine.ok_charge
      (by simp; omega) (Spine.ok_bind (Spine.ok_deep (by simp; omega) (Spine.ok_pure ?_)))))))))
    refine ok_onehot p target k.width _ (fun _ _ => rfl) prs _ 3 _ _
      (fun y hy => F2 y (by simp [hy])) (by simp; omega) (Nat.le_refl _) (by omega)
      (by simp; omega) fun lo' he' hh' => ?_
    refine Spine.ok_pure (Spine.ok_deep (by omega) ?_)
    rw [he', onehotRow, erase_orArms]
    simp only [armRow_erase]
    rw [← List.foldl_map (f := fun x : Low × Low => (x.1.expr, x.2.expr))
      (g := fun e y => Core.Expr.bin (cpos p) .or e (armCore (cpos p) k.width y)), F1,
      List.foldl_map]
    simp only [hs0, hv0, selE, valE]
    rfl

/-! Each finite static operation agrees with its core row, and `lower` emits that row. -/
theorem static_op_agrees :
    BinAgrees ∧ CmpAgrees ∧ BoolCmpAgrees ∧ LogicAgrees ∧ InvAgrees ∧ NegAgrees ∧
      NotAgrees ∧ ShiftAgrees ∧ ResizeSameAgrees ∧ ResizeTruncAgrees ∧ ResizeZextAgrees ∧
      ResizeSextAgrees ∧ ReinterpretAgrees ∧ EqLeavesAgrees ∧ NeLeavesAgrees ∧ IfLeafAgrees ∧
      UnpackEnumAgrees ∧ BinderLeafAgrees ∧ BinderBoolAgrees ∧ SelectAgrees ∧ SelectBoolAgrees ∧
      RestAgrees ∧ OnehotAgrees :=
  ⟨static_bin_agrees, static_cmp_agrees, static_bool_cmp_agrees, static_logic_agrees,
    static_inv_agrees, static_neg_agrees, static_not_agrees, static_shift_agrees,
    static_resize_same_agrees, static_resize_trunc_agrees, static_resize_zext_agrees,
    static_resize_sext_agrees, static_reinterpret_agrees, static_eq_leaves_agrees,
    static_ne_leaves_agrees, static_if_leaf_agrees, static_unpack_enum_agrees,
    static_binder_leaf_agrees, static_binder_bool_agrees, static_select_agrees,
    static_select_bool_agrees, static_rest_agrees, static_onehot_agrees⟩

end Silicon.Source.StaticOps
