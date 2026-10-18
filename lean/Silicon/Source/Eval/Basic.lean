-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Resolve
import Silicon.Source.Names
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
The values, the state, and the scalar operations of the evaluator. `Source.Eval.Container` adds
the static containers, and `Source.Eval` the evaluator with the cost model of its module doc.
-/
namespace Silicon.Source.Eval

open Resolve Names

/-! Position order: the lower line, then the lower column. -/
def Pos.compare (a b : Pos) : Ordering :=
  (Ord.compare a.line b.line).then (Ord.compare a.col b.col)

/-! The budgets of section 5.4 with their normative defaults. -/
structure Budget where
  fuel : Nat := 100000000
  depth : Nat := 1000
  deriving Repr, Inhabited

/-! The state of a constant in the table of constants. -/
inductive Entry where
  | notStarted
  | inProgress
  | done (value : Value)
  deriving Repr, Inhabited

/-!
A struct specialization in the table of specializations (section 5.6): the struct item, its
static arguments after their typed use, and its state. A done entry holds its struct type and the
name and the type of each field. A specialization that is not started has no entry.
-/
inductive SpecState where
  | inProgress
  | done (ty : Ty) (fields : Array (String × Ty))

structure Spec where
  item : Nat
  args : List Value
  state : SpecState

/-!
An enum in the table of enums (section 5.6), by its item. A done entry holds its enum type, its
tag width `W`, and its payload width `P`. It also holds the tag value and the payload types of
each variant, in declaration order. Its tag map gives the variant of each tag value. An enum that
is not started has no entry.
-/
inductive EnumState where
  | inProgress
  | done (ty : Ty) (w p : Nat) (variants : Array (Nat × Array Ty))
      (tags : Std.TreeMap Nat Nat compare)

/-! The order of the keys of specializations: the struct item, then the static arguments. -/
def Spec.cmp (a b : Nat × List Value) : Ordering := (compare a.1 b.1).then (Value.cmps a.2 b.2)

/-!
The table of specializations. A struct type holds the number of its entry. `index` finds the
number of an entry by its key in logarithmic time (section 5.6). A comparison of two keys walks
at most the smaller arguments, so the lookup stays in the charge of the arguments. `enums` is
the table of enums by their item, also in logarithmic time.
-/
structure Specs where
  entries : Array Spec := #[]
  index : Std.TreeMap (Nat × List Value) Nat Spec.cmp := {}
  enums : Std.TreeMap Nat EnumState compare := {}

/-! The number and the entry of the struct item `i` with the static arguments `args`. -/
def Specs.find? (s : Specs) (i : Nat) (args : List Value) : Option (Nat × Spec) := do
  let k ← s.index[(i, args)]?
  return (k, ← s.entries[k]?)

/-! The struct item of the struct type `t`, from its entry. -/
def Specs.item (s : Specs) : Ty → Option Nat
  | .struct k .. => (s.entries[k]?).map (·.item)
  | _ => none

/-! The tag width and the payload width of the enum type `t`, from its done entry. -/
def Specs.widths (s : Specs) : Ty → Option (Nat × Nat)
  | .enum i .. =>
    match s.enums[i]? with
    | some (.done _ w p ..) => some (w, p)
    | _ => none
  | _ => none

/-!
The named parts of the type `t`, in packing order: the name and the type of each field of a
struct type, from its done entry. An enum type has the parts `tag` of type `UInt[W]` and
`payload` of type `UInt[P]`, without `payload` when `P` is 0 (section 5.1). Each walk over the
parts of a type with named parts reads them here and nowhere else. A type without named parts
and an entry that is not done give `none`. A record or an enum value exists only after its entry
is done, so each such type has its parts.
-/
def Specs.parts (s : Specs) : Ty → Option (Array (String × Ty))
  | .struct k .. => do
    match (← s.entries[k]?).state with
    | .done _ fs => some fs
    | .inProgress => none
  | t@(.enum ..) => do
    let (w, p) ← s.widths t
    return #[("tag", .uint w)] ++ if p = 0 then #[] else #[("payload", .uint p)]
  | _ => none

/-!
A node of a hardware value. Section 7.4 lowers each node to core operations. `share k` marks its
one operand, the condition of an aggregate `if`, as shared by several leaf statements. The
lowering binds it to one temporary at its first use (section 7.4). `k` numbers the marks of one
instantiation. `word m off` is a leaf of the word of the memory `m` at the bit offset `off`. It
holds the path of the memory once and lowers to `(extract m$0rdata off w)` (section 7.6).
`pack w` packs its operands, the leaves in packing order, into `UInt[w]`: the first leaf in the
low bits, and zero high bits (ADR 0025). `extract off w` gives the `w` bits of its one operand
from the bit `off`. They are the hardware pack and unpack of an enum (section 7.4). `onehot` of a
hardware `match` takes the `m` selects of its arms, then the `m` values of one leaf. It gives
the value of the arm whose select is true (section 5.4). `rest` is the select of the arm `_`: it
is true when none of its operands, the other selects, is true.
-/
inductive Op where
  | ref (name : Path)
  | out (inst : Path) (port : Name)
  | word (mem : Path) (off : Nat)
  | lit (value : Value)
  | un (op : UnOp)
  | bin (op : BinOp)
  | mux
  | resize
  | reinterpret
  | share (k : Nat)
  | pack (w : Nat)
  | extract (off w : Nat)
  | onehot
  | rest
  deriving Repr, Inhabited

/-!
A hardware value: a typed tree of operations over core names. Each node keeps the position of
the source node that made it, and its recursive size, so a charge reads the size in one step.
-/
inductive Hw where
  | node (pos : Pos) (ty : Ty) (size : Nat) (op : Op) (args : List Hw)
  deriving Repr, Inhabited

def Hw.pos : Hw → Pos | .node p .. => p
def Hw.ty : Hw → Ty | .node _ t .. => t
def Hw.size : Hw → Nat | .node _ _ s .. => s

/-!
The size of a node of the type `ty` without its operands. A name, a child output, and a leaf of a
memory word refer to a core name. Each has the size of a finite value of its type (section 5.4).
A constant has the size of its value. A mark of a shared operand paid for its operand once, when
it was made (section 5.4). It lowers to a temporary, so it has the size of a core name, and its
operand does not count again. Each other node has the size 1 plus the sizes of its operands.
-/
def Op.size (ty : Ty) : Op → Nat
  | .lit v => v.size
  | .ref _ | .out .. | .word .. | .share _ => ty.info.zeroSize
  | _ => 1

def Hw.mk (pos : Pos) (ty : Ty) (op : Op) (args : List Hw) : Hw :=
  let reads := if op matches .share _ then 0 else (args.map Hw.size).sum
  .node pos ty (op.size ty + reads) op args

/-! The core name of the port with the source name `x`. A port keeps its source name. -/
def portName (x : String) : Name := ⟨x, []⟩

/-!
The base of a reference aggregate: a core name, an output of a child instance, or the word of a
memory. A child output holds the name of its port and the fields of its part in reverse order.
Thus a step adds a field at the front. A word holds the path of its memory and the bit offset of
its part (section 7.6).
-/
inductive Base where
  | name (path : Path)
  | out (inst : Path) (port : String) (rev : List Field)
  | word (mem : Path) (off : Nat)
  deriving Repr, Inhabited

/-! The operation of a leaf of the base `b`. A child output puts its fields in order once. -/
def Base.op : Base → Op
  | .name p => .ref p
  | .out i q r => .out i { portName q with rest := r.reverse }
  | .word m o => .word m o

/-!
The fields of a struct type for the offset of a word part: the number and the type of each field
in declaration order. A table can leave out a field without a leaf, because its width is 0.
-/
abbrev Parts := Ty → Option (Array (Nat × Ty))

/-! The numbered part types of the named parts `fs` (`Specs.parts`), for a word part. -/
def typesOf (fs : Ty → Option (Array (String × Ty))) : Parts := fun t =>
  (fs t).map fun xs => xs.zipIdx.map fun ((_, u), k) => (k, u)

/-!
The bit offset of the part `k` in a word of the type `t` (section 7.6). The first leaf is in the
least significant bits. For an array, the offset is `k` times the width of the element. For a
tuple or a record, it is the sum of the widths of the earlier parts. `ps` gives the fields of a
struct type. The metadata gives each width, so the work is at most the parts of `t`.
-/
def Ty.offset (ps : Parts) (t : Ty) (k : Nat) : Nat :=
  match t with
  | .array e _ => k * e.info.width
  | .tuple ts => ((ts.extract 0 k).map (·.info.width)).sum
  | t => ((((ps t).getD #[]).filter (·.1 < k)).map (·.2.info.width)).sum

/-!
The part `k` of the type `t` of the base `b`, with the leaf field `f` (section 7.3). The field is
a field `.f` of a record, or the element `<k>e` of an array or a tuple. A name and a child output
add the field in one step. A word adds the offset of the part (`Ty.offset`), and only a word
reads `ps`.
-/
def Base.sub (ps : Parts) (t : Ty) (k : Nat) (f : Field) : Base → Base
  | .name p => .name (p.push f)
  | .out i q r => .out i q (f :: r)
  | .word m o => .word m (o + Ty.offset ps t k)

/-! A port of an instantiation, as its parent sees it. `sym` is the symbol of its name. -/
structure Port where
  name : String
  sym : Nat
  input : Bool
  ty : Ty
  pos : Pos
  deriving Repr, Inhabited

/-!
The interface of a done instantiation: its emitted name, its ports by the symbol of their
name, its number of inputs, and its domain. A combinational module has no domain.
-/
structure Iface where
  name : Names.Name
  ports : Std.HashMap Nat Port
  inputs : Nat
  domain : Option String

/-! The resources that need one binding with `:=`. -/
inductive Kind where
  | reg | wire | output
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
A handle. Its number indexes the resources, the memories, or the instances of its
instantiation. A child input holds the number of its instance. A memory holds its word type and
its depth, and an instance its type `Instance[M, args]` (section 5.1).
-/
inductive Handle where
  | res (kind : Kind) (id : Nat) (ty : Ty) (path : Path)
  | mem (id : Nat) (path : Path) (word : Ty) (depth : Nat)
  | inst (id : Nat) (path : Path) (iface : Iface) (ty : Ty)
  | input (inst : Nat) (path : Path) (port : Port)
  | domain (name : String)

/-! A handle shows its kind and its path. An interface has no `Repr`, so the derive cannot. -/
instance : Repr Handle where
  reprPrec
    | .res _ _ _ p, _ | .mem _ p .., _ | .inst _ p .., _ | .input _ p _, _ => s!"handle {repr p}"
    | .domain x, _ => s!"domain {x}"

/-!
The handle type of `h` (section 5.1). It comes from the stored types and the depth, with no
charge. An own output and a domain have none.
-/
def Handle.ty? : Handle → Option Ty
  | .res .reg _ t _ => some (.reg t)
  | .res .wire _ t _ => some (.wire t)
  | .res .output .. | .domain _ => none
  | .mem _ _ w d => some (.mem w d)
  | .inst _ _ _ t => some t
  | .input _ _ q => some (.input q.ty)

/-! The text of the handle `h` in a message, by its kind. -/
def Handle.text : Handle → String
  | .res .reg .. => "a register"
  | .res .wire .. => "a wire"
  | .res .output .. => "an output"
  | .mem .. => "a memory"
  | .inst .. => "an instance"
  | .input .. => "an input of a child"
  | .domain _ => "a domain"

/-!
The stored numbers of a container node of an aggregate: its type, its size, its depth, and the
number of its hardware leaves.
-/
structure Node where
  ty : Ty
  size : Nat
  depth : Nat
  leaves : Nat
  deriving Repr, Inhabited

/-!
An aggregate (section 5.1): a tree with at least one hardware leaf, or a container of a type with
the handle flag. A `static` part holds no hardware leaf and no handle, and a `hw` part is a
hardware value. A `ref` refers to a part of a port, a register, a wire, or a child output. Its
type is `ty`, and it does not expand into its leaves. A `handle` is a handle leaf (slice 3b). A
`list` is a list of the element type `elem` with the handle flag. Each container node stores its
type, its recursive size, its depth, and the number of its hardware leaves. Thus no charge walks
the tree.
-/
inductive Agg where
  | static (v : Value)
  | hw (h : Hw)
  | ref (base : Base) (ty : Ty)
  | handle (h : Handle)
  | array (node : Node) (elems : Array Agg)
  | tuple (node : Node) (elems : Array Agg)
  | record (node : Node) (elems : Array Agg)
  | list (node : Node) (elem : Ty) (elems : Array Agg)
  deriving Repr, Inhabited

/-!
The recursive size (section 5.4). Each leaf of a reference has the size of a finite value of its
type. Thus a reference has the zero size of its type, and the metadata gives it in one step. A
handle has the size 1.
-/
def Agg.size : Agg → Nat
  | .static v => v.size
  | .hw h => h.size
  | .ref _ t => t.info.zeroSize
  | .handle _ => 1
  | .array n _ | .tuple n _ | .record n _ | .list n .. => n.size

/-!
The depth (section 5.5). A reference has the depth of a value of its type, and a handle the
depth 1.
-/
def Agg.depth : Agg → Nat
  | .static v => v.depth
  | .hw _ | .handle _ => 1
  | .ref _ t => t.zeroDepth
  | .array n _ | .tuple n _ | .record n _ | .list n .. => n.depth

/-!
The number of hardware leaves. Each leaf of a reference is a hardware leaf. A handle is not a
hardware leaf.
-/
def Agg.leaves : Agg → Nat
  | .static _ | .handle _ => 0
  | .hw _ => 1
  | .ref _ t => t.info.leaves
  | .array n _ | .tuple n _ | .record n _ | .list n .. => n.leaves

/-! The type of a part. A handle has its handle type (`Handle.ty?`). -/
def Agg.ty? : Agg → Option Ty
  | .static v => v.ty?
  | .hw h => some h.ty
  | .ref _ t => some t
  | .handle h => h.ty?
  | .array n _ | .tuple n _ | .record n _ | .list n .. => some n.ty

/-!
A container node with the elements `xs` and the type `t`. When `t` has no handle flag and no
element has a hardware leaf, it is a static value. A node of a type with the handle flag stays a
node, also without a hardware leaf or an element (section 5.1). The depth of the node also counts
`d`. This is the depth of the element type of an array or a list, the depth of the struct type of
a record, or 0. Each element is in its normal form (`normalize`).
-/
def Agg.container (mk : Node → Array Agg → Agg) (static : Array Value → Value) (t : Ty) (d : Nat)
    (xs : Array Agg) : Agg :=
  let vs := xs.filterMap fun | .static v => some v | _ => none
  if !t.info.handles && vs.size = xs.size then .static (static vs)
  else
    mk ⟨t, 1 + (xs.toList.map Agg.size).sum, 1 + xs.foldl (fun m x => max m x.depth) d,
      (xs.toList.map Agg.leaves).sum⟩ xs

def Agg.mkArray (e : Ty) (xs : Array Agg) : Agg :=
  Agg.container .array (.array e) (.array e xs.size) e.depth xs

def Agg.mkTuple (ts : Array Ty) (xs : Array Agg) : Agg :=
  Agg.container .tuple .tuple (.tuple ts) 0 xs

/-! A list of the element type `e`. With the handle flag, it is a list node (section 5.1). -/
def Agg.mkList (e : Ty) (xs : Array Agg) : Agg :=
  Agg.container (fun n => .list n e) (.list e) (.list e) e.depth xs

/-!
The parts of a static enum value with the tag `x` of `w` bits and the payload `y` of `p` bits:
`tag`, then `payload` when `p` is not 0 (section 5.1).
-/
def Value.enumParts (w : Nat) (x : BitVec w) (p : Nat) (y : BitVec p) : Array Value :=
  #[.uint w x] ++ if p = 0 then #[] else #[.uint p y]

/-!
The static enum value of the enum type `t` with the static parts `vs` (`Value.enumParts`). The
parts of an enum always have this form, so the last case does not occur.
-/
def Value.ofEnum (t : Ty) (vs : Array Value) : Value :=
  match vs.toList with
  | [.uint w x] => .enum t w x 0 0
  | [.uint w x, .uint p y] => .enum t w x p y
  | _ => .record t vs

/-!
A record node, or a hardware enum node when `t` is an enum type (section 5.1). An enum node with
only static parts is the one static form of its value, a static enum value.
-/
def Agg.mkRecord (t : Ty) (xs : Array Agg) : Agg :=
  Agg.container .record (if t matches .enum .. then Value.ofEnum t else .record t) t t.depth xs

/-!
The static value `v` in its normal form. A container of a type with the handle flag is a node,
also when it holds no handle (section 5.1), for example `[]` converted to `[Reg[Bool]; 0]`. The
conversion that made `v` paid for its size, so this walk has no charge.
-/
mutual
  def Agg.ofStatic : Value → Agg
    | v@(.array e ⟨xs⟩) =>
      if e.info.handles then .mkArray e (Agg.ofStaticAll xs).toArray else .static v
    | v@(.tuple ⟨xs⟩) =>
      match Value.tyAll? xs with
      | some ts =>
        if (Ty.tuple ts.toArray).info.handles then .mkTuple ts.toArray (Agg.ofStaticAll xs).toArray
        else .static v
      | none => .static v
    | v@(.record t ⟨xs⟩) =>
      if t.info.handles then .mkRecord t (Agg.ofStaticAll xs).toArray else .static v
    | v@(.list e ⟨xs⟩) =>
      if e.info.handles then .mkList e (Agg.ofStaticAll xs).toArray else .static v
    | v => .static v

  def Agg.ofStaticAll : List Value → List Agg
    | [] => []
    | x :: xs => Agg.ofStatic x :: Agg.ofStaticAll xs
end

/-!
The static value `v` after its typed use at `t`. Only a type with the handle flag can need a
node (`Agg.ofStatic`).
-/
def Agg.typed (t : Ty) (v : Value) : Agg := if t.info.handles then .ofStatic v else .static v

/-!
The text of the aggregate part `a` in a message. A node without a hardware leaf names its type
only, because it is not hardware.
-/
def Agg.text : Agg → String
  | .static v => v.text
  | .hw h => s!"hardware {h.ty.text}"
  | .handle h => h.text
  | a =>
    let t := (a.ty?.map Ty.text).getD "a tuple"
    if a.leaves = 0 then t else s!"hardware {t}"

/-! The container node `a` with the new elements `xs`, in its normal form. -/
def Agg.rebuild (a : Agg) (xs : Array Agg) : Agg :=
  match a with
  | .array { ty := .array e _, .. } _ => .mkArray e xs
  | .tuple { ty := .tuple ts, .. } _ => .mkTuple ts xs
  | .record n _ => .mkRecord n.ty xs
  | .list _ e _ => .mkList e xs
  | a => a

/-!
A part of a literal that waits for its type. It is a value with its normal form as an aggregate
part, the literal `[]` at `pos`, or an array or a tuple literal at `pos`. Such a literal has at
least one part that waits.
-/
inductive Part where
  | value (v : Agg)
  | empty (pos : Pos)
  | array (pos : Pos) (elems : List Part)
  | tuple (pos : Pos) (elems : List Part)

/-! The size of a part: 1 for `[]`, and 1 more than its elements for a literal. -/
mutual
  def Part.size : Part → Nat
    | .value v => v.size
    | .empty _ => 1
    | .array _ ps | .tuple _ ps => 1 + Part.sizeAll ps

  def Part.sizeAll : List Part → Nat
    | [] => 0
    | p :: ps => p.size + Part.sizeAll ps
end

def Part.text : Part → String
  | .value v => v.text
  | .empty _ => "`[]`"
  | .array .. => "an array literal with `[]`"
  | .tuple .. => "a tuple literal with `[]`"

/-!
A value of the evaluator: a static value, a hardware value, a hardware aggregate, or a handle
(section 5.1).
`pending` is a literal with `[]` before a typed use gives it its type. `first` is the position
of its first `[]`.
-/
inductive Val where
  | static (v : Value)
  | hw (h : Hw)
  | handle (h : Handle)
  | pending (first : Pos) (part : Part)
  | agg (a : Agg)

/-! A handle has the size 1. A literal that waits has the size of its parts. -/
def Val.size : Val → Nat
  | .static v => v.size
  | .hw h => h.size
  | .agg a => a.size
  | .handle _ => 1
  | .pending _ p => p.size

/-! The value of the aggregate part `a`. -/
def Agg.val : Agg → Val
  | .static v => .static v
  | .hw h => .hw h
  | .handle h => .handle h
  | a => .agg a

/-!
The part of a container that the value `v` gives. A handle is a handle leaf. A waiting literal
has none.
-/
def Val.agg? : Val → Option Agg
  | .static v => some (.static v)
  | .hw h => some (.hw h)
  | .agg a => some a
  | .handle h => some (.handle h)
  | .pending .. => none

/-!
A value with a hardware leaf: each hardware value and each aggregate with a hardware leaf. A
container of handles has none. A use that takes only static values asks this, so it does not
depend on the form of the value.
-/
def Val.hasHw : Val → Bool
  | .hw _ => true
  | .agg a => 0 < a.leaves
  | _ => false

/-! The type of a value. A handle has its handle type (`Handle.ty?`). -/
def Val.ty? : Val → Option Ty
  | .static v => v.ty?
  | .hw h => some h.ty
  | .agg a => a.ty?
  | .handle h => h.ty?
  | .pending .. => none

def Val.text : Val → String
  | .static v => v.text
  | .hw h => (Agg.hw h).text
  | .agg a => a.text
  | .handle h => h.text
  | .pending _ p => s!"{p.text} without a type"

/-! The source name of the resource at `path`: its first user name, else its outer name. -/
def sourceOf (path : Path) : String :=
  (path.inner.findSome? fun | .user u => some u | _ => none).getD path.outer

/-!
The value `{a}` of a message (section 6.2). A handle names its handle type (section 5.1), an own
output its source name, and a domain its name. A literal that waits for its type is `[]`. Each
other value names its type. Thus the text reads no value in full, and each type text is bounded.
-/
def Val.about : Val → String
  | .handle (.res .output _ _ path) => s!"the output `{sourceOf path}`"
  | .handle (.domain x) => s!"the domain `{x}`"
  | .handle h => match h.ty? with
    | some t => s!"a handle of `{t.text}`"
    | none => (Val.handle h).text
  | .pending .. => "`[]`"
  | v => match v.ty? with
    | some t => s!"a value of `{t.text}`"
    | none => v.text

/-!
A local. A string, a type, an own output, and a domain without an annotation have no `Ty`, so
their `ty` is `none`. A local of a handle, also without an annotation, holds its handle type
(section 5.4).
-/
structure Slot where
  ty : Option Ty
  mutable : Bool
  value : Val

/-! A frame of section 7.3: its path, and its number in the table of frames. The root is 0. -/
structure Frame where
  path : Option Path
  id : Nat

/-!
The symbols of a file. Each distinct identifier gets one number, so a lookup or a key compares
numbers and not text. `binders` gives the symbol of each local number of each item. `fields`
gives the symbol of each field name by its position in each item, and the last entry is the
top expression. `items` gives the symbol of each item name. `members` gives the number of each
field of each struct item by the symbol of its name.
-/
structure Syms where
  binders : Array (Array Nat)
  fields : Array (Std.TreeMap Pos Nat Pos.compare)
  items : Array Nat
  members : Array (Std.TreeMap Nat Nat compare)

/-! The kind of a guard (section 9.4): a hardware arm or a structural context. -/
inductive GuardKind where
  | arm
  | structural
  deriving DecidableEq, BEq

/-!
The innermost guard (section 9.4): its kind, the nesting depth at its start, and `callee`. The
`callee` is the item of the outermost call under the guard. A call records its item only when
the guard has no record. A deeper call thus keeps the record, and the return of the call ends
it. The record is an index, so it costs O(1), and the name renders only in an error. Its texts
of `S016` name the kind: `change` for a mutation of the binding `x`, and `effect` for the graph
effect `g`. The texts are normative, and the front ends print them exactly.
-/
structure Guard where
  kind : GuardKind
  depth : Nat
  callee : Option Nat := none

def Guard.change (g : Guard) (x : String) : String :=
  match g.kind with
  | .arm => "a hardware arm changes a binding from before the arm"
  | .structural => s!"a type or a constant cannot change `{x}`; change `{x}` before it, " ++
    "keep the result in a `let`, and use that name here"

def Guard.effect (g : Guard) (f : String) : String :=
  match g.kind with
  | .arm => s!"a hardware arm has no graph effect such as `{f}`; call `{f}` before the `if` " ++
    "or `match`, and use its result in the arm"
  | .structural =>
    s!"a type or a constant has no graph effect such as `{f}`; call it before and use the result"

/-! The source name of an item. -/
def itemName : Resolve.Item → String
  | .const _ n .. | .fn _ _ n .. | .module _ n .. | .struct _ n .. | .alias _ n ..
  | .enum _ n .. => n.name

/-!
The items, the depth limit, the current depth, and the return type of the current call. The
item whose body runs, its symbols, and the current frame name the hardware. `binding` holds
the struct items whose parameter types evaluate now. `guard` is the innermost guard
(section 9.4). `mode` is the item of the outermost `comptime fn` of the call chain, else
`none` (section 9.4). A call sets it in O(1), and the name renders only in an error. `site`
is the name of a function value while its signature evaluates: each depth check there reports
at it. `inst` is the emitted name of the current instantiation, else
`-`. `calls` holds the call frames from the module body, innermost first (section 8.2). A frame
is the item name of the callee and the position of its call. A call adds its frame in one step,
and the records share the list. `digest` makes the digest of an emitted name (section 7.1), so a
test can replace it.
-/
structure Ctx where
  items : Array Resolve.Item
  limit : Nat
  depth : Nat
  ret : Option Ty
  item : Nat
  syms : Syms
  frame : Frame
  binding : List Nat
  guard : Option Guard
  mode : Option Nat
  site : Option Pos
  inst : String
  calls : List (String × Pos)
  digest : String → String

/-! The source name of the item `i`, for an error text. -/
def Ctx.itemName (c : Ctx) (i : Nat) : String := (c.items[i]?.map Eval.itemName).getD ""

/-! The context with a new guard of the kind `k` at the current depth: the innermost guard. -/
def Ctx.guarded (c : Ctx) (k : GuardKind) : Ctx :=
  { c with guard := some { kind := k, depth := c.depth } }

/-! The symbol of the local number `id` in the current item. Each binder has one. -/
def Ctx.binder (c : Ctx) (id : Nat) : Nat := ((c.syms.binders[c.item]?).bind (·[id]?)).getD 0

/-! The symbol of the field name at `p` in the current item. -/
def Ctx.field (c : Ctx) (p : Pos) : Option Nat := (c.syms.fields[c.item]?).bind (·[p]?)

/-!
The key of a binding in a frame: the symbol of its source name. A call result takes no version
(section 7.3), so it has no key.
-/
inductive Tag where
  | sym (n : Nat)
  deriving DecidableEq, BEq, Hashable

/-! A named hardware binding: its core name, its value, and the position of the binding. -/
structure Let where
  path : Path
  value : Hw
  pos : Pos

/-!
A memory of one instantiation (section 7.6): its name, its path, its word type, its depth, and
its `mem` statement. `read` holds the request of its first `read_port` call: the address and the
enable. `write` holds the request of its first `write_port` call: the address, the data, and the
enable. Each part of a request is after its typed use. `dup` holds the first `S018` of a second
call by position (section 6.2).
-/
structure Mem where
  name : String
  path : Path
  word : Ty
  depth : Nat
  pos : Pos
  read : Option (Agg × Agg) := none
  write : Option (Agg × Agg × Agg) := none
  dup : Option Error := none

/-! The address width of a memory of the depth `n`: `max(1, ⌈log₂ n⌉)` (section 7.6). -/
def addrWidth (n : Nat) : Nat := max 1 (Nat.log2 (n - 1) + 1)

/-!
The names of one instantiation. `frames` numbers each frame by its parent and its field pair.
`versions` counts the bindings of each tag in each frame. `lets` holds the named bindings in
evaluation order. Each table grows only with the bindings that run. `shares` counts the marks of
shared operands (`Op.share`). `mems` holds the memories by their number, with their port calls.
-/
structure Naming where
  frames : Std.HashMap (Nat × Nat × Field) Nat := {}
  versions : Std.HashMap (Nat × Tag) Nat := {}
  lets : Array Let := #[]
  shares : Nat := 0
  mems : Array Mem := #[]

end Silicon.Source.Eval

/-!
The hardware description and the work of an instantiation (section 5.3). `Elab` makes
them, and the lowering reads them.
-/
namespace Silicon.Source.Elab

open Resolve Names Eval

/-! A port declaration. A port keeps its source name. -/
structure PortDecl where
  name : String
  sym : Nat
  input : Bool
  ty : Ty
  pos : Pos

structure RegDecl where
  path : Path
  ty : Ty
  init : Value
  pos : Pos

structure WireDecl where
  path : Path
  ty : Ty
  pos : Pos

/-! A child instance: its path, the interface of its instantiation, its statement, and its name. -/
structure ChildDecl where
  path : Path
  iface : Iface
  pos : Pos
  name : String

/-!
The target of a `:=` binding: an own resource, or an input of the child number `index`. The
input names its port by its core name, and `ty` gives its leaves.
-/
inductive Sink where
  | own (kind : Kind) (ty : Ty) (path : Path)
  | child (index : Nat) (inst : Path) (port : Name) (ty : Ty)

/-! A `:=` binding. Its value has the type of the sink, and the lowering takes it leaf by leaf. -/
structure Bind where
  sink : Sink
  value : Agg
  pos : Pos

/-!
The hardware description of one instantiation, in evaluation order. A combinational module
has no domain.
-/
structure Body where
  domain : Option String
  ports : Array PortDecl := #[]
  regs : Array RegDecl := #[]
  wires : Array WireDecl := #[]
  mems : Array Mem := #[]
  lets : Array Let := #[]
  children : Array ChildDecl := #[]
  binds : Array Bind := #[]

/-! A resource that needs one binding, by its number: its declaration and its bindings. -/
structure Need where
  name : String
  pos : Pos
  count : Nat

/-!
The work of the current instantiation. The resource number indexes `needs`, and the instance
number indexes `bound`. The memories are in the names of the instantiation (`Naming.mems`).
`inputs` counts the bindings of each child input. `dup` holds the first `S018` of a second
binding by position. `spent` is the fuel of the new children.
-/
structure Work where
  body : Body
  needs : Array Need := #[]
  bound : Array Nat := #[]
  inputs : Std.HashMap (Nat × Nat) Nat := {}
  dup : Option Error := none
  spent : Nat := 0

/-! The state of an `InstantiationId` in the table of instantiations. -/
inductive Status where
  | inProgress
  | done (index : Nat)

/-!
A done instantiation: its identity, its interface, its description, its units, and the position
of its module item.
-/
structure Inst where
  id : InstantiationId
  iface : Iface
  body : Body
  units : Nat
  pos : Pos

/-!
The tables of the instantiations. `table` maps the serialization of each `InstantiationId` to
its state, and `names` holds the emitted name of each instantiation that is in progress or done.
`work` is the work of the current instantiation.
-/
structure Insts where
  table : Std.HashMap String Status := {}
  names : Std.HashSet String := {}
  done : Array Inst := #[]
  work : Work := { body := { domain := none } }

end Silicon.Source.Elab

namespace Silicon.Source.Eval

open Resolve Names

/-! An observation record: its line of section 8.2, with no line end. -/
abbrev Record := String

/-!
The state holds the fuel, the table of constants by item index, and the table of struct
specializations. It also holds the locals of the current frame and the names of the current
instantiation. `holds` counts the waiting results that hold each local of the frame (section
5.4). `changes` counts the mutations of each local of the frame, so an index finds that it
changed its root (section 5.4). `pending` counts the open windows of each root of the frame
(section 9.1). `inst` holds the tables of the instantiations. `records` holds the observation
records of the elaboration in their order (section 8.2).
-/
structure St where
  fuel : Nat
  consts : Array Entry
  specs : Specs
  frame : Std.HashMap Nat Slot
  holds : Std.HashMap Nat Nat
  changes : Std.HashMap Nat Nat
  pending : Std.TreeMap Nat Nat compare
  naming : Naming
  inst : Elab.Insts
  records : Array Record

/-!
The stop of a run: its first error and the records before it. An error keeps the records before
it (section 8.2), so `fail` is the only way that `M` stops.
-/
structure Stop where
  err : Error
  records : Array Record

abbrev M := ReaderT Ctx (StateT St (Except Stop))

/-! An error without a position. The caller adds the position of its node. -/
abbrev Fault := ErrorCode × String

/-! The charge of an operation and the operation itself. The charge comes first. -/
structure Step where
  charge : Nat
  run : Unit → Except Fault Value

/-! A string in a message: at most 64 characters, then a note of the full length. -/
def strText (m : String) : String :=
  if m.length ≤ 64 then m else s!"{(m.take 64).toString}... ({m.length} characters)"

/-! The error stops the run. The stop holds the records so far, with no copy. -/
def fail (code : ErrorCode) (pos : Pos) (msg : String) : M α :=
  fun _ s => .error ⟨⟨code, pos, msg⟩, s.records⟩

def lift (pos : Pos) : Except Fault α → M α
  | .ok a => pure a
  | .error (c, m) => fail c pos m

def typeError (msg : String) : Except Fault α := .error (.S010, msg)

/-!
Pays `units` from the fuel, or fails with `S015` at `pos`. `cannot left` is the message when
`left` units remain.
-/
def chargeWith (pos : Pos) (units : Nat) (cannot : Nat → String) : M Unit := do
  let s ← get
  if units ≤ s.fuel then set { s with fuel := s.fuel - units }
  else fail .S015 pos (cannot s.fuel)

/-! The message of a charge of `units` when `left` units remain. -/
def payText (units left : Nat) : String :=
  s!"the fuel cannot pay {intText units} unit(s); {intText left} remain; raise --fuel"

def charge (pos : Pos) (units : Nat) : M Unit :=
  chargeWith pos units (payText units)

/-! The charge of an entry function at the bound 0. The fuel is 0 there, so it fails. -/
def exhausted (pos : Pos) : M α := do
  charge pos 1
  fail .S015 pos "the fuel is exhausted; raise --fuel"

/-! Runs `act` and gives the fuel that it uses. The result reads only a difference of fuel. -/
def measure (act : M α) : M (α × Nat) := do
  let start := (← get).fuel
  let a ← act
  return (a, start - (← get).fuel)

/-!
Runs `act` one level deeper, or gives `S015` at `pos` above the limit. The level reports its
own depth checks, so it clears `site`.
-/
def nested (pos : Pos) (act : M α) : M α := do
  let c ← readThe Ctx
  if c.limit ≤ c.depth then
    fail .S015 pos s!"the nesting depth goes above {c.limit}; raise --depth"
  withTheReader Ctx (fun c => { c with depth := c.depth + 1, site := none }) act

/-!
Runs `act` in a structural context (section 9.4): its guard starts at the current depth, so it
is the innermost guard.
-/
def structural (act : M α) : M α :=
  withTheReader Ctx (·.guarded .structural) act

/-!
A mutation at `pos` of the binding `x` of the current frame of locals (section 9.4). `x` is the
root of the changed place. Each call, each constant, and each struct use nests one level deeper
with a new frame. Thus the binding is older than the innermost guard when that guard started at
the current depth: `S016`.
-/
def mutation (pos : Pos) (x : String) : M Unit := do
  let c ← read
  if let some g := c.guard then
    if g.depth == c.depth then fail .S016 pos (g.change x)

/-!
Runs `act` with an empty frame of locals and the return type `ret`. A waiting result of the
caller holds no local of the new frame, and a window of the caller holds no root of it. The
tables of the caller wait unchanged, with no copy.
-/
def inFrame (ret : Option Ty) (act : M α) : M α := do
  let saved ← (do let s ← get; return (s.frame, s.holds, s.changes, s.pending) : M _)
  modify fun s => { s with frame := {}, holds := {}, changes := {}, pending := {} }
  let r ← withTheReader Ctx (fun c => { c with ret }) act
  modify fun s =>
    { s with frame := saved.1, holds := saved.2.1, changes := saved.2.2.1,
             pending := saved.2.2.2 }
  return r

/-!
Local numbers are dense over the whole item, also in branches that do not run. The frame thus
holds only the bindings that run, and each of them pays its charge.
-/
def bindLocal (id : Nat) (slot : Slot) : M Unit :=
  modify fun s => { s with frame := s.frame.insert id slot }

def setConst (i : Nat) (e : Entry) : M Unit :=
  modify fun s => { s with consts := s.consts.set! i e }

/-! The finite value of a signedness and a width. -/
def finite (signed : Bool) (w : Nat) (x : BitVec w) : Value :=
  if signed then .sint w x else .uint w x

/-! Two finite operands of one type: the signedness, the width, and both bit vectors. -/
def finitePair : Value → Value → Option (Bool × (w : Nat) × BitVec w × BitVec w)
  | .uint w x, .uint v y => if h : v = w then some (false, ⟨w, x, h ▸ y⟩) else none
  | .sint w x, .sint v y => if h : v = w then some (true, ⟨w, x, h ▸ y⟩) else none
  | _, _ => none

/-! `&`, `|`, and `^` on `Int` in infinite two's complement. `negSucc x` is `~x`. -/
def intAnd : Int → Int → Int
  | .ofNat p, .ofNat q => .ofNat (p &&& q)
  | .ofNat p, .negSucc x | .negSucc x, .ofNat p => .ofNat (p - (p &&& x))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)

def intOr : Int → Int → Int
  | .ofNat p, .ofNat q => .ofNat (p ||| q)
  | .ofNat p, .negSucc x | .negSucc x, .ofNat p => .negSucc (x - (x &&& p))
  | .negSucc x, .negSucc y => .negSucc (x &&& y)

def intXor : Int → Int → Int
  | .ofNat p, .ofNat q => .ofNat (p ^^^ q)
  | .ofNat p, .negSucc x | .negSucc x, .ofNat p => .negSucc (p ^^^ x)
  | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

/-! `floor (a / 2^k)`. A count above the bit length gives 0 or -1 without a large shift. -/
def intShr (a : Int) (k : Nat) : Int :=
  if a.natAbs.log2 < k then (if a < 0 then -1 else 0) else a >>> k

/-!
The size limit of section 5.4. It bounds the bits of a static integer and of a metadata number.
It also bounds the bytes of a string and the elements of a list. A fuel near `2^64` pays for a
value that no machine can hold, so the limit stops the value before its charge.
-/
def limit : Nat := 2 ^ 32

/-! A number of bits, bytes, or elements above the limit. -/
def over (n : Nat) : Bool := limit < n

/-! The bit length of the magnitude of `n`. It is 0 for 0. -/
def bitLength (n : Int) : Nat := if n == 0 then 0 else n.natAbs.log2 + 1

def intLimitText : String :=
  "the result can have more than 2^32 bits, the limit of a static Int; use smaller operands"

def strLimitText : String :=
  "the string has more than 2^32 bytes, the limit of a string; use shorter strings"

def listLimitText : String :=
  "the list has more than 2^32 elements, the limit of a list; use a shorter list"

def zeroLimitText : String :=
  "the value of the type has a size above 2^32, the limit of a value from a type; " ++
  "use a smaller type or keep it a reference"

def recordLimitText : String :=
  "the recorded value has a size above 2^32, the limit of a record; record a smaller part"

/-!
The bound on the bit length of the result of a static integer operator, from the bit lengths
`a` and `b` of its operands (section 5.4). `<<` has its own bound (`shlBits`). The other
operators make no result longer than an operand, so their bound is in the limit.
-/
def intBound (op : BinOp) (a b : Nat) : Nat :=
  match op with
  | .mul => a + b
  | .add | .sub | .and | .or | .xor => max a b + 1
  | _ => max a b

/-!
The bit length of `x <<< k`. It is exact, and it needs no shift. A count above the limit is
above the limit with no addition, so a huge `k` costs nothing.
-/
def shlBits (x : Int) (k : Nat) : Nat :=
  if x == 0 then 0 else if over k then limit + 1 else bitLength x + k

/-! The step `s` of an integer result with the bit length bound `b`, or `S015` above the limit. -/
def capped (b : Nat) (s : Step) : Except Fault Step :=
  if over b then .error (.S015, intLimitText) else .ok s

/-! The size of `a * 2^k`, from the bit length of `a`, before the shift runs. -/
def shlSize (a : Int) (k : Nat) : Nat :=
  if a == 0 then 1 else (a.natAbs.log2 + k) / 64 + 1

/-!
`a * 2^k` without the power `2^k`. The shift makes no value above the result, and a zero
operand makes no value at all. Thus the work stays in the charge `shlSize a k`.
-/
def intShl (a : Int) (k : Nat) : Int :=
  if a == 0 then 0 else a <<< k

theorem intShl_eq (a : Int) (k : Nat) : intShl a k = a * 2 ^ k := by
  unfold intShl
  split
  · simp_all
  · exact Int.shiftLeft_eq a k

/-! A count of a finite shift. The amount `min k w` fits `w` bits, because `w < 2^w`. -/
def amount (w k : Nat) : BitVec w := BitVec.ofNat w (min k w)

/-! The range of a finite type, for the fit rule. -/
def fits (t : Ty) (n : Int) : Bool :=
  match t with
  | .uint w => 0 ≤ n && n < 2 ^ w
  | .sint w => -(2 ^ (w - 1) : Int) ≤ n && n < 2 ^ (w - 1)
  | .nat => 0 ≤ n
  | _ => true

/-! The `S012` text of the static integer `n` that does not fit the type `t`. -/
def fitText (t : Ty) (n : Int) : String :=
  if t matches .nat then s!"{intText n} is not a Nat" else s!"{intText n} does not fit {t.text}"

/-!
A typed use of a scalar, `()`, a record, an enum value, or a function at `t`. Only a static
integer at a finite type converts. A `()` part of a container comes here, because it has no
elements. A record needs its own struct type, because a struct type is nominal. An enum value
needs its own enum type for the same reason, and it converts nothing (section 5.1). A function
needs its exact function type, also in the `mut` marks, and charges nothing.
-/
def convertLeaf (t : Ty) (v : Value) : Except Fault Step :=
  let same := Except.ok ⟨0, fun _ => .ok v⟩
  let wrong := typeError s!"expected {t.text}, but the value is {v.text}"
  match t, v with
  | .unit, .unit | .bool, .bool _ | .int, .int _ | .type, .type _ | .string, .str _ => same
  | .struct .., .record s _ | .enum .., .enum s .. => if s.same t then same else wrong
  | .fn .., .function _ _ ps r => if (Ty.fn ps r).same t then same else wrong
  | .nat, .int n => if 0 ≤ n then same else .error (.S012, fitText t n)
  | .uint w, .uint u _ | .sint w, .sint u _ => if u == w then same else wrong
  | .uint w, .int n | .sint w, .int n =>
    .ok ⟨(Value.int n).size + widthSize w, fun _ =>
      if fits t n then .ok (finite (t matches .sint _) w (BitVec.ofInt w n))
      else .error (.S012, fitText t n)⟩
  | _, _ => wrong

/-! The size of a scalar `v` after its typed use at `t`. -/
def leafSize (t : Ty) (v : Value) : Nat :=
  match t with
  | .uint w | .sint w => widthSize w
  | _ => v.size

/-! An operation runs in its step after the charge, so each result is a thunk. -/
def unary (op : UnOp) (a : Value) : Except Fault Step :=
  let step (r : Unit → Value) : Except Fault Step := .ok ⟨a.size, fun u => .ok (r u)⟩
  match op, a with
  | .not, .bool b => step fun _ => .bool !b
  | .inv, .int n => capped (bitLength n + 1) ⟨a.size, fun _ => .ok (.int (Int.not n))⟩
  | .neg, .int n => step fun _ => .int (-n)
  | .inv, .uint w x => step fun _ => .uint w (~~~x)
  | .inv, .sint w x => step fun _ => .sint w (~~~x)
  | .neg, .uint w x => step fun _ => .uint w (Core.Semantics.evalOp .sub (by decide) 0 x)
  | .neg, .sint w x => step fun _ => .sint w (Core.Semantics.evalOp .sub (by decide) 0 x)
  | _, _ => typeError s!"`{op.text}` does not accept {a.text}"

/-! The ordinary operators on `Int`. They do not wrap. -/
def intArith (op : BinOp) (x y : Int) : Except Fault Value :=
  match op with
  | .add => .ok (.int (x + y))
  | .sub => .ok (.int (x - y))
  | .mul => .ok (.int (x * y))
  | .div => if y == 0 then .error (.S013, "division by zero") else .ok (.int (x.tdiv y))
  | .rem => if y == 0 then .error (.S013, "remainder by zero") else .ok (.int (x.tmod y))
  | _ => typeError s!"`{op.text}` is not an ordinary operator"

/-! The core operation of a wrapping or bitwise operator. -/
def coreOp : BinOp → Option Core.BinOp
  | .addw => some .add | .subw => some .sub | .mulw => some .mul
  | .and => some .and | .or => some .or | .xor => some .xor
  | _ => none

def finiteOp (op : Core.BinOp) (s : Bool) (w : Nat) (x y : BitVec w) : Value :=
  if h : op = .concat then finite s w x else finite s w (Core.Semantics.evalOp op h x y)

/-! The core predicate of an ordering, by signedness. -/
def pred (op : BinOp) (signed : Bool) : Core.Pred :=
  match op, signed with
  | .lt, false => .ult | .le, false => .ule | .gt, false => .ugt | .ge, false => .uge
  | .lt, true => .slt | .le, true => .sle | .gt, true => .sgt | _, true => .sge
  | _, false => .uge

def shift (op : BinOp) (a b : Value) : Except Fault Step := do
  let count : Except Fault Nat := match b with
    | .int k =>
      if k < 0 then .error (.S013, s!"the shift count {intText k} is negative") else .ok k.toNat
    | .uint _ x => .ok x.toNat
    | _ => typeError s!"a shift count is UInt or a static Int, not {b.text}"
  match a with
  | .int x =>
    unless b matches .int _ do typeError "an Int shift needs a static Int count"
    let k ← count
    if op == .shl then capped (shlBits x k) ⟨shlSize x k, fun _ => .ok (.int (intShl x k))⟩
    else .ok ⟨a.size, fun _ => .ok (.int (intShr x k))⟩
  | .uint w x | .sint w x =>
    let k ← count
    let s := a matches .sint ..
    let c : Core.BinOp := if op == .shl then .shl else if s then .shrs else .shru
    .ok ⟨widthSize w, fun _ => .ok (finiteOp c s w x (amount w k))⟩
  | _ => typeError s!"`{op.text}` does not accept {a.text}"

/-! The type check of `==`, and the comparison as a thunk for the step after the charge. -/
def equal (a b : Value) : Except Fault (Unit → Bool) :=
  match a, b with
  | .int x, .int y => .ok fun _ => x == y
  | .bool x, .bool y => .ok fun _ => x == y
  | .str x, .str y => .ok fun _ => x == y
  | .type x, .type y => .ok fun _ => x.same y
  | _, _ =>
    match finitePair a b with
    | some (_, ⟨_, x, y⟩) => .ok fun _ => x == y
    | none => typeError s!"`==` compares values of one type, not {a.text} and {b.text}"

def order (op : BinOp) (a b : Value) : Except Fault (Unit → Bool) :=
  match a, b with
  | .int x, .int y =>
    .ok fun _ => match op with | .lt => x < y | .le => x ≤ y | .gt => x > y | _ => x ≥ y
  | _, _ =>
    match finitePair a b with
    | some (s, ⟨_, x, y⟩) => .ok fun _ => Core.Semantics.evalPred (pred op s) x y == 1
    | none => typeError s!"`{op.text}` orders integers of one type, not {a.text} and {b.text}"

def apply (pos : Pos) (s : Except Fault Step) : M Value := do
  let s ← lift pos s
  charge pos s.charge
  lift pos (s.run ())

end Silicon.Source.Eval
