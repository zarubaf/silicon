/-!
The core syntax stores source positions and declared widths.
The checker gives these terms their types.
-/
namespace Silicon.Core

/-! Positions use line and column numbers that start at one. -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Clocks and bit vectors are distinct types. -/
inductive Ty where
  | clock
  | bits (n : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Each operation has one fixed spelling in the text format. -/
inductive UnOp where
  | not
  deriving Repr, DecidableEq, BEq, Inhabited

inductive BinOp where
  | add | sub | mul | and | or | xor | shl | shru | shrs | concat
  deriving Repr, DecidableEq, BEq, Inhabited

inductive Pred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Every expression records the start of its source form. -/
inductive Expr where
  | ref (pos : Pos) (name : String)
  | port (pos : Pos) (inst port : String)
  | const (pos : Pos) (width value : Nat)
  | un (pos : Pos) (op : UnOp) (arg : Expr)
  | bin (pos : Pos) (op : BinOp) (lhs rhs : Expr)
  | icmp (pos : Pos) (pred : Pred) (lhs rhs : Expr)
  | mux (pos : Pos) (cond yes no : Expr)
  | extract (pos : Pos) (arg : Expr) (lo width : Nat)
  | replicate (pos : Pos) (arg : Expr) (count : Nat)
  | read (pos : Pos) (mem : String) (addr : Expr)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! A reset has a kind, a signal, and a value. -/
inductive ResetKind where
  | sync
  deriving Repr, DecidableEq, BEq, Inhabited

structure Reset where
  kind : ResetKind
  signal : Expr
  value : Expr
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Statements describe equations and state updates. Widths remain unchecked here. -/
inductive Stmt where
  | let_ (pos : Pos) (name : String) (width : Nat) (value : Expr)
  | reg (pos : Pos) (name : String) (width : Nat) (clock : String) (reset : Option Reset)
  | next (pos : Pos) (name : String) (value : Expr)
  | mem (pos : Pos) (name : String) (width depth : Nat) (clock : String)
  | write (pos : Pos) (mem : String) (port : Nat) (addr data enable : Expr)
  | inst (pos : Pos) (name module : String) (inputs : List (String × Expr))
  | assign (pos : Pos) (name : String) (value : Expr)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Port order is part of a module's interface. -/
inductive PortDir where
  | input | output
  deriving Repr, DecidableEq, BEq, Inhabited

structure Port where
  pos : Pos
  dir : PortDir
  name : String
  ty : Ty
  deriving Repr, DecidableEq, BEq, Inhabited

/-! An extern lists the input dependencies of each output. -/
structure Dep where
  pos : Pos
  output : String
  inputs : List String
  deriving Repr, DecidableEq, BEq, Inhabited

structure Module where
  pos : Pos
  name : String
  ports : List Port
  body : List Stmt
  deriving Repr, DecidableEq, BEq, Inhabited

structure Extern where
  pos : Pos
  name : String
  ports : List Port
  deps : List Dep
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Source trees retain atom positions for errors within a form. -/
structure SourcePos where
  pos : Pos
  children : List Pos := []
  deriving Repr, DecidableEq, BEq, Inhabited

def SourcePos.locate (source : List SourcePos) : Pos → List Nat → Pos
  | p, [] => p
  | p, i :: path =>
    match source.find? (·.pos == p) with
    | some s => match s.children[i]? with
      | some child => SourcePos.locate source child path
      | none => p
    | none => p

/-! A design names its top module and stores modules and externs in input order. -/
inductive Item where
  | module (value : Module)
  | extern (value : Extern)
  deriving Repr, DecidableEq, BEq, Inhabited

structure Design where
  top : String
  items : List Item
  source : List SourcePos := []
  deriving Repr, DecidableEq, BEq, Inhabited

def Design.locate (d : Design) (p : Pos) (path : List Nat) : Pos :=
  SourcePos.locate d.source p path

def Design.topPos (d : Design) : Pos :=
  match d.source with
  | s :: _ => d.locate s.pos [1]
  | [] => ⟨1, 1⟩

/-! The shared error codes identify grammar, checker, and execution errors. -/
inductive ErrorCode where
  | E001 | E002 | E003 | E004 | E005 | E006 | E007
  | E008 | E009 | E010 | E011 | E012 | E013 | E014
  deriving Repr, DecidableEq, BEq, Inhabited

def ErrorCode.toString : ErrorCode → String
  | .E001 => "E001" | .E002 => "E002" | .E003 => "E003" | .E004 => "E004"
  | .E005 => "E005" | .E006 => "E006" | .E007 => "E007" | .E008 => "E008"
  | .E009 => "E009" | .E010 => "E010" | .E011 => "E011" | .E012 => "E012"
  | .E013 => "E013" | .E014 => "E014"

instance : ToString ErrorCode := ⟨ErrorCode.toString⟩

structure Error where
  code : ErrorCode
  pos : Pos
  msg : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-! Position erasure removes source locations without changing the syntax. -/
def Expr.erasePos : Expr → Expr
  | .ref _ n => .ref ⟨0, 0⟩ n
  | .port _ i n => .port ⟨0, 0⟩ i n
  | .const _ w v => .const ⟨0, 0⟩ w v
  | .un _ o a => .un ⟨0, 0⟩ o a.erasePos
  | .bin _ o a b => .bin ⟨0, 0⟩ o a.erasePos b.erasePos
  | .icmp _ o a b => .icmp ⟨0, 0⟩ o a.erasePos b.erasePos
  | .mux _ a b c => .mux ⟨0, 0⟩ a.erasePos b.erasePos c.erasePos
  | .extract _ a l w => .extract ⟨0, 0⟩ a.erasePos l w
  | .replicate _ a n => .replicate ⟨0, 0⟩ a.erasePos n
  | .read _ n a => .read ⟨0, 0⟩ n a.erasePos

def Reset.erasePos (r : Reset) : Reset :=
  { r with signal := r.signal.erasePos, value := r.value.erasePos }

def Stmt.erasePos : Stmt → Stmt
  | .let_ _ n w v => .let_ ⟨0, 0⟩ n w v.erasePos
  | .reg _ n w c r => .reg ⟨0, 0⟩ n w c (r.map Reset.erasePos)
  | .next _ n v => .next ⟨0, 0⟩ n v.erasePos
  | .mem _ n w d c => .mem ⟨0, 0⟩ n w d c
  | .write _ n i a d e => .write ⟨0, 0⟩ n i a.erasePos d.erasePos e.erasePos
  | .inst _ n m xs => .inst ⟨0, 0⟩ n m (xs.map fun (k, v) => (k, v.erasePos))
  | .assign _ n v => .assign ⟨0, 0⟩ n v.erasePos

def Port.erasePos (p : Port) : Port := { p with pos := ⟨0, 0⟩ }

def Dep.erasePos (d : Dep) : Dep := { d with pos := ⟨0, 0⟩ }

def Item.erasePos : Item → Item
  | .module m => .module
      { m with pos := ⟨0, 0⟩, ports := m.ports.map Port.erasePos, body := m.body.map Stmt.erasePos }
  | .extern e => .extern
      { e with pos := ⟨0, 0⟩, ports := e.ports.map Port.erasePos, deps := e.deps.map Dep.erasePos }

def Design.erasePos (d : Design) : Design :=
  { d with items := d.items.map Item.erasePos, source := [] }

end Silicon.Core
