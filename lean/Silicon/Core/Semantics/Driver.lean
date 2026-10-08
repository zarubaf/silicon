import Silicon.Core.Semantics.State

/-!
A value driver names the exact typed equation or input port that supplies a value.
Memory drivers select finite state cells and cannot select a combinational equation.
-/
namespace Silicon.Core.Semantics

inductive ValueDriver (m : Typed.Module) : Deps.Node → Nat → Type where
  | input (port : Port) (member : port ∈ m.ports) (dir : port.dir = .input)
      (bits : port.ty = .bits width) : ValueDriver m (.name port.name) width
  | let_ (index : Nat) (pos : Pos) (name : String) (width : Nat)
      (expr : Typed.Expr m.ctx (.bits width))
      (member : .let_ index pos name width expr ∈ m.body) : ValueDriver m (.name name) width
  | reg (index : Nat) (pos : Pos) (name : String) (width : Nat) (clock : String)
      (target : Typed.valueTy m.ctx name = some (.bits width))
      (reset : Option (Typed.Reset m.ctx width)) (nextIndex : Nat) (nextPos : Pos)
      (next : Typed.Expr m.ctx (.bits width))
      (member : .reg index pos name width clock target reset nextIndex nextPos next ∈ m.body) :
      ValueDriver m (.name name) width
  | assign (index : Nat) (pos : Pos) (name : String) (width : Nat)
      (target : Typed.valueTy m.ctx name = some (.bits width))
      (expr : Typed.Expr m.ctx (.bits width))
      (member : .assign index pos name width target expr ∈ m.body) :
      ValueDriver m (.name name) width
  | inst (index : Nat) (pos : Pos) (name child : String)
      (inputs : List ((p : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx p.val.ty))
      (member : .inst index pos name child inputs ∈ m.body)
      (port : Port) (portMember : port ∈ m.interfaces child) (dir : port.dir = .output)
      (bits : port.ty = .bits width) : ValueDriver m (.port name port.name) width

inductive MemoryDriver (m : Typed.Module) : String → Nat → Nat → Type where
  | mem (index : Nat) (pos : Pos) (name : String) (width depth : Nat) (clock : String)
      (target : m.ctx.lookup (.name name) = some (.memory width depth))
      (writes : List (Typed.Write m.ctx width depth))
      (member : .mem index pos name width depth clock target writes ∈ m.body) :
      MemoryDriver m name width depth

/-! A decoded driver reads inputs, current state, or the current equation valuation. -/
def ValueDriver.eval (m : Typed.Module) (children : Children m) (state : LocalState m children)
    (input : Input m) (values : Valuation m.ctx) (memories : Memories m.ctx)
    (connections : ConnectionValues m) : ValueDriver m node width → Value width
  | .input p member dir bits => cast (congrArg TyValue bits) (input ⟨p, member, dir⟩)
  | .let_ _ _ _ _ expr _ | .assign _ _ _ _ _ expr _ => evalExpr values memories expr
  | .reg i p n w c target reset ni np next member =>
    state ⟨.reg i p n w c target reset ni np next, member⟩
  | .inst i p n child inputs member port portMember dir bits =>
    let e : EquationRef m := ⟨.inst i p n child inputs, member⟩
    cast (congrArg TyValue bits)
      ((children e).out (state e) (connections e) ⟨port, portMember, dir⟩)

def MemoryDriver.eval (m : Typed.Module) (children : Children m) (state : LocalState m children) :
    MemoryDriver m name width depth → Fin depth → Value width
  | .mem i p n w d c target writes member => state ⟨.mem i p n w d c target writes, member⟩

end Silicon.Core.Semantics
