import Silicon.Core.Semantics.Drivers

/-! Module outputs read the solved values of their own assignment equations. -/
namespace Silicon.Core.Semantics

def outputValues (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (values : Valuation m.ctx) : Output m :=
  fun port => match ht : port.val.ty with
    | .clock => ()
    | .bits width => values (.name port.val.name) width
      (port_found d.design d.wellFormed m hm port.val port.property.1 ht)

theorem outputValues_bits (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (values : Valuation m.ctx) (port : PortRef m.ports .output)
    (width : Nat) (ht : port.val.ty = .bits width) :
    cast (congrArg TyValue ht) (outputValues d m hm values port) =
      values (.name port.val.name) width
        (port_found d.design d.wellFormed m hm port.val port.property.1 ht) := by
  rcases port with ⟨⟨pos, dir, name, ty⟩, member, direction⟩
  cases ty <;> cases ht
  rfl

end Silicon.Core.Semantics
