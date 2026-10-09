import Silicon.Core.Vectors
import Silicon.Core.Text
import Silicon.Core.Check

/-! Input vectors use port order and decimal values within the port width. -/
namespace Silicon.Core.Test.Vectors

private def inputs (source line : String) : Option (List (String × Nat)) := do
  let d ← (parse source >>= check).toOption
  let m ← d.bodies.head?
  (parseInputLine m line).toOption

private def counter := "(design top (module top
  (input rst (bits 1)) (input clk clock) (input en (bits 1))))"

#guard inputs counter "in=(rst 0 en 1)" == some [("rst", 0), ("en", 1)]
#guard inputs counter " \tin=(\trst\t000 en 01\t) " == some [("rst", 0), ("en", 1)]
#guard (inputs counter "in=(en 1 rst 0)").isNone
#guard (inputs counter "in=(rst 0)").isNone
#guard (inputs counter "in=(rst 0 en 1 x 1)").isNone
#guard (inputs counter "in=(rst 2 en 1)").isNone
#guard (inputs counter "").isNone
#guard (inputs counter "in=(rst 0 en 1)\r").isNone
#guard (inputs counter "in=(rst 0\nen 1)").isNone
#guard (inputs counter "in=(rst +0 en 1)").isNone
#guard (inputs counter "in=(rst 0 en 1) x").isNone
#guard (inputs counter "in = (rst 0 en 1)").isNone

private def wide := "(design top (module top (input x (bits 40))))"
#guard inputs wide "in=(x 1099511627775)" == some [("x", 1099511627775)]
#guard (inputs wide "in=(x 1099511627776)").isNone
#guard inputs "(design top (module top))" "in=()" == some []
#guard printOutputLine [("q", 0)] == "out=(q 0)\n"
#guard printOutputLine [("q", 12), ("r", 3)] == "out=(q 12 r 3)\n"
#guard printOutputLine [] == "out=()\n"
#guard errorLine ⟨.E004, ⟨12, 5, []⟩, "width mismatch"⟩ ==
  "error[E004]: 12:5: width mismatch"

end Silicon.Core.Test.Vectors
