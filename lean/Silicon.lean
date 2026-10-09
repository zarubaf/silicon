import Silicon.Core.Syntax
import Silicon.Core.Text
import Silicon.Core.Test.Text
import Silicon.Core.GraphReach
import Silicon.Core.Deps
import Silicon.Core.Test.Deps
import Silicon.Core.Typed
import Silicon.Core.Order
import Silicon.Core.Reassemble
import Silicon.Core.StatementOrder
import Silicon.Core.Complete
import Silicon.Core.GraphIndex
import Silicon.Core.GraphSCC
import Silicon.Core.GraphDFSBase
import Silicon.Core.GraphDFSInvariant
import Silicon.Core.GraphDFSState
import Silicon.Core.GraphDFS
import Silicon.Core.GraphFlood
import Silicon.Core.GraphComponents
import Silicon.Core.GraphCycleIndex
import Silicon.Core.Check
import Silicon.Core.Canonical.WellFormed
import Silicon.Core.Test.Check
import Silicon.Core.Semantics
import Silicon.Core.Interp
import Silicon.Core.Canonical.View
import Silicon.Core.Canonical.Local
import Silicon.Core.Canonical.Trace
import Silicon.Core.Test.Interp
import Silicon.Core.Test.Semantics
import Silicon.Core.Test.Step
import Silicon.Core.Test.Hierarchy
import Silicon.Core.Mlir.Syntax
import Silicon.Core.Mlir.Print
import Silicon.Core.MemModel
import Silicon.Core.Lower
import Silicon.Core.Test.Mlir
import Silicon.Core.Test.MemModel
import Silicon.Core.Test.Lower

/-!
Core IR semantics live here. The Lean model is the normative spec.
-/
