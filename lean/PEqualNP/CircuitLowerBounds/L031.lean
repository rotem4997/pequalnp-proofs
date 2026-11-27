import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.Depth3

/-- Every language has depth 3 circuits of AND, OR and NOT gates of size `(n + 2) * 2 ^ n`:
a NOT layer, one AND gate per accepted string, and an OR gate on top. -/
theorem PEqualNP.CircuitLowerBounds.L031 : ∀ L : Language Bool,
    L ∈ PEqualNP.CircuitLowerBounds.SizeDepth
      {PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} (fun n : ℕ => (n + 2) * 2 ^ n) 3 :=
  fun L => PEqualNP.CircuitLowerBounds.Helpers.Depth3.depth3_universal L
