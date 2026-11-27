import PEqualNP.CircuitLowerBounds.Helpers.Switching.Wire
import PEqualNP.CircuitLowerBounds.Helpers.Switching.Round

/-!
# Hastad's bound for parity, with the switching lemma as the one hypothesis left
-/

namespace PEqualNP.CircuitLowerBounds.Switching

/-- The switching lemma in its semantic counting form gives the recorded statement of
L-lib-034. -/
theorem stmt034_of_switching (h : Plan.SwitchingSem) : Plan.Stmt034 :=
  Plan.stmt034_of_round (PEqualNP.CircuitLowerBounds.Switching.Round.roundOfSwitching h)

end PEqualNP.CircuitLowerBounds.Switching
