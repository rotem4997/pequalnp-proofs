import PEqualNP.CircuitLowerBounds.Helpers.Majority

/-- MAJORITY is in TC0. -/
theorem PEqualNP.CircuitLowerBounds.L012 :
    ({x : List Bool | x.length ≤ 2 * x.count true} : Language Bool) ∈
      PEqualNP.CircuitLowerBounds.TC0 :=
  PEqualNP.CircuitLowerBounds.Helpers.maj_in_TC0
