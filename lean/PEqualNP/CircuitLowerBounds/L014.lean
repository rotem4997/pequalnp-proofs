import PEqualNP.CircuitLowerBounds.Helpers.ThresholdParity

/-- Parity is a threshold of `n` thresholds: gate `j` tests that at least `j + 1` inputs are
true, and the top gate sums them with alternating signs. -/
theorem PEqualNP.CircuitLowerBounds.L014 :
    ({x : List Bool | x.count true % 2 = 1} : Language Bool) ∈
      PEqualNP.CircuitLowerBounds.THRTHR (fun n => n) :=
  PEqualNP.CircuitLowerBounds.Helpers.parity_mem_THRTHR
