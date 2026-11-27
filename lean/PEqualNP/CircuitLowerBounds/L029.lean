import PEqualNP.CircuitLowerBounds.Helpers.ThrThrClosure

/-- Depth-two threshold circuits are closed under complement with the same bound on the number
of bottom gates: the complement of a language with such circuits with `s n` bottom gates has
such circuits with `s n` bottom gates. -/
theorem PEqualNP.CircuitLowerBounds.L029 :
    ∀ (s : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.CircuitLowerBounds.THRTHR s →
      Lᶜ ∈ PEqualNP.CircuitLowerBounds.THRTHR s :=
  PEqualNP.CircuitLowerBounds.Helpers.thrthr_compl
