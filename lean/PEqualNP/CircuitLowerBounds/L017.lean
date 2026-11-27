import PEqualNP.CircuitLowerBounds.Helpers.EncodeThr

/-- The encoding of depth-two threshold circuits is injective. -/
theorem PEqualNP.CircuitLowerBounds.L017 :
    Function.Injective PEqualNP.CircuitLowerBounds.encodeThr :=
  PEqualNP.CircuitLowerBounds.Helpers.encodeThr_injective
