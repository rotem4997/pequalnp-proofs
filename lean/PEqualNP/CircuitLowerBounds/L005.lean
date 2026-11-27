import PEqualNP.CircuitLowerBounds.Helpers.Shannon

/-- Some language is not in P/poly (Shannon's counting argument): the language that, at each
length, is a function with no small circuit. -/
theorem PEqualNP.CircuitLowerBounds.L005 :
    ∃ L : Language Bool, L ∉ PEqualNP.CircuitLowerBounds.PPoly :=
  ⟨PEqualNP.CircuitLowerBounds.Helpers.hardLang,
    PEqualNP.CircuitLowerBounds.Helpers.hardLang_not_ppoly⟩
