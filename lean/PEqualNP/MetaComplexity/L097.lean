import PEqualNP.MetaComplexity.Helpers.LgpSanity

/-- On two inputs, one AND gate is a minimal circuit for AND, and the same with a second copy of
the gate is a no instance. -/
theorem PEqualNP.MetaComplexity.L097 : PEqualNP.MetaComplexity.LgpYes 2 ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩ ∧ PEqualNP.MetaComplexity.LgpNo 2 ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩ :=
  ⟨PEqualNP.MetaComplexity.Helpers.LgpSanity.minimal_and2, PEqualNP.MetaComplexity.Helpers.LgpSanity.lgpNo_and2dup⟩
