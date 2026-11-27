import PEqualNP.MetaComplexity.Helpers.LgpSanity

/-- A minimal circuit with one OR gate of no inputs (the constant `false`) appended, same output
wire, is a no instance of the last-gate problem. -/
theorem PEqualNP.MetaComplexity.L096 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.LgpNo n ⟨C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩], C.output⟩ := by
  intro n C hC
  exact PEqualNP.MetaComplexity.Helpers.LgpSanity.lgpNo_appendDead n C hC
