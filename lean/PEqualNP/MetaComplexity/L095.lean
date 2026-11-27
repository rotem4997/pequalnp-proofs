import PEqualNP.MetaComplexity.Helpers.LgpSanity

/-- On every number of inputs, both sides of the last-gate problem are inhabited: the empty
circuit is minimal, and with a dead gate appended it is one gate above the minimum. -/
theorem PEqualNP.MetaComplexity.L095 : ∀ n : ℕ, (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.LgpYes n C) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.LgpNo n C) := by
  intro n
  exact ⟨⟨⟨[], 0⟩, PEqualNP.MetaComplexity.Helpers.LgpSanity.minimal_empty n 0⟩,
    ⟨_, PEqualNP.MetaComplexity.Helpers.LgpSanity.lgpNo_appendDead n ⟨[], 0⟩ 
      (PEqualNP.MetaComplexity.Helpers.LgpSanity.minimal_empty n 0)⟩⟩
