import PEqualNP.MetaComplexity.Helpers.CoverCircB

/-- The root cover circuit is monotone of fan-in two, and every gate reads exactly two wires. -/
theorem PEqualNP.MetaComplexity.L402 : ∀ (n : ℕ) (own : List (ℕ × List ℕ)), PEqualNP.MetaComplexity.Monotone2 (PEqualNP.MetaComplexity.coverCircuitB n own) ∧ ∀ g ∈ (PEqualNP.MetaComplexity.coverCircuitB n own).gates, g.inputs.length = 2 :=
  fun n own => PEqualNP.MetaComplexity.Helpers.CoverCircB.circuit_shape n own
