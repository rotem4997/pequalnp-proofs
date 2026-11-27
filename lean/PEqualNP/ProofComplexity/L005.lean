import PEqualNP.ProofComplexity.Helpers.Completeness

namespace PEqualNP.ProofComplexity

/-- L-pcx-005: resolution is complete. -/
theorem L005 : ∀ (V : Type) [DecidableEq V] [Fintype V] (F : Set (PEqualNP.ProofComplexity.Clause V)), ¬ PEqualNP.ProofComplexity.Satisfiable F → ∃ π : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F π := by
  intro V _ _ F h
  obtain ⟨π, hπ, -⟩ := Helpers.completeness F h
  exact ⟨π, hπ⟩

end PEqualNP.ProofComplexity
