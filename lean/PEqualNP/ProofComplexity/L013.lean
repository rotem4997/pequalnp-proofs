import PEqualNP.ProofComplexity.Helpers.LinSim

namespace PEqualNP.ProofComplexity

/-- L-pcx-013: Res(⊕) simulates resolution line by line. -/
theorem L013 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.Clause V)), PEqualNP.ProofComplexity.IsRefutation F π → ∃ π' : List (PEqualNP.ProofComplexity.LinClause V), PEqualNP.ProofComplexity.IsLinRefutation F π' ∧ π'.length = π.length := by
  rintro V _ F π ⟨hπ, hempty⟩
  refine ⟨π.map linOfClause, ⟨Helpers.lin_of_derivation hπ, ?_⟩, List.length_map _⟩
  exact List.mem_map.mpr ⟨∅, hempty, by simp [linOfClause]⟩

end PEqualNP.ProofComplexity
