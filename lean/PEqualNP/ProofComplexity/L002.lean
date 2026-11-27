import PEqualNP.ProofComplexity.Helpers.Resolution

namespace PEqualNP.ProofComplexity

/-- L-pcx-002: resolution is sound. -/
theorem L002 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.Clause V)), PEqualNP.ProofComplexity.IsRefutation F π → ¬ PEqualNP.ProofComplexity.Satisfiable F := by
  rintro V _ F π ⟨hπ, hempty⟩ ⟨a, ha⟩
  obtain ⟨l, hl, -⟩ := Helpers.derivation_sound a hπ ha ∅ hempty
  simp at hl

end PEqualNP.ProofComplexity
