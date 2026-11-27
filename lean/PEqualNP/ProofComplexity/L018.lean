import PEqualNP.ProofComplexity.Helpers.LinBridge

namespace PEqualNP.ProofComplexity

/-- L-pcx-018: the list-based Res(lin) of the Search definitions is simulated by Res(⊕) with at
most two lines per line. -/
theorem L018 : ∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (π : List (PEqualNP.Search.LinClause n)), PEqualNP.Search.IsResLinRefutation F π → ∃ π' : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation F π' ∧ π'.length ≤ 2 * π.length := by
  rintro n F π ⟨hπ, hempty⟩
  obtain ⟨π', hπ', hlen, hmem⟩ := Helpers.bridge_derivation hπ
  refine ⟨π', ⟨hπ', ?_⟩, hlen⟩
  simpa using hmem [] hempty

end PEqualNP.ProofComplexity
