import PEqualNP.ProofComplexity.Helpers.BitPHP

namespace PEqualNP.ProofComplexity

/-- L-pcx-020: every Res(⊕) refutation of the bit pigeonhole formula has a line of rank at
least a quarter of the number of holes. -/
theorem L020 : ∀ (m l : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin l))), 0 < l → 2 ^ l < m → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP m l) π → ∃ C ∈ π, 2 ^ l ≤ 4 * PEqualNP.ProofComplexity.linRank C :=
  Helpers.bphp_rank

end PEqualNP.ProofComplexity
