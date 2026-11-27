import PEqualNP.ProofComplexity.Helpers.LinKBit

namespace PEqualNP.ProofComplexity

/-- L-pcx-061: for every `k ≥ 1`, resolution over conjunctions of at most `k` parity equations
(termwise weakening) is not polynomially bounded on the bit pigeonhole formulas. -/
theorem L061 : ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinKLine (Fin (2 ^ l + 1) × Fin l)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval ((2 ^ l + 1) * l) < π.length :=
  LinKBit.main

end PEqualNP.ProofComplexity
