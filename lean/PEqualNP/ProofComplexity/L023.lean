import PEqualNP.ProofComplexity.Helpers.SizeBound

namespace PEqualNP.ProofComplexity

/-- L-pcx-023: the baseline size bound for bit pigeonhole in Res(⊕): every axiom is used. -/
theorem L023 : ∀ (l : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l))), 0 < l → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → 2 ^ l * (2 ^ l + 1).choose 2 + 1 ≤ π.length :=
  Helpers.bphp_size

end PEqualNP.ProofComplexity
