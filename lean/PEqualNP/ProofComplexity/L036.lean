import PEqualNP.ProofComplexity.L032
import PEqualNP.ProofComplexity.L033
import PEqualNP.ProofComplexity.L034
import PEqualNP.ProofComplexity.L035

namespace PEqualNP.ProofComplexity

/-- L-pcx-036: dag-like Res(⊕) refutations of bit pigeonhole are exponentially long. -/
theorem L036 : ∀ (l : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l))), 32 ≤ l → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) < (π.length : ℝ) :=
  L035 L032 L033 L034

end PEqualNP.ProofComplexity
