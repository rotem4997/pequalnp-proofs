import PEqualNP.ProofComplexity.L036
import PEqualNP.ProofComplexity.L037

namespace PEqualNP.ProofComplexity

/-- L-pcx-022: Res(⊕) refutations of bit pigeonhole are not polynomially bounded. -/
theorem L022 : ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval (2 ^ l) < π.length :=
  L037 L036

end PEqualNP.ProofComplexity
