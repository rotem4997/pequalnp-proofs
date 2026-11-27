import PEqualNP.ProofComplexity.Helpers.PhpFinal
import PEqualNP.ProofComplexity.L046
import PEqualNP.ProofComplexity.L047

namespace PEqualNP.ProofComplexity

/-- L-pcx-017: dag-like Res(⊕) refutations of the pigeonhole formula are not polynomially
bounded. -/
theorem L017 : ∀ p : Polynomial ℕ, ∃ n : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin (n + 1) × Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π → p.eval n < π.length :=
  PhpFinal.php_not_poly L046 L047

end PEqualNP.ProofComplexity
