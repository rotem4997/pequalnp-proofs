import PEqualNP.ProofComplexity.Helpers.ChainA
import PEqualNP.ProofComplexity.Helpers.ChainB

namespace PEqualNP.ProofComplexity

/-- L-pcx-032: no nonzero row-linear polynomial is a low-degree polynomial calculus
consequence of bit pigeonhole. -/
theorem L032 : ∀ (m l k B : ℕ) (f : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l → 1 ≤ k → k ≤ B → 4 * (k - 1) < 2 ^ l → 2 * B + 2 * k ≤ 2 ^ l + 1 → f ≠ 0 → PEqualNP.ProofComplexity.IsRowLinear m l k f → ¬ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) B f :=
  Helpers.chainB_of_decoder Helpers.chainA

end PEqualNP.ProofComplexity
