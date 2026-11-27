import PEqualNP.ProofComplexity.Helpers.ChainA

namespace PEqualNP.ProofComplexity

/-- L-pcx-031: the bit decoder maps polynomial calculus consequences of bit pigeonhole to
consequences of functional pigeonhole in the same degree. -/
theorem L031 : ∀ (m l B : ℕ) (q : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l → PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) B q → PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.funPHPSystem m (2 ^ l)) B (PEqualNP.ProofComplexity.bitDecoder m l q) :=
  Helpers.chainA

end PEqualNP.ProofComplexity
