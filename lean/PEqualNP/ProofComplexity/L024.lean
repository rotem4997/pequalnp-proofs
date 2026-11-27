import PEqualNP.ProofComplexity.Helpers.PCToolkit

namespace PEqualNP.ProofComplexity

/-- L-pcx-024: multiplying a derived line by any polynomial stays within the expected degree. -/
theorem L024 : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (B : ℕ) (g q : MvPolynomial σ (ZMod 2)), PEqualNP.ProofComplexity.PCDerivable F B g → PEqualNP.ProofComplexity.PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  intro σ F B g q hg; exact Helpers.pcDerivable_mul_left hg q

end PEqualNP.ProofComplexity
