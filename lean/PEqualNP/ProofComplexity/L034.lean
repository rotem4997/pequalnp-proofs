import PEqualNP.ProofComplexity.Helpers.ChainD

namespace PEqualNP.ProofComplexity

/-- L-pcx-034: removing the blocks from a polynomial calculus refutation leaves a nonzero row-linear consequence of bit pigeonhole. -/
theorem L034 : ∀ (m l k D M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)), 0 < m → 1 ≤ l → 1 ≤ k → 1 ≤ M → k ≤ m → (m : ℝ) * Real.log (4 * (M : ℝ)) ≤ (k : ℝ) ^ 2 → 2 * (3 * l) + 1 ≤ D → (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.blockSystem (PEqualNP.ProofComplexity.bitPHPSystem m l) (3 * l) M W g) D → ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ PEqualNP.ProofComplexity.IsRowLinear m l k f ∧ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) (k * (D + 1)) f :=
  Helpers.chainD

end PEqualNP.ProofComplexity
