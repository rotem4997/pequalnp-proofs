import PEqualNP.ProofComplexity.Helpers.ChainC

namespace PEqualNP.ProofComplexity

/-- L-pcx-033: a Res(⊕) refutation of bit pigeonhole gives a low-degree polynomial calculus
refutation of the bit system extended by blocks of extension variables. -/
theorem L033 : ∀ (m l h : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin l))), 1 ≤ h → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP m l) π → ∃ (M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)), M ≤ 3 * π.length + m.choose 2 ∧ (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.blockSystem (PEqualNP.ProofComplexity.bitPHPSystem m l) h M W g) (max (2 * h + l) (4 * h + 1)) :=
  Helpers.chainC

end PEqualNP.ProofComplexity
