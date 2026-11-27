import PEqualNP.Gct.L038
import PEqualNP.Gct.Helpers.WeightedBezout

/-- Weighted Bezout: if every monomial of `F i` has weighted degree at most `D i` for the
weights `w`, then the number of nondegenerate zeros times the product of the weights is at
most the product of the `D i`. -/
theorem PEqualNP.Gct.L039 :
    ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (w D : Fin N → ℕ), (∀ i, ∀ s ∈ (F i).support, ∑ j, w j * s j ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card * ∏ j, w j ≤ ∏ i, D i :=
  PEqualNP.Gct.Helpers.weighted_bezout_of PEqualNP.Gct.L038
