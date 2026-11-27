import PEqualNP.Gct.L034
import PEqualNP.Gct.L040
import PEqualNP.Gct.L041
import PEqualNP.Gct.Helpers.SmoothAssembly

/-- A smooth form of degree `r` in `d` variables with a border determinantal expression of
size `n` satisfies `(r - 1) * (d - 1) ≤ 11 * n`. -/
theorem PEqualNP.Gct.L024 :
    ∀ (d r n : ℕ) (G : MvPolynomial (Fin d) ℂ), 2 ≤ d → 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → PEqualNP.Gct.HasBorderDetExpression G n → (r - 1) * (d - 1) ≤ 11 * n :=
  PEqualNP.Gct.Helpers.smooth_bound_of PEqualNP.Gct.L034 PEqualNP.Gct.L040 PEqualNP.Gct.L041
