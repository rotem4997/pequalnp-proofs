import PEqualNP.Gct.L040
import PEqualNP.Gct.L046

/-- L-gct-045: every border determinantal expression of the power sum `x_1^r + .. + x_d^r`
has size `n` with `(r - 1) * (d - 1) ≤ 11 * n`. The assembly L-gct-046 applied to half (b),
L-gct-040. -/
theorem PEqualNP.Gct.L045 :
    ∀ (d r n : ℕ), 2 ≤ d → 2 ≤ r → PEqualNP.Gct.HasBorderDetExpression (∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r) n → (r - 1) * (d - 1) ≤ 11 * n :=
  PEqualNP.Gct.L046 PEqualNP.Gct.L040
