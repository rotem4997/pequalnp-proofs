import PEqualNP.Gct.Helpers.BorderSubst

/-- L-gct-023: a border determinantal expression of size `n` is preserved by substituting
polynomials of total degree at most one for the variables. -/
theorem PEqualNP.Gct.L023 :
    ∀ (σ τ : Type) [Finite σ] (p : MvPolynomial σ ℂ) (g : σ → MvPolynomial τ ℂ) (n : ℕ),
      (∀ i, (g i).totalDegree ≤ 1) → PEqualNP.Gct.HasBorderDetExpression p n →
        PEqualNP.Gct.HasBorderDetExpression (MvPolynomial.bind₁ g p) n :=
  PEqualNP.Gct.Helpers.hasBorderDetExpression_bind₁
