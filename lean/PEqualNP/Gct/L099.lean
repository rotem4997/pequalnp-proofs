import PEqualNP.Gct.Helpers.SupportCriterion

/-- Support expansion: the permanent of the all-ones matrix plus a combination of rank-one
matrices, as a sum over the monomials of the two product polynomials. -/
theorem PEqualNP.Gct.L099 : ∀ (n d : ℕ) (u w : Fin d → Fin n → ℂ) (c : Fin d → ℂ), MvPolynomial.eval (fun p : Fin n × Fin n => 1 + ∑ i, c i * u i p.1 * w i p.2) (PEqualNP.Gct.permPoly ℂ n) = ∑ α ∈ (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (w i j) * MvPolynomial.X i) : MvPolynomial (Fin d) ℂ).support, ((n - ∑ i, α i).factorial : ℂ) * (∏ i, ((α i).factorial : ℂ)) * (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (u i j) * MvPolynomial.X i) : MvPolynomial (Fin d) ℂ).coeff α * (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (w i j) * MvPolynomial.X i) : MvPolynomial (Fin d) ℂ).coeff α * ∏ i, c i ^ α i :=
  PEqualNP.Gct.Helpers.Support.support_criterion
