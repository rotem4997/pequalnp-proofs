import PEqualNP.Gct.Helpers.PowerSum

/-- If smooth forms have large border determinantal complexity, so do power sums: a power sum
is homogeneous and its partial derivatives vanish together only at the origin. -/
theorem PEqualNP.Gct.L029 :
    ( ∀ (d r n : ℕ) (G : MvPolynomial (Fin d) ℂ), 2 ≤ d → 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → PEqualNP.Gct.HasBorderDetExpression G n → (r - 1) * (d - 1) ≤ 11 * n ) → (∀ (r d n : ℕ), 2 ≤ d → 2 ≤ r → PEqualNP.Gct.HasBorderDetExpression (∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r) n → (r - 1) * (d - 1) ≤ 11 * n)  := by
  intro H r d n hd hr hb
  exact H d r n _ hd hr (PEqualNP.Gct.Helpers.powerSum_isHomogeneous d r)
    (PEqualNP.Gct.Helpers.powerSum_smooth d r hr) hb
