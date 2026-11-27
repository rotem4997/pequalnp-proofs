import PEqualNP.Gct.Helpers.Border064

/-- L-gct-075: the border subspace reduction (the statement of L-gct-069) implies the border
target L-gct-070. -/
theorem PEqualNP.Gct.L075 :
    (∀ (m n k : ℕ) (y : Fin m × Fin m → ℂ), MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 → (∀ L : Submodule ℂ (Fin m × Fin m → ℂ), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → Module.finrank ℂ L ≤ k) → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 ≤ k + n) → (∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m) :=
  fun h069 => PEqualNP.Gct.Helpers.border064_of h069
