import PEqualNP.Gct.L069

/-- L-gct-071: the same statement as L-gct-069, recorded twice; proved by it. -/
theorem PEqualNP.Gct.L071 :
    ∀ (m n k : ℕ) (y : Fin m × Fin m → ℂ), MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 → (∀ L : Submodule ℂ (Fin m × Fin m → ℂ), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → Module.finrank ℂ L ≤ k) → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 ≤ k + n :=
  PEqualNP.Gct.L069
