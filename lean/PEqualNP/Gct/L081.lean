import PEqualNP.Gct.Helpers.BadZero

/-- A zero of the permanent of size `k + 2` with a linear space of dimension `(k + 1) k / 2`
through it inside the permanent hypersurface. -/
theorem PEqualNP.Gct.L081 : ∀ k : ℕ, ∃ (y : Fin (k + 2) × Fin (k + 2) → ℂ) (L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ)), MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0 ∧ (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0) ∧ 2 * Module.finrank ℂ L = (k + 1) * k :=
  PEqualNP.Gct.Helpers.BadZero.bad_zero
