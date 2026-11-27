import PEqualNP.Gct.Helpers.CubicAssembly

/-- L-gct-027: closure of border determinantal expressions under affine substitutions, a
lower bound for smooth forms, and a family of smooth forms obtained from permanents by affine
substitutions together give a cubic lower bound on the border determinantal complexity of the
permanent. -/
theorem PEqualNP.Gct.L027 :
    (∀ (σ τ : Type) [Finite σ] (p : MvPolynomial σ ℂ) (g : σ → MvPolynomial τ ℂ) (n : ℕ),
      (∀ i, (g i).totalDegree ≤ 1) → PEqualNP.Gct.HasBorderDetExpression p n →
        PEqualNP.Gct.HasBorderDetExpression (MvPolynomial.bind₁ g p) n) →
    (∀ (d r n : ℕ) (G : MvPolynomial (Fin d) ℂ), 2 ≤ d → 2 ≤ r → G.IsHomogeneous r →
      (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) →
        PEqualNP.Gct.HasBorderDetExpression G n → (r - 1) * (d - 1) ≤ 11 * n) →
    (∀ k : ℕ, 128 ≤ k → ∃ (r d : ℕ) (G : MvPolynomial (Fin d) ℂ)
      (g : Fin (11 * k) × Fin (11 * k) → MvPolynomial (Fin d) ℂ),
        k ≤ 3 * r ∧ k ^ 2 ≤ 100 * d + 100 ∧ G.IsHomogeneous r ∧
        (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) ∧
        (∀ i, (g i).totalDegree ≤ 1) ∧
        MvPolynomial.bind₁ g (PEqualNP.Gct.permPoly ℂ (11 * k)) = G) →
    (∃ (c m0 : ℕ), 0 < c ∧ ∀ m n : ℕ, m0 ≤ m →
      PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 3 ≤ c * n) :=
  PEqualNP.Gct.Helpers.cubic_assembly
