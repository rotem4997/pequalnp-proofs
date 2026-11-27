import PEqualNP.Gct.Helpers.Corank

/-- At a zero of `det A` with nonzero gradient the matrix has corank one: kernel vectors
`u`, `v` exist and every partial derivative of `det A` there is `v ⬝ᵥ (∂A) u`. -/
theorem PEqualNP.Gct.L032 :
    ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ), MvPolynomial.eval x A.det = 0 → (∃ k, MvPolynomial.eval x (MvPolynomial.pderiv k A.det) ≠ 0) → ∃ u v : Fin n → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ Matrix.mulVec (A.map (MvPolynomial.eval x)) u = 0 ∧ Matrix.vecMul v (A.map (MvPolynomial.eval x)) = 0 ∧ ∀ k, MvPolynomial.eval x (MvPolynomial.pderiv k A.det) = dotProduct v (Matrix.mulVec ((A.map (MvPolynomial.pderiv k)).map (MvPolynomial.eval x)) u) :=
  fun n d A x h0 h1 => PEqualNP.Gct.Helpers.nondeg_zero_corank_one A x h0 h1
