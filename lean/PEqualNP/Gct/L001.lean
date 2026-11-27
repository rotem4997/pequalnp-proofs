import PEqualNP.Defs

/-! L-gct-001: the determinant `det_n` has a determinantal expression of size `n`: the matrix
of variables itself. -/

theorem PEqualNP.Gct.L001 :
    ∀ (R : Type) [CommRing R] (n : ℕ),
      PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.detPoly R n) n := by
  intro R _ n
  refine ⟨Matrix.mvPolynomialX (Fin n) (Fin n) R, fun i j => ?_, rfl⟩
  simpa [MvPolynomial.X] using MvPolynomial.totalDegree_monomial_le (Finsupp.single (i, j) 1) (1 : R)
