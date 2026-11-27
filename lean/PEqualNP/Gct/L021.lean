import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Pointwise

/-! L-gct-021: if `perm_m = det A` with `2n ≤ m² + 1`, then at every zero of `perm_m` with
full-rank Hessian the adjugate of `A(y)` kills the constant part `A0` on both sides. The
homogenized determinant `det(s A0 + L(z)) = s^(n-m) perm(z)` has a Hessian at `(1, y)` with kernel
`(1, -c y)`; the rank bound on the det Hessian forces a kernel vector of `Q J`, which is a
multiple of `(1 + c) A0 - c A(y)`, and L-gct-020 finishes. -/

theorem PEqualNP.Gct.L021 :
    ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ)), 3 ≤ m →
      2 * n ≤ m ^ 2 + 1 → (∀ i j, (A i j).totalDegree ≤ 1) → A.det = PEqualNP.Gct.permPoly ℂ m →
      ∀ y : Fin m × Fin m → ℂ, MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 →
      (Matrix.of fun a b : Fin m × Fin m => MvPolynomial.eval y (MvPolynomial.pderiv a
        (MvPolynomial.pderiv b (PEqualNP.Gct.permPoly ℂ m)))).rank = m ^ 2 →
      (A.map (MvPolynomial.eval y)).adjugate * A.map (fun q => q.coeff 0) = 0 ∧
        A.map (fun q => q.coeff 0) * (A.map (MvPolynomial.eval y)).adjugate = 0 :=
  fun _ _ A hm hsmall hA hdet y hy hH =>
    PEqualNP.Gct.Helpers.pointwise_mr A hm hsmall hA hdet y hy hH
