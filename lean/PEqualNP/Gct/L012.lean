import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetHessian

/-! L-gct-012: at every singular complex matrix the Hessian of `det_n` has rank at most `2n`
(Mignon and Ressayre 2004). Reduce to a diagonal matrix by transvections, which preserve the
determinant, and read the column space of the Hessian at a diagonal matrix with a zero. -/

theorem PEqualNP.Gct.L012 :
    ∀ (n : ℕ) (x : Fin n × Fin n → ℂ), MvPolynomial.eval x (PEqualNP.Gct.detPoly ℂ n) = 0 →
      (Matrix.of fun a b : Fin n × Fin n => MvPolynomial.eval x (MvPolynomial.pderiv a
        (MvPolynomial.pderiv b (PEqualNP.Gct.detPoly ℂ n)))).rank ≤ 2 * n :=
  fun _ x h => PEqualNP.Gct.Helpers.rank_hess_det_singular x h
