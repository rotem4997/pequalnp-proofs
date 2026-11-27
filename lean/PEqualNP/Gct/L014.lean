import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetExprHessian

/-! L-gct-014: if `p` is the determinant of an `n × n` matrix of affine forms over `ℂ`, its
Hessian has rank at most `2n` at every zero of `p` (Mignon and Ressayre 2004): the Hessian
chain rule for an affine substitution, then L-gct-012's bound at the singular matrix `A(y)`. -/

theorem PEqualNP.Gct.L014 :
    ∀ (k n : ℕ) (p : MvPolynomial (Fin k) ℂ) (y : Fin k → ℂ),
      PEqualNP.Gct.HasDetExpression p n → MvPolynomial.eval y p = 0 →
      (Matrix.of fun a b : Fin k => MvPolynomial.eval y (MvPolynomial.pderiv a
        (MvPolynomial.pderiv b p))).rank ≤ 2 * n :=
  fun _ _ p y hp h0 => PEqualNP.Gct.Helpers.rank_hess_detExpr p y hp h0
