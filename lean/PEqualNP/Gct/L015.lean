import PEqualNP.Defs
import PEqualNP.Gct.L021
import PEqualNP.Gct.Helpers.MRPlusOne

/-! L-gct-015: over `ℂ`, every determinantal expression of `perm_m` with `m ≥ 3` has size at least
`m²/2 + 1`, one more than Mignon and Ressayre (L-gct-009). Suppose `2n ≤ m² + 1`. At the zero of
L-gct-013 and at every nearby zero, the adjugate of `A(y)` kills the constant part `A0`
(L-gct-021). Differentiating along the tangent space of `{perm = 0}` (the argument of L-gct-018)
gives an `(m² - 1)`-dimensional space of matrices `D` with `D A0 = 0 = A0 D` and `D A(x)` in
`adj(A(x))` times matrices, while L-gct-019 bounds such spaces by `2n - 3`. -/

theorem PEqualNP.Gct.L015 :
    ∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n →
      m ^ 2 + 2 ≤ 2 * n :=
  PEqualNP.Gct.Helpers.mr_plus_one_of_pointwise PEqualNP.Gct.L021
