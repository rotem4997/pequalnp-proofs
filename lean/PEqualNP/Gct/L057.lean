import PEqualNP.Gct.Helpers.Rung.Chain
import PEqualNP.Gct.Helpers.Rung.BlockPerm

/-- L-gct-057: the permanent restricts to smooth forms with `(r - 1)(d - 1) / m^2` unbounded.
For every `R` there are arbitrarily large `m` such that an affine substitution turns `perm_m`
into a complex form of degree `r` in `d` variables whose partial derivatives vanish together
only at the origin, with `(r - 1)(d - 1)` at least `R m^2`. The form is a linear section of a
block sum of sums of `r × r` subpermanents. -/
theorem PEqualNP.Gct.L057 :
    ∀ R m0 : ℕ, ∃ (m r d : ℕ) (G : MvPolynomial (Fin d) ℂ) (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ), m0 ≤ m ∧ 1 ≤ m ∧ 2 ≤ r ∧ 2 ≤ d ∧ R * m ^ 2 ≤ (r - 1) * (d - 1) ∧ G.IsHomogeneous r ∧ (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) ∧ (∀ i, (g i).totalDegree ≤ 1) ∧ MvPolynomial.bind₁ g (PEqualNP.Gct.permPoly ℂ m) = G :=
  PEqualNP.Gct.Rung.stmt057_of_blockPerm PEqualNP.Gct.Rung.blockPerm
