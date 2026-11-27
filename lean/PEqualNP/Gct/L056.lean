import PEqualNP.Gct.Helpers.Rung.AssemblyBound
import PEqualNP.Gct.L023
import PEqualNP.Gct.L024
import PEqualNP.Gct.L057

/-- L-gct-056: the border determinantal complexity of the permanent is not `O(m^2)`. For every
`R` there are arbitrarily large `m` such that every border determinantal expression of
`perm_m` over the complex numbers has size at least `R m^2`. From the smooth restriction
(L-gct-057), the smooth-form bound (L-gct-024) and closure under affine substitutions
(L-gct-023). -/
theorem PEqualNP.Gct.L056 :
    ∀ R m0 : ℕ, ∃ m : ℕ, m0 ≤ m ∧ 1 ≤ m ∧ ∀ n : ℕ, PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → R * m ^ 2 ≤ n :=
  PEqualNP.Gct.Rung.assemblyBound PEqualNP.Gct.L057 PEqualNP.Gct.L024 PEqualNP.Gct.L023
