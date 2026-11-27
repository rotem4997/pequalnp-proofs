import PEqualNP.Gct.L069
import PEqualNP.Gct.L075

/-- L-gct-070: every border determinantal expression of `perm_m` over `ℂ`, `m ≥ 3`, has size
`n` with `3 n ≥ 2 m ^ 2 - 10 m + 11`. The assembly L-gct-075 applied to the border subspace
reduction L-gct-069. -/
theorem PEqualNP.Gct.L070 :
    ∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m :=
  PEqualNP.Gct.L075 PEqualNP.Gct.L069
