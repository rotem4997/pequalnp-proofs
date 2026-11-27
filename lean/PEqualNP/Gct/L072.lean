import PEqualNP.Gct.L070

/-- L-gct-072: the same statement as L-gct-070, recorded twice; proved by it. -/
theorem PEqualNP.Gct.L072 :
    ∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m :=
  PEqualNP.Gct.L070
