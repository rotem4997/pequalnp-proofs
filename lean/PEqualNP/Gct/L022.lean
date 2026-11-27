import PEqualNP.Gct.Helpers.DetExprExists

/-- The permanent has a determinantal expression of some size, for every `m`. -/
theorem PEqualNP.Gct.L022 :
    ∀ m : ℕ, ∃ n : ℕ, PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n :=
  PEqualNP.Gct.Helpers.DetExprExists.perm_hasDetExpression
