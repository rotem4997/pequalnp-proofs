import PEqualNP.Gct.Helpers.Rung.AllM

/-- L-gct-074: for every `R`, every border determinantal expression of `perm_m` over the complex
numbers has size at least `R m^2` for all large `m`. The construction of L-gct-057 with a free
number of top rows reaches every large size. -/
theorem PEqualNP.Gct.L074 :
    ∀ R : ℕ, ∃ m0 : ℕ, ∀ m n : ℕ, m0 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → R * m ^ 2 ≤ n :=
  PEqualNP.Gct.Rung.AllM.allLarge
