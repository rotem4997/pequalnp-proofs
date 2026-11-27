import PEqualNP.Gct.Helpers.LevelLow

/-- For every `n ≥ 2` there is a linear space of `n × n` complex matrices of dimension `2n - 3` on
which the permanent of the all-ones matrix plus the matrix stays `n!`. -/
theorem PEqualNP.Gct.L080 : ∀ n : ℕ, 2 ≤ n → ∃ L : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) ∧ Module.finrank ℂ L = 2 * n - 3 :=
  PEqualNP.Gct.Helpers.LevelLow.level_space_lower
