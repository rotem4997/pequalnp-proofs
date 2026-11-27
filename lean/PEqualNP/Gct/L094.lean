import PEqualNP.Gct.Helpers.LevelThree

/-- A linear space of `3 × 3` complex matrices on which the permanent of the all-ones matrix plus
the matrix stays `6` has dimension at most `3`. -/
theorem PEqualNP.Gct.L094 : ∀ L : Submodule ℂ (Fin 3 × Fin 3 → ℂ), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6) → Module.finrank ℂ L ≤ 3 :=
  PEqualNP.Gct.Helpers.LevelThree.level_three_le
