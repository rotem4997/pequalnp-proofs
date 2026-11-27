import PEqualNP.Gct.Helpers.STwoRow

/-- A linear space of pairs of complex rows of length `q ≥ 2` on which the total entry sum and the
off-diagonal row product both vanish has dimension at most `q - 1`. -/
theorem PEqualNP.Gct.L101 : ∀ (q : ℕ) (L : Submodule ℂ (Fin 2 × Fin q → ℂ)), 2 ≤ q → (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) → Module.finrank ℂ L + 1 ≤ q :=
  PEqualNP.Gct.Helpers.STwoRow.main
