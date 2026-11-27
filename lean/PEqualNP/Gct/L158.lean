import PEqualNP.Gct.Helpers.RealLevel

/-- A real linear space of `p × q` arrays, `p, q ≥ 1`, on which the total sum and the off-row,
off-column product sum both vanish has dimension at most `p + q - 2`. -/
theorem PEqualNP.Gct.L158 : ∀ (p q : ℕ) (L : Submodule ℝ (Fin p × Fin q → ℝ)), 1 ≤ p → 1 ≤ q → (∀ t ∈ L, (∑ i, ∑ j, t (i, j)) = 0 ∧ (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else t (i, j) * t (k, l)) = 0) → Module.finrank ℝ L + 2 ≤ p + q :=
  PEqualNP.Gct.Helpers.RealLevel.main
