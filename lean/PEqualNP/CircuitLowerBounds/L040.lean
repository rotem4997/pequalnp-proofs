import PEqualNP.CircuitLowerBounds.L039

/-- SAT has no fan-in two circuits of size at most `0.99 n + c`: no size bound `s` with
`100 * s n ≤ 99 * n + c` for all `n` puts SAT in `SIZE s`. -/
theorem PEqualNP.CircuitLowerBounds.L040 :
    ¬ ∃ (s : ℕ → ℕ) (c : ℕ), (∀ n : ℕ, 100 * s n ≤ 99 * n + c) ∧ PEqualNP.Search.SAT ∈ PEqualNP.CircuitLowerBounds.SIZE s :=
  PEqualNP.CircuitLowerBounds.Helpers.SatSlice.s3_of PEqualNP.CircuitLowerBounds.L039
