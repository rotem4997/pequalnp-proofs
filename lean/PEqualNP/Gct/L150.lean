import PEqualNP.Gct.Helpers.GapLemma

/-- Over a field of characteristic zero, a polynomial with nonzero constant term whose coefficients
vanish on a window `[n, n + s)` with `n ≥ 1`, where `s` is its number of distinct roots in an
algebraic closure, has all coefficients from `n` on equal to zero. -/
theorem PEqualNP.Gct.L150 : ∀ (K : Type) [Field K] [CharZero K] (G : Polynomial K) (n : ℕ), G.coeff 0 ≠ 0 → 1 ≤ n → (∀ i : ℕ, n ≤ i → i < n + (G.rootSet (AlgebraicClosure K)).ncard → G.coeff i = 0) → ∀ i : ℕ, n ≤ i → G.coeff i = 0 :=
  PEqualNP.Gct.Helpers.GapLemma.main
