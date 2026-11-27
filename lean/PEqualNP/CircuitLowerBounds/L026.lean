import PEqualNP.CircuitLowerBounds.Helpers.ThrThrIPBound

/-- If inner product modulo two is a threshold of `k = s (2 n)` threshold gates at length
`2 n`, then `2 ^ n ≤ (2 (k + 2) ^ (k + 2) (n + 2)) ^ 2`: about `n / log n` gates are needed. -/
theorem PEqualNP.CircuitLowerBounds.L026 :
    ∀ s : ℕ → ℕ, ({x : List Bool | ((List.range (x.length / 2)).filter (fun i => x.getD i false && x.getD (i + x.length / 2) false)).length % 2 = 1} : Language Bool) ∈ PEqualNP.CircuitLowerBounds.THRTHR s → ∀ n : ℕ, 0 < n → (2 : ℤ) ^ n ≤ (2 * ((s (2 * n) : ℤ) + 2) ^ (s (2 * n) + 2) * ((n : ℤ) + 2)) ^ 2 :=
  PEqualNP.CircuitLowerBounds.Helpers.ip_thrthr_gate_bound
