import PEqualNP.CircuitLowerBounds.Helpers.Staircase

/-- One linear threshold gate with arbitrary weights, its inputs split in two halves, has
correlation at most `(n + 1) * 2 ^ (-n / 2)` with inner product modulo two. -/
theorem PEqualNP.CircuitLowerBounds.L020 :
    ∀ (n : ℕ) (a b : (Fin n → Bool) → ℤ) (t : ℤ), (∑ x : Fin n → Bool, ∑ y : Fin n → Bool, (if t ≤ a x + b y then (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card else 0)) ^ 2 ≤ ((n : ℤ) + 1) ^ 2 * 2 ^ (3 * n) :=
  PEqualNP.CircuitLowerBounds.Helpers.threshold_ip_bound
