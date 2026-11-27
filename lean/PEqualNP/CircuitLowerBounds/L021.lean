import PEqualNP.CircuitLowerBounds.Helpers.ThresholdTop

/-- A weighted threshold of linear threshold gates of any weights that computes inner product
modulo two on `n + n` bits has total absolute top weight at least `2 ^ (n / 2) / (2 (n + 2))`
(stated squared). -/
theorem PEqualNP.CircuitLowerBounds.L021 :
    ∀ (n m : ℕ) (c : Fin m → ℤ) (t0 : ℤ) (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ), 0 < n → (∀ x y : Fin n → Bool, (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔ (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1) → (2 : ℤ) ^ n ≤ (2 * (∑ j : Fin m, |c j|) * ((n : ℤ) + 2)) ^ 2 :=
  PEqualNP.CircuitLowerBounds.Helpers.ip_top_weight_bound
