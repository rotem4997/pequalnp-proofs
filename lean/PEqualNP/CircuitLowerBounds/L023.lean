import PEqualNP.CircuitLowerBounds.Helpers.SignRank

/-- Forster's sign-rank bound for inner product modulo two: if a threshold of `m` threshold gates,
each depending on the first input through an integer-valued function with at most `V` values,
computes inner product modulo two on `n + n` bits, then `2 ^ n ≤ (m V + 1) ^ 2`. -/
theorem PEqualNP.CircuitLowerBounds.L023 :
    ∀ (n m V : ℕ) (c : Fin m → ℤ) (t0 : ℤ) (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ), (∀ j : Fin m, (Finset.univ.image (a j)).card ≤ V) → (∀ x y : Fin n → Bool, (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔ (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1) → 2 ^ n ≤ (m * V + 1) ^ 2 :=
  fun n m V c t0 a b t hV h =>
    PEqualNP.CircuitLowerBounds.Helpers.signrank_ip n m V c t0 a b t hV h
