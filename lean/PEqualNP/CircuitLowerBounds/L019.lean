import PEqualNP.CircuitLowerBounds.Helpers.Discriminator

/-- A threshold of `m` comparison gates `t j ≤ a j x + b j y`, each with `a j` taking at most
`V` values, that computes inner product modulo two on `n + n` bits has total top weight `C`
with `2 ^ n ≤ (2 C (V + 1)) ^ 2`. -/
theorem PEqualNP.CircuitLowerBounds.L019 : ∀ (n m V : ℕ) (c : Fin m → ℤ) (t0 : ℤ) (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ), 0 < n → (∀ j : Fin m, (Finset.univ.image (a j)).card ≤ V) → (∀ x y : Fin n → Bool, (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔ (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1) → (2 : ℤ) ^ n ≤ (2 * (∑ j : Fin m, |c j|) * ((V : ℤ) + 1)) ^ 2 :=
  PEqualNP.CircuitLowerBounds.Helpers.ip_rect_bound
