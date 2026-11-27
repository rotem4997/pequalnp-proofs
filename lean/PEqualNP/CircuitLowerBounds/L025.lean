import PEqualNP.CircuitLowerBounds.Helpers.WeightBound

/-- Every linear threshold function of `s` Boolean inputs with integer weights is computed
with integer weights whose absolute values sum to at most `(s + 2) ^ (s + 2)`. -/
theorem PEqualNP.CircuitLowerBounds.L025 :
    ∀ (s : ℕ) (c : Fin s → ℤ) (t0 : ℤ), ∃ (c' : Fin s → ℤ) (t0' : ℤ), (∑ j : Fin s, |c' j| ≤ ((s : ℤ) + 2) ^ (s + 2)) ∧ ∀ g : Fin s → Bool, (t0 ≤ ∑ j : Fin s, c j * (if g j = true then 1 else 0)) ↔ (t0' ≤ ∑ j : Fin s, c' j * (if g j = true then 1 else 0)) :=
  PEqualNP.CircuitLowerBounds.Helpers.threshold_small_weights
