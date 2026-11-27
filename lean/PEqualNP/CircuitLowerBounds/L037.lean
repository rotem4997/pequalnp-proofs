import PEqualNP.CircuitLowerBounds.Helpers.SatSlice

/-- Every input bit of the SAT slice at length `6 * q` (for `q ≥ 2`) matters: for each
position there is a string whose membership in SAT changes when that bit is flipped. -/
theorem PEqualNP.CircuitLowerBounds.L037 :
    ∀ q : ℕ, 2 ≤ q → ∀ i : Fin (6 * q), ∃ x : Fin (6 * q) → Bool, (List.ofFn (Function.update x i (!x i)) ∈ PEqualNP.Search.SAT ↔ List.ofFn x ∉ PEqualNP.Search.SAT) :=
  PEqualNP.CircuitLowerBounds.Helpers.SatSlice.s1
