import PEqualNP.CircuitLowerBounds.Helpers.Lindsey

/-- Lindsey's lemma: the sign matrix of inner product modulo two on `n + n` bits sums, over any
rectangle `A × B`, to at most `sqrt (|A| |B| 2 ^ n)` in absolute value (stated squared). -/
theorem PEqualNP.CircuitLowerBounds.L016 :
    ∀ (n : ℕ) (A B : Finset (Fin n → Bool)), (∑ x ∈ A, ∑ y ∈ B, (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card) ^ 2 ≤ (A.card : ℤ) * (B.card : ℤ) * 2 ^ n :=
  fun n A B => PEqualNP.CircuitLowerBounds.Helpers.lindsey n A B
