import PEqualNP.MetaComplexity.Helpers.Counting

/-- Shannon's counting bound: for every `n ≥ 5` some Boolean function on `n` inputs has no
circuit with at most `2 ^ n / (4 * n)` gates. -/
theorem PEqualNP.MetaComplexity.L002 : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ f : (Fin n → Bool) → Bool, ¬ PEqualNP.MetaComplexity.HasCircuitSize n f (2 ^ n / (4 * n)) :=
  ⟨5, PEqualNP.MetaComplexity.Helpers.counting⟩
