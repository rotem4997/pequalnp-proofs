import PEqualNP.MetaComplexity.Helpers.Hierarchy

/-- Circuit size hierarchy: for `n ≥ 5` and `n ≤ s ≤ 2 ^ n / (4 * n)` some Boolean function on
`n` inputs has a circuit with `5 * s` gates and none with `s` gates. -/
theorem PEqualNP.MetaComplexity.L004 : ∃ c n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : ℕ, n ≤ s → s ≤ 2 ^ n / (4 * n) → ∃ f : (Fin n → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize n f (c * s) ∧ ¬ PEqualNP.MetaComplexity.HasCircuitSize n f s :=
  ⟨5, 5, fun n hn s hs hs' => PEqualNP.MetaComplexity.Helpers.hierarchy n hn s hs hs'⟩
