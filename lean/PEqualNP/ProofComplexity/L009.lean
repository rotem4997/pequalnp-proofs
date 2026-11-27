import PEqualNP.ProofComplexity.Helpers.Greedy

namespace PEqualNP.ProofComplexity

/-- L-pcx-009: Haken's theorem, every resolution refutation of the pigeonhole formula with
`n + 1` pigeons and `n` holes has exponentially many lines. -/
theorem L009 : ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (π : List (PEqualNP.ProofComplexity.Clause (Fin (n + 1) × Fin n))), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π → (2 : ℝ) ^ (ε * (n : ℝ)) ≤ (π.length : ℝ) := by
  refine ⟨1 / 42, by norm_num, ?_⟩
  intro n π hπ
  exact Helpers.real_bound (Helpers.two_pow_le hπ)

end PEqualNP.ProofComplexity
