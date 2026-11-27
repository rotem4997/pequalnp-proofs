import PEqualNP.ProofComplexity.L004
import PEqualNP.ProofComplexity.L006

/-- A resolution refutation of the pigeonhole formula exists at every `n`, below an exponential length. -/
theorem PEqualNP.ProofComplexity.L030 : ∀ n : ℕ, ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin (n + 1) × Fin n)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π ∧ π.length ≤ 2 ^ ((n + 1) * n + 1) - 1 := by
  intro n
  obtain ⟨π, h1, h2⟩ := PEqualNP.ProofComplexity.L006 (Fin (n + 1) × Fin n) _
    (PEqualNP.ProofComplexity.L004 (n + 1) n (Nat.lt_succ_self n))
  refine ⟨π, h1, ?_⟩
  simpa [Fintype.card_prod] using h2
