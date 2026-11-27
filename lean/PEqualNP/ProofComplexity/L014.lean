import PEqualNP.ProofComplexity.Helpers.Lin

namespace PEqualNP.ProofComplexity

/-- L-pcx-014: every Res(⊕) refutation of the pigeonhole formula has a line of medium
critical complexity. -/
theorem L014 : ∀ (n : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin (n + 1) × Fin n))), 1 ≤ n → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π → ∃ C ∈ π, ∃ S : Finset (Fin (n + 1)), n + 1 < 3 * S.card ∧ 3 * S.card ≤ 2 * (n + 1) ∧ (∀ e : Fin (n + 1) ≃ Option (Fin n), (∀ i ∈ S, e i ≠ none) → PEqualNP.ProofComplexity.LinClauseSat (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2)) C) ∧ ∀ T : Finset (Fin (n + 1)), (∀ e : Fin (n + 1) ≃ Option (Fin n), (∀ i ∈ T, e i ≠ none) → PEqualNP.ProofComplexity.LinClauseSat (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2)) C) → S.card ≤ T.card := by
  intro n π hn hπ
  obtain ⟨C, hC, S, h1, h2, hS, hmin⟩ := Helpers.exists_lmedium hn hπ
  exact ⟨C, hC, S, h1, h2, hS, hmin⟩

end PEqualNP.ProofComplexity
