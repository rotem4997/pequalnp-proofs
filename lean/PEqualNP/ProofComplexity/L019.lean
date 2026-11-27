import PEqualNP.ProofComplexity.Helpers.ParityLine

namespace PEqualNP.ProofComplexity

/-- L-pcx-019: the parity line of a set `S` of pigeons is implied by seating `S`, and every
set of pigeons whose seating implies it contains `S`. -/
theorem L019 : ∀ (n : ℕ) (S : Finset (Fin (n + 1))), (∀ e : Fin (n + 1) ≃ Option (Fin n), (∀ i ∈ S, e i ≠ none) → PEqualNP.ProofComplexity.LinClauseSat (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2)) {(S ×ˢ (Finset.univ : Finset (Fin n)), decide (S.card % 2 = 1))}) ∧ ∀ T : Finset (Fin (n + 1)), (∀ e : Fin (n + 1) ≃ Option (Fin n), (∀ i ∈ T, e i ≠ none) → PEqualNP.ProofComplexity.LinClauseSat (fun p : Fin (n + 1) × Fin n => decide (e p.1 = some p.2)) {(S ×ˢ (Finset.univ : Finset (Fin n)), decide (S.card % 2 = 1))}) → S ⊆ T := by
  intro n S
  exact ⟨Helpers.parity_line_sat S, fun T hT => Helpers.parity_line_min S T hT⟩

end PEqualNP.ProofComplexity
