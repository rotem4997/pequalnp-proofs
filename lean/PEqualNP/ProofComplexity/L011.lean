import PEqualNP.ProofComplexity.Helpers.Matching

namespace PEqualNP.ProofComplexity

/-- L-pcx-011: the wide clause lemma for the pigeonhole formula. -/
theorem L011 : ∀ (n : ℕ) (π : List (PEqualNP.ProofComplexity.Clause (Fin (n + 1) × Fin n))), 1 ≤ n → PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π → ∃ C ∈ π, 2 * (n + 1) ^ 2 ≤ 9 * (Finset.univ.filter (fun p : Fin (n + 1) × Fin n => (p, true) ∈ C ∨ ∃ i : Fin (n + 1), i ≠ p.1 ∧ ((i, p.2), false) ∈ C)).card := by
  intro n π hn hπ
  have hcard : (Helpers.freeP (∅ : Finset (Helpers.PVar n))).card = n + 1 := by
    rw [Helpers.freeP_empty, Finset.card_univ, Fintype.card_fin]
  obtain ⟨C, hC, -, hwide⟩ := Helpers.exists_wide Helpers.valid_empty (by omega) hπ
  refine ⟨C, hC, ?_⟩
  rw [hcard] at hwide
  refine hwide.trans (Nat.mul_le_mul_left 9 (Finset.card_le_card ?_))
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Helpers.mem_mono.mp hp'⟩

end PEqualNP.ProofComplexity
