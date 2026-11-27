import PEqualNP.Defs

/-- SIZE is monotone in the size bound: the same circuits witness the larger bound. -/
theorem PEqualNP.CircuitLowerBounds.L001 : ∀ s t : ℕ → ℕ, (∀ n, s n ≤ t n) →
    PEqualNP.CircuitLowerBounds.SIZE s ⊆ PEqualNP.CircuitLowerBounds.SIZE t := by
  intro s t hst L hL n
  obtain ⟨C, hg, hs, hd⟩ := hL n
  exact ⟨C, hg, le_trans hs (hst n), hd⟩
