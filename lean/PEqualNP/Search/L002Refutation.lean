import PEqualNP.Search.Helpers.Tseitin
import PEqualNP.Search.Helpers.SplitGrid

/-- Width-k resolution saturation does not decide 3-SAT, for any fixed k: Tseitin formulas on
split grids are unsatisfiable 3-CNFs with no resolution refutation of width at most k. -/
theorem PEqualNP.Search.L002Refutation : ¬ (∃ k : ℕ, ∀ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) → ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) → ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)), PEqualNP.ProofComplexity.IsRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π ∧ ∀ C ∈ π, C.card ≤ k) := by
  rintro ⟨k, hk⟩
  obtain ⟨m, n, G, hm, hdeg, hbig⟩ := PEqualNP.Search.Helpers.splitGrid_exists (k + 1)
  obtain ⟨v0, h0⟩ := hbig ∅ (by simp)
  obtain ⟨D⟩ := PEqualNP.Search.Helpers.tseitin_duplicator G v0 k hm hbig h0
  obtain ⟨π, hπ, hw⟩ := hk n (PEqualNP.Search.Helpers.tseitin G v0)
    (PEqualNP.Search.Helpers.tseitin_width G v0 hdeg) (PEqualNP.Search.Helpers.tseitin_unsat G v0)
  exact PEqualNP.Search.Helpers.duplicator_no_narrow_refutation D π hπ hw
