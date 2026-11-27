import PEqualNP.Defs

/-- DTIME is monotone in the time bound. -/
theorem PEqualNP.Library.L002 : ∀ t t' : ℕ → ℕ, (∀ n : ℕ, t n ≤ t' n) →
    PEqualNP.Library.DTIME t ⊆ PEqualNP.Library.DTIME t' := by
  rintro t t' h L ⟨f, hf, c, hc⟩
  exact ⟨f, hf, c, fun n => (hc n).trans (h n)⟩
