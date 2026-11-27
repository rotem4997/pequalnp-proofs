import PEqualNP.Library.Helpers.Erasure

/-- Deciding any language takes linear time on these machines: the input has to be erased. -/
theorem PEqualNP.Library.L021 : ∀ (t : ℕ → ℕ) (L : Language Bool),
    L ∈ PEqualNP.Library.DTIME t → ∃ d : ℕ, ∀ n : ℕ, n ≤ d * t n + 1 :=
  PEqualNP.Library.Helpers.dtime_linear
