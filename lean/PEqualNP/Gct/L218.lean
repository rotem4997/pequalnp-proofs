import PEqualNP.Gct.Helpers.RiffleBelow

/-! L-gct-218: for every field, every `c > 0` and every `d`, eventually in `n` the riffle rank of
`pairId (Fin n)` is below `c n ^ 2 / (log₂ n) ^ d`. Proof: `t = Nat.clog 2 n`, the bound `3 ^ t`
of L-gct-097, and `t ^ d / (4 / 3) ^ t → 0`, `PEqualNP.Gct.Helpers.RiffleBelow.main`. -/

theorem PEqualNP.Gct.L218 : ∀ (F : Type) [Field F] (c : ℝ) (d : ℕ), 0 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ r : ℕ, (r : ℝ) < c * (n : ℝ) ^ 2 / (Real.logb 2 (n : ℝ)) ^ d ∧ PEqualNP.RiffleRank.RiffleRankLe r (PEqualNP.RiffleRank.pairId (Fin n) F) :=
  PEqualNP.Gct.Helpers.RiffleBelow.main
