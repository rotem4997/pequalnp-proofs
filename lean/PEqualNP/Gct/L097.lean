import PEqualNP.Gct.Helpers.Riffle

/-! L-gct-097: if `n ≤ 2 ^ t` then `pairId (Fin n)` has riffle rank at most `3 ^ t`. Proof:
induction on `t` with L-gct-095 and L-gct-096 for `Fin (2 ^ t)`, then restriction along
`Fin.castLE`, `PEqualNP.Gct.Riffle.rank_fin_le_pow`. -/

theorem PEqualNP.Gct.L097 : ∀ (F : Type) [Field F] (n t : ℕ), n ≤ 2 ^ t → PEqualNP.RiffleRank.RiffleRankLe (3 ^ t) (PEqualNP.RiffleRank.pairId (Fin n) F) :=
  fun _ _ _ _ h => PEqualNP.Gct.Riffle.rank_fin_le_pow h
