import PEqualNP.Gct.Helpers.Riffle

/-! L-gct-096: riffle rank bounds for `pairId` multiply under products of index types. Proof:
the products of the terms, indexed by `Fin r × Fin s`, `PEqualNP.Gct.Riffle.rank_prod`. -/

theorem PEqualNP.Gct.L096 : ∀ (F : Type) [Field F] (X Y : Type) [DecidableEq X] [DecidableEq Y] (r s : ℕ), PEqualNP.RiffleRank.RiffleRankLe r (PEqualNP.RiffleRank.pairId X F) → PEqualNP.RiffleRank.RiffleRankLe s (PEqualNP.RiffleRank.pairId Y F) → PEqualNP.RiffleRank.RiffleRankLe (r * s) (PEqualNP.RiffleRank.pairId (X × Y) F) :=
  fun _ _ _ _ _ _ _ _ hX hY => PEqualNP.Gct.Riffle.rank_prod hX hY
