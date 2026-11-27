import PEqualNP.Gct.Helpers.Riffle

/-! L-gct-095: over every field, `pairId (Fin 2)` (the tensor square of the 2 by 2 identity) is
a sum of three riffle-basic functions. Proof: an explicit three-term identity,
`PEqualNP.Gct.Riffle.rank_fin_two`. -/

theorem PEqualNP.Gct.L095 : ∀ (F : Type) [Field F], PEqualNP.RiffleRank.RiffleRankLe 3 (PEqualNP.RiffleRank.pairId (Fin 2) F) :=
  fun _ _ => PEqualNP.Gct.Riffle.rank_fin_two
