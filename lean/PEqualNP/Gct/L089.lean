import PEqualNP.Gct.Helpers.RankOne

/-- The subpermanent sums of a rank-one matrix: `k!` times the elementary symmetric sums of the
two vectors. -/
theorem PEqualNP.Gct.L089 : ∀ (n k : ℕ) (x y : Fin n → ℂ), (∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k}, Matrix.permanent (Matrix.of fun i j : Fin k => x (S.1.orderEmbOfFin S.2 i) * y (T.1.orderEmbOfFin T.2 j))) = (k.factorial : ℂ) * (∑ S : {S : Finset (Fin n) // S.card = k}, ∏ i ∈ S.1, x i) * (∑ T : {T : Finset (Fin n) // T.card = k}, ∏ j ∈ T.1, y j) :=
  fun n k x y => PEqualNP.Gct.Helpers.RankOne.Mk_rankOne n k x y
