import PEqualNP.Gct.Helpers.RankOne

/-- Injection form of the subpermanent sums: `k!` times the sum of all `k × k` subpermanents of `t`
is the sum over pairs of injections of the product of the entries. -/
theorem PEqualNP.Gct.L088 : ∀ (n k : ℕ) (t : Fin n × Fin n → ℂ), (k.factorial : ℂ) * (∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k}, Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))) = ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a) :=
  fun n k t => PEqualNP.Gct.Helpers.RankOne.injForm n k t
