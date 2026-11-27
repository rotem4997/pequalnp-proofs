import PEqualNP.Gct.Helpers.MincExpansion

/-- Expansion of the permanent of the all-ones matrix plus `t` in the sums of subpermanents of
`t`: `perm(J + t) = ∑ k, (n - k)! * M_k(t)` (see Minc, Permanents, 1978). -/
theorem PEqualNP.Gct.L084 : ∀ (n : ℕ) (t : Fin n × Fin n → ℂ), MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) * ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k}, Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j)) :=
  PEqualNP.Gct.Helpers.Minc.minc_expansion
