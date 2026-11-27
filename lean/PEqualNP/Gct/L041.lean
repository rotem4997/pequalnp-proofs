import PEqualNP.Gct.Helpers.PolarArith

/-- Arithmetic of the weighted count: if the count inequality holds at every test point, then
`(r - 1) * (h + 1) ≤ 11 * n`. -/
theorem PEqualNP.Gct.L041 :
    ∀ (h n r K : ℕ), 2 ≤ r → (r - 1) ^ (h + 1) ≤ K → (∀ p q : ℕ, K * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) → (r - 1) * (h + 1) ≤ 11 * n :=
  fun h n r K hr hK hyp => PEqualNP.Gct.Helpers.polar_arith h n r K hr hK hyp
