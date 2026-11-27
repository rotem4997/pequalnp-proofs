import PEqualNP.Library.Universal.BruteForce

/-- Every language in NP is decidable in exponential time `2 ^ (n ^ k) + k` for some `k`. -/
theorem PEqualNP.Library.L014 : ∀ L ∈ PEqualNP.Library.NP, ∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k) :=
  fun L hL => PEqualNP.Library.Universal.np_subset_exp L hL
