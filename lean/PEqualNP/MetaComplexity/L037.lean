import PEqualNP.MetaComplexity.Helpers.NaturalAll

/-- If MCSP is in P, no language in P is an exponentially secure pseudorandom function family
against fan-in two circuits: `L-meta-034` composed with `L-lib-086`. -/
theorem PEqualNP.MetaComplexity.L037 : PEqualNP.MetaComplexity.MCSP ∈ PEqualNP.Library.P → ¬ (∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ PEqualNP.Library.P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 2 ^ (n / k) → |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) - (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) :=
  PEqualNP.MetaComplexity.Helpers.NaturalAll.no_prf_of_mcsp
