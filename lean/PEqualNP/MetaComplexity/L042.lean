import PEqualNP.MetaComplexity.Helpers.TotalConstruct

/-- For `n ≤ 4 q` some `q`-local map with outputs `1111 0 T`, `T` a table on three variables,
reduces parity on `n` bits to MCSP. -/
theorem PEqualNP.MetaComplexity.L042 : ∀ n q : ℕ, n ≤ 4 * q → ∃ w : (Fin n → Bool) → List Bool, PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length = 13) ∧ (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.MCSP) ∧ ∀ x : Fin n → Bool, ∃ T : List Bool, w x = List.replicate 4 true ++ false :: T ∧ T.length = 2 ^ 3 :=
  PEqualNP.MetaComplexity.Helpers.TotalConstruct.main
