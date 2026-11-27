import PEqualNP.MetaComplexity.Helpers.LocalLinear

/-- A 1-local reduction of parity on `n` bits to partial MCSP of fixed format, with size bound
`s` and tables of length `2 ^ n'`, has `n ≤ 2 ^ n'`, and its size bound is small unless the
table is much longer than the input: `s < (2 * (2 ^ n' - n) + 4) * (n' + 1) + 4`. -/
theorem PEqualNP.MetaComplexity.L049 : ∀ (n n' s : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), PEqualNP.MetaComplexity.QueryLocal n 1 w → (∀ x : Fin n → Bool, w x = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n') → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → n ≤ 2 ^ n' ∧ s < (2 * (2 ^ n' - n) + 4) * (n' + 1) + 4 :=
  PEqualNP.MetaComplexity.Helpers.LocalLinear.linear
