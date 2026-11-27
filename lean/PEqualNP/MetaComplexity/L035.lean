import PEqualNP.MetaComplexity.Helpers.LocalConstruct

/-- For every `n` and `q` at least one, some `q`-local map with outputs of length
`2 ^ (2 * ⌈n / q⌉ + 1) + ⌈n / q⌉` reduces parity on `n` bits to partial MCSP. -/
theorem PEqualNP.MetaComplexity.L035 : ∀ n q : ℕ, 0 < n → 0 < q → ∃ w : (Fin n → Bool) → List Bool, PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length = 2 ^ (2 * ((n + q - 1) / q) + 1) + (n + q - 1) / q) ∧ ∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP :=
  PEqualNP.MetaComplexity.Helpers.LocalConstruct.main
