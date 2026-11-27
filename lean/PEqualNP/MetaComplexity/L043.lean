import PEqualNP.MetaComplexity.Helpers.LocalMajorityQ

/-- Every table is easy: in a `q`-local reduction of parity to partial MCSP of fixed format on at
least `4 * q + 1` input bits, every input, odd or even, has a function of circuit size at most
`(4 * q + 1) * s + 3 * (4 * q + 1) ^ 2` consistent with its table (at least `2 * q + 1` of the
witnesses of `4 * q + 1` odd neighbours). -/
theorem PEqualNP.MetaComplexity.L043 : ∀ (n n' s q : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), 0 < q → 4 * q + 1 ≤ n → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, w x = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n') → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → ∀ x : Fin n → Bool, ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' (T x) f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f ((4 * q + 1) * s + 3 * (4 * q + 1) ^ 2) :=
  PEqualNP.MetaComplexity.Helpers.LocalMajorityQ.majq_witness
