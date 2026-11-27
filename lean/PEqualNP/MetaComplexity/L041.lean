import PEqualNP.MetaComplexity.Helpers.LocalMajority

/-- Every table is easy: in a 1-local reduction of parity to partial MCSP of fixed format on at
least three input bits, every input, odd or even, has a function of circuit size at most
`3 * s + 4` consistent with its table (the majority of the witnesses of three odd neighbours). -/
theorem PEqualNP.MetaComplexity.L041 : ∀ (n n' s : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), 3 ≤ n → PEqualNP.MetaComplexity.QueryLocal n 1 w → (∀ x : Fin n → Bool, w x = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n') → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → ∀ x : Fin n → Bool, ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' (T x) f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f (3 * s + 4) :=
  PEqualNP.MetaComplexity.Helpers.LocalMajority.maj_witness
