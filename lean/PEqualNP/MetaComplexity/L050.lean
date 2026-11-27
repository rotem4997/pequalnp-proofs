import PEqualNP.MetaComplexity.Helpers.LocalWitness

/-- The construction of L-meta-035 with its fixed format exposed. -/
theorem PEqualNP.MetaComplexity.L050 : ∀ n q : ℕ, 0 < n → 0 < q → ∃ (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, w x = List.replicate ((n + q - 1) / q - 1) true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ (2 * ((n + q - 1) / q))) ∧ ∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP :=
  PEqualNP.MetaComplexity.Helpers.LocalWitness.fixed_format
