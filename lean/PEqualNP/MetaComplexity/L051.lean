import PEqualNP.MetaComplexity.Helpers.LocalWitness

/-- The hypotheses of L-meta-036 are satisfiable for every 3q < n. -/
theorem PEqualNP.MetaComplexity.L051 : ∀ n q : ℕ, 0 < q → 3 * q < n → ∃ (M : ℕ) (w : (Fin n → Bool) → List Bool), PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length ≤ M) ∧ (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) ∧ ∃ (n' : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate ((n + q - 1) / q - 1) true ++ false :: PEqualNP.MetaComplexity.encodePartial T ∧ T.length = 2 ^ n' :=
  PEqualNP.MetaComplexity.Helpers.LocalWitness.local_witness_explicit
