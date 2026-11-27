import PEqualNP.MetaComplexity.Helpers.SparseCore

/-- The sparse partial MCSP instance of a set family is a member exactly when the family has a
hitting set of size at most `s + 1`. -/
theorem PEqualNP.MetaComplexity.L047 : ∀ (n : ℕ) (F : List (Finset (Fin n))) (s : ℕ), List.replicate s true ++ false :: (List.replicate n true ++ false :: PEqualNP.MetaComplexity.encodeRows n (((fun _ : Fin n => false), false) :: F.map fun S : Finset (Fin n) => ((fun i : Fin n => decide (i ∈ S)), true))) ∈ PEqualNP.MetaComplexity.SparsePartialMCSP ↔ ∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ s + 1 :=
  PEqualNP.MetaComplexity.Helpers.Sparse.sparse_hitting_iff
