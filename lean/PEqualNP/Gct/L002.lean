import PEqualNP.Defs

/-! L-gct-002: a determinantal expression of size `n` pads to one of size `n + 1`, by adding a
diagonal entry `1` (the block matrix `[[A, 0], [0, 1]]`, reindexed to `Fin (n + 1)`). -/

theorem PEqualNP.Gct.L002 :
    ∀ (σ R : Type) [CommRing R] (p : MvPolynomial σ R) (n : ℕ),
      PEqualNP.Gct.HasDetExpression p n → PEqualNP.Gct.HasDetExpression p (n + 1) := by
  intro σ R _ p n ⟨A, hA, hdet⟩
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) (MvPolynomial σ R))), ?_, ?_⟩
  · intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
    · simpa using hA i j
    · simp
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs <;> simp
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, hdet]
