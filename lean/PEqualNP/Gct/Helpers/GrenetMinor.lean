import PEqualNP.Defs.Gct
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Helper module, proofs only. An entry of the adjugate of a square matrix with affine entries
has a determinantal expression of size one less than the matrix: it is, up to a sign, the
determinant of a minor, and the sign is absorbed in one row. -/

namespace PEqualNP.Gct.Helpers.Grenet

open MvPolynomial

/-- Negating one row: the negative of a polynomial with a determinantal expression of positive
size has one of the same size. -/
theorem hasDetExpression_neg {σ R : Type} [CommRing R] {n : ℕ} (hn : 0 < n)
    {p : MvPolynomial σ R} (h : HasDetExpression p n) : HasDetExpression (-p) n := by
  obtain ⟨A, hA, rfl⟩ := h
  refine ⟨A.updateRow ⟨0, hn⟩ ((-1 : MvPolynomial σ R) • A ⟨0, hn⟩), ?_, ?_⟩
  · intro i j
    by_cases h : i = ⟨0, hn⟩
    · subst h
      simp only [Matrix.updateRow_self, neg_one_smul, Pi.neg_apply, totalDegree_neg]
      exact hA _ _
    · rw [Matrix.updateRow_ne h]
      exact hA _ _
  · rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
    ring

/-- A matrix whose row `i` is the unit vector at `j` has determinant the signed minor. -/
theorem det_eq_of_row_single {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (i j : Fin (n + 1))
    (h : ∀ k, M i k = if k = j then 1 else 0) :
    M.det = (-1) ^ (i + j : ℕ) * (M.submatrix i.succAbove j.succAbove).det := by
  rw [Matrix.det_succ_row M i, Finset.sum_eq_single j]
  · rw [h]
    simp
  · intro k _ hk
    simp [h, hk]
  · simp

/-- An entry of the adjugate of a square matrix of size `n + 1` with affine entries has a
determinantal expression of size `n`, for `n` positive. -/
theorem hasDetExpression_adjugate {σ R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) (hcard : Fintype.card ι = n + 1)
    (B : Matrix ι ι (MvPolynomial σ R)) (hB : ∀ a b, (B a b).totalDegree ≤ 1) (i j : ι) :
    HasDetExpression (B.adjugate i j) n := by
  let e : ι ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcard
  set M := (B.updateRow j (Pi.single i 1)).submatrix e.symm e.symm with hM
  have hdet : B.adjugate i j = M.det := by
    rw [Matrix.adjugate_apply, hM, Matrix.det_submatrix_equiv_self]
  have hrow : ∀ k, M (e j) k = if k = e i then 1 else 0 := by
    intro k
    simp [hM, Pi.single_apply, Equiv.symm_apply_eq]
  have hexp : HasDetExpression (M.submatrix (e j).succAbove (e i).succAbove).det n := by
    refine ⟨_, ?_, rfl⟩
    intro a b
    have hne : e.symm ((e j).succAbove a) ≠ j := by
      intro h
      exact Fin.succAbove_ne (e j) a (e.symm_apply_eq.mp h)
    simp only [hM, Matrix.submatrix_apply, Matrix.updateRow_ne hne]
    exact hB _ _
  rw [hdet, det_eq_of_row_single M _ _ hrow]
  rcases neg_one_pow_eq_or (MvPolynomial σ R) ((e j : ℕ) + (e i : ℕ)) with h | h
  · rw [h, one_mul]
    exact hexp
  · rw [h, neg_one_mul]
    exact hasDetExpression_neg hn hexp

end PEqualNP.Gct.Helpers.Grenet
