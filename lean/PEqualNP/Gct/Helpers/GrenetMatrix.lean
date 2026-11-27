import PEqualNP.Gct.Helpers.GrenetMinor
import PEqualNP.Gct.Helpers.GrenetPaths

/-! Helper module, proofs only. The subset graph matrix of Grenet (2011): vertices the subsets
of `Fin m`, an edge from `S` to `S ∪ {j}` of weight `w |S| j`. The row vector of path sums `f`
solves `f * (1 - N) = e_∅`, the matrix `1 - N` has determinant one, hence the path sum of the
full set is an entry of the adjugate of `1 - N`, and for the weights `x_{s, j}` it is the
permanent. -/

namespace PEqualNP.Gct.Helpers.Grenet

open Finset MvPolynomial

variable {A : Type*} [CommRing A] {m : ℕ}

/-- The weighted adjacency matrix of the subset graph. -/
def stepMatrix (w : ℕ → Fin m → A) : Matrix (Finset (Fin m)) (Finset (Fin m)) A :=
  fun S T => ∑ j ∈ T, if S = T.erase j then w S.card j else 0

/-- The row vector of path sums. -/
def pathVec (w : ℕ → Fin m → A) : Finset (Fin m) → A := fun S => pathSum w S.card S

theorem stepMatrix_eq_zero (w : ℕ → Fin m → A) {S T : Finset (Fin m)} (h : T.card ≤ S.card) :
    stepMatrix w S T = 0 := by
  refine Finset.sum_eq_zero fun j hj => if_neg ?_
  rintro rfl
  exact absurd (Finset.card_erase_lt_of_mem hj) (not_lt.mpr h)

theorem pathVec_vecMul_stepMatrix (w : ℕ → Fin m → A) (T : Finset (Fin m)) :
    (Matrix.vecMul (pathVec w) (stepMatrix w)) T =
      ∑ j ∈ T, pathVec w (T.erase j) * w (T.erase j).card j := by
  simp only [Matrix.vecMul, dotProduct, stepMatrix, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq' univ (T.erase j)]
  simp

theorem pathVec_vecMul (w : ℕ → Fin m → A) :
    Matrix.vecMul (pathVec w) (1 - stepMatrix w) = Pi.single ∅ 1 := by
  funext T
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply, pathVec_vecMul_stepMatrix]
  by_cases hT : T = ∅
  · subst hT
    simp [pathVec, pathSum_zero]
  · rw [Pi.single_apply, if_neg hT, sub_eq_zero]
    obtain ⟨s, hs⟩ : ∃ s, T.card = s + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by simpa using hT)
    simp only [pathVec]
    rw [hs, pathSum_succ]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : (T.erase j).card = s := by rw [Finset.card_erase_of_mem hj, hs]; rfl
    rw [this]

theorem det_one_sub_stepMatrix (w : ℕ → Fin m → A) : (1 - stepMatrix w).det = 1 := by
  have htri : Matrix.BlockTriangular (1 - stepMatrix w) Finset.card := by
    intro S T h
    have hne : S ≠ T := by
      rintro rfl
      exact lt_irrefl _ h
    simp [hne, stepMatrix_eq_zero w h.le]
  rw [htri.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (1 - stepMatrix w).toSquareBlock Finset.card a = 1 := by
    ext ⟨S, hS⟩ ⟨T, hT⟩
    have h0 : stepMatrix w S T = 0 := stepMatrix_eq_zero w (by rw [hS, hT])
    simp [Matrix.toSquareBlock_def, Matrix.one_apply, h0]
  rw [this, Matrix.det_one]

/-- The path sum of a set is an entry of the adjugate of `1 - N`. -/
theorem pathVec_eq_adjugate (w : ℕ → Fin m → A) (T : Finset (Fin m)) :
    pathVec w T = (1 - stepMatrix w).adjugate ∅ T := by
  have h := congrArg (fun v => Matrix.vecMul v (1 - stepMatrix w).adjugate) (pathVec_vecMul w)
  simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, det_one_sub_stepMatrix, one_smul,
    Matrix.vecMul_one, Matrix.single_one_vecMul] at h
  rw [h]
  rfl

/-- The weights of the permanent: `x_{s, j}` for `s < m`. -/
noncomputable def permWeight (R : Type) [CommRing R] (m : ℕ) :
    ℕ → Fin m → MvPolynomial (Fin m × Fin m) R :=
  fun s j => if h : s < m then X (⟨s, h⟩, j) else 0

theorem totalDegree_permWeight_le (R : Type) [CommRing R] (m s : ℕ) (j : Fin m) :
    (permWeight R m s j).totalDegree ≤ 1 := by
  unfold permWeight
  split_ifs with h
  · rcases subsingleton_or_nontrivial R with hR | hR
    · rw [Subsingleton.elim (X (⟨s, h⟩, j) : MvPolynomial (Fin m × Fin m) R) 0]
      simp
    · simp
  · simp

theorem pathVec_permWeight_univ (R : Type) [CommRing R] (m : ℕ) :
    pathVec (permWeight R m) univ = PEqualNP.Gct.permPoly R m := by
  have h := pathSum_eq_permanent (permWeight R m) m id Function.injective_id
  rw [Finset.image_id] at h
  simp only [pathVec, Finset.card_univ, Fintype.card_fin]
  rw [h, PEqualNP.Gct.permPoly]
  congr 1
  ext i k
  simp [permWeight, Matrix.mvPolynomialX]

theorem totalDegree_one_sub_stepMatrix_le (R : Type) [CommRing R] (m : ℕ)
    (S T : Finset (Fin m)) :
    ((1 - stepMatrix (permWeight R m)) S T).totalDegree ≤ 1 := by
  rw [Matrix.sub_apply]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · refine totalDegree_finsetSum_le fun j _ => ?_
    split_ifs
    · exact totalDegree_permWeight_le R m _ j
    · simp

/-- Grenet (2011): the permanent of size `m ≥ 1` has a determinantal expression of size
`2 ^ m - 1`. -/
theorem hasDetExpression_permPoly (R : Type) [CommRing R] (m : ℕ) (hm : 1 ≤ m) :
    PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly R m) (2 ^ m - 1) := by
  rw [← pathVec_permWeight_univ, pathVec_eq_adjugate]
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine hasDetExpression_adjugate (by omega) ?_ _
    (totalDegree_one_sub_stepMatrix_le R m) _ _
  rw [Fintype.card_finset, Fintype.card_fin]
  omega

end PEqualNP.Gct.Helpers.Grenet
