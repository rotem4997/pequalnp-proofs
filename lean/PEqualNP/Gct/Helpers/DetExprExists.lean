import PEqualNP.Defs
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Every polynomial has a determinantal expression

Non-vacuity witness for the determinantal complexity lower bounds: every multivariate polynomial
over a commutative ring is the determinant of a square matrix with affine entries, in
particular the permanent `perm_m` for every `m`.

The proof goes through an inverse free form of an algebraic branching program. `IsABP p` says
there are a finite index type `ι`, a matrix `A` over `ι` with affine entries and determinant
`1`, an affine row `u`, a constant column `v` and a column `w` with `A *ᵥ w = v` and
`u ⬝ᵥ w = p` (so `p = u A⁻¹ v`). This predicate holds for affine polynomials and is closed under
sums and products, hence holds for every polynomial; and `p` is the determinant of the bordered
matrix `[[A, v], [-u, 0]]`.
-/

namespace PEqualNP.Gct.Helpers.DetExprExists

open MvPolynomial Matrix

variable {σ R : Type} [CommRing R]

/-- Inverse free branching program form: `p = u A⁻¹ v` with `A` affine of determinant one, `u`
affine and `v` constant. The column `w` plays the role of `A⁻¹ v`. -/
def IsABP (p : MvPolynomial σ R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (A : Matrix ι ι (MvPolynomial σ R))
    (u w : ι → MvPolynomial σ R) (v : ι → R),
    (∀ i j, (A i j).totalDegree ≤ 1) ∧ (∀ i, (u i).totalDegree ≤ 1) ∧ A.det = 1 ∧
      A *ᵥ w = (fun i => C (v i)) ∧ u ⬝ᵥ w = p

theorem totalDegree_X_le_one (i : σ) : (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  simpa [MvPolynomial.X] using
    MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R)

theorem totalDegree_one_apply_le {ι : Type} [DecidableEq ι] (i j : ι) :
    ((1 : Matrix ι ι (MvPolynomial σ R)) i j).totalDegree ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- An affine polynomial is a branching program of size one. -/
theorem isABP_of_affine (q : MvPolynomial σ R) (hq : q.totalDegree ≤ 1) : IsABP q := by
  refine ⟨Unit, inferInstance, inferInstance, 1, fun _ => q, fun _ => 1, fun _ => 1, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro i j
    exact totalDegree_one_apply_le i j
  · intro _
    exact hq
  · simp
  · ext i
    simp
  · simp [dotProduct]

/-- Parallel composition: sums. -/
theorem IsABP.add {p q : MvPolynomial σ R} (hp : IsABP p) (hq : IsABP q) : IsABP (p + q) := by
  obtain ⟨ι₁, hF₁, hD₁, A₁, u₁, w₁, v₁, hA₁, hu₁, hdet₁, hw₁, hp⟩ := hp
  obtain ⟨ι₂, hF₂, hD₂, A₂, u₂, w₂, v₂, hA₂, hu₂, hdet₂, hw₂, hq⟩ := hq
  refine ⟨ι₁ ⊕ ι₂, inferInstance, inferInstance, Matrix.fromBlocks A₁ 0 0 A₂, Sum.elim u₁ u₂,
    Sum.elim w₁ w₂, Sum.elim v₁ v₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · simpa using hA₁ i j
    · simp
    · simp
    · simpa using hA₂ i j
  · rintro (i | i)
    · simpa using hu₁ i
    · simpa using hu₂ i
  · rw [Matrix.det_fromBlocks_zero₂₁, hdet₁, hdet₂, mul_one]
  · rw [Matrix.fromBlocks_mulVec]
    funext i
    rcases i with i | i
    · have := congrFun hw₁ i
      simpa using this
    · have := congrFun hw₂ i
      simpa using this
  · rw [← hp, ← hq]
    simp [dotProduct, Fintype.sum_sum_type]

/-- Series composition: products. -/
theorem IsABP.mul {p q : MvPolynomial σ R} (hp : IsABP p) (hq : IsABP q) : IsABP (p * q) := by
  obtain ⟨ι₁, hF₁, hD₁, A₁, u₁, w₁, v₁, hA₁, hu₁, hdet₁, hw₁, hp⟩ := hp
  obtain ⟨ι₂, hF₂, hD₂, A₂, u₂, w₂, v₂, hA₂, hu₂, hdet₂, hw₂, hq⟩ := hq
  refine ⟨ι₁ ⊕ ι₂, inferInstance, inferInstance,
    Matrix.fromBlocks A₁ (Matrix.of fun i j => -(C (v₁ i) * u₂ j)) 0 A₂,
    Sum.elim u₁ (fun _ => 0), Sum.elim (fun i => q * w₁ i) w₂, Sum.elim (fun _ => 0) v₂,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · simpa using hA₁ i j
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.of_apply, MvPolynomial.totalDegree_neg]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact hu₂ j
    · simp
    · simpa using hA₂ i j
  · rintro (i | i)
    · simpa using hu₁ i
    · simp
  · rw [Matrix.det_fromBlocks_zero₂₁, hdet₁, hdet₂, mul_one]
  · rw [Matrix.fromBlocks_mulVec]
    funext i
    rcases i with i | i
    · have h1 := congrFun hw₁ i
      simp only [Matrix.mulVec, dotProduct] at h1
      have h2 : ∑ j, u₂ j * w₂ j = q := hq
      simp only [Sum.elim_inl, Pi.add_apply, Matrix.mulVec, dotProduct, Function.comp_apply,
        Sum.elim_inr, Matrix.of_apply, map_zero]
      have e1 : ∑ x, A₁ i x * (q * w₁ x) = q * C (v₁ i) := by
        rw [← h1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      have e2 : ∑ x, -(C (v₁ i) * u₂ x) * w₂ x = -(C (v₁ i) * q) := by
        rw [← h2, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [e1, e2]
      ring
    · have := congrFun hw₂ i
      simpa using this
  · rw [← hp]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, add_zero, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- Every polynomial is a branching program. -/
theorem isABP_of_any (p : MvPolynomial σ R) : IsABP p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact isABP_of_affine _ (by simp)
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (isABP_of_affine _ (totalDegree_X_le_one i))

/-- A branching program is a determinant of a bordered affine matrix. -/
theorem IsABP.hasDetExpression {p : MvPolynomial σ R} (hp : IsABP p) :
    ∃ n : ℕ, PEqualNP.Gct.HasDetExpression p n := by
  obtain ⟨ι, hF, hD, A, u, w, v, hA, hu, hdet, hw, hp⟩ := hp
  let M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) (MvPolynomial σ R) :=
    Matrix.fromBlocks A (Matrix.of fun i _ => C (v i)) (Matrix.of fun _ j => -u j) 0
  let U : Matrix (ι ⊕ Unit) (ι ⊕ Unit) (MvPolynomial σ R) :=
    Matrix.fromBlocks 1 (Matrix.of fun i _ => -w i) 0 1
  let T : Matrix (ι ⊕ Unit) (ι ⊕ Unit) (MvPolynomial σ R) :=
    Matrix.fromBlocks A 0 (Matrix.of fun _ j => -u j) (Matrix.of fun _ _ => p)
  have hMU : M * U = T := by
    simp only [M, U, T, Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · ext i j
      have h1 := congrFun hw i
      simp only [Matrix.mulVec, dotProduct] at h1
      simp [Matrix.mul_apply, h1]
    · simp
    · ext i j
      have h2 : ∑ j, u j * w j = p := hp
      simp [Matrix.mul_apply, h2]
  have hU : U.det = 1 := by
    simp only [U]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
  have hT : T.det = p := by
    simp only [T]
    rw [Matrix.det_fromBlocks_zero₁₂, hdet, one_mul, Matrix.det_unique]
    rfl
  have hM : M.det = p := by
    rw [← hT, ← hMU, Matrix.det_mul, hU, mul_one]
  let e := Fintype.equivFin (ι ⊕ Unit)
  refine ⟨Fintype.card (ι ⊕ Unit), Matrix.reindex e e M, ?_, ?_⟩
  · intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases e.symm i with i | i <;> rcases e.symm j with j | j
    · simpa [M] using hA i j
    · simp [M]
    · simpa [M] using hu j
    · simp [M]
  · rw [Matrix.det_reindex_self, hM]

/-- Every polynomial over a commutative ring, in any set of variables, is the determinant of a
square matrix with affine entries. -/
theorem hasDetExpression_of_any (σ R : Type) [CommRing R] (p : MvPolynomial σ R) :
    ∃ n : ℕ, PEqualNP.Gct.HasDetExpression p n :=
  (isABP_of_any p).hasDetExpression

/-- The permanent has a determinantal expression of some size, for every `m`. -/
theorem perm_hasDetExpression :
    ∀ m : ℕ, ∃ n : ℕ, PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n :=
  fun _ => hasDetExpression_of_any _ _ _

end PEqualNP.Gct.Helpers.DetExprExists
