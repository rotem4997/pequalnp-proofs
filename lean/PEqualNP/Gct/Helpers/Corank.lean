import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DimCount

/-! The corank-one reduction for determinants of matrices of polynomials.

Jacobi's formula for the derivative of a determinant, the rank-one form of the adjugate of a
singular matrix with nonzero adjugate, and their combination: at a zero of `det A` where some
partial derivative of `det A` does not vanish, the evaluated matrix has one-dimensional left and
right kernels spanned by `v` and `u`, and every partial derivative of `det A` there is
`v ⬝ᵥ (∂_k A) *ᵥ u`. -/

namespace PEqualNP.Gct.Helpers

open Finset Matrix

/-- The product rule for a derivation over a finite product. -/
theorem derivation_prod {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq ι]
    (D : Derivation R S S) (s : Finset ι) (f : ι → S) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, erase_insert ha, smul_eq_mul,
      smul_eq_mul, mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [erase_insert_of_ne hia.symm, prod_insert (fun h => ha (mem_of_mem_erase h)), mul_assoc]

/-- A derivation applied to a determinant is the trace of the adjugate times the entrywise
derivative. -/
theorem derivation_det {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    (D : Derivation R S S) (A : Matrix (Fin n) (Fin n) S) :
    D A.det = Matrix.trace (A.adjugate * A.map D) := by
  have h1 : D A.det = ∑ i, (A.updateCol i fun j => D (A j i)).det := by
    simp only [det_apply', map_sum]
    rw [sum_comm]
    refine sum_congr rfl fun σ _ => ?_
    rw [Derivation.leibniz, derivation_prod]
    have : D ((Equiv.Perm.sign σ : ℤ) : S) = 0 := by
      rw [← zsmul_one, map_zsmul]; simp
    rw [this, smul_zero, add_zero, smul_eq_mul, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_prod_erase univ _ (mem_univ i), updateCol_self]
    congr 1
    rw [mul_comm]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [updateCol_ne (ne_of_mem_erase hj)]
  rw [h1, Matrix.trace]
  refine sum_congr rfl fun i _ => ?_
  rw [← cramer_apply, cramer_eq_adjugate_mulVec]
  rfl

/-- Jacobi's formula at a point. -/
theorem eval_pderiv_det {n d : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ))
    (x : Fin d → ℂ) (k : Fin d) :
    MvPolynomial.eval x (MvPolynomial.pderiv k A.det) =
      Matrix.trace ((A.map (MvPolynomial.eval x)).adjugate *
        ((A.map (MvPolynomial.pderiv k)).map (MvPolynomial.eval x))) := by
  have h := RingHom.map_adjugate (MvPolynomial.eval x) A
  simp only [RingHom.mapMatrix_apply] at h
  rw [derivation_det, ← h, ← Matrix.map_mul]
  exact AddMonoidHom.map_trace (MvPolynomial.eval x).toAddMonoidHom _

/-- A singular matrix with nonzero adjugate has adjugate of rank one, `adj M = u vᵀ`, with `u`
in the right kernel and `v` in the left kernel. -/
theorem adjugate_rank_one_of_det_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hdet : M.det = 0)
    (hadj : M.adjugate ≠ 0) :
    ∃ u v : Fin n → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ M *ᵥ u = 0 ∧ v ᵥ* M = 0 ∧
      M.adjugate = Matrix.vecMulVec u v := by
  classical
  have hMadj : M * M.adjugate = 0 := by rw [mul_adjugate, hdet, zero_smul]
  have hadjM : M.adjugate * M = 0 := by rw [adjugate_mul, hdet, zero_smul]
  have hcol : ∀ j, M *ᵥ (fun i => M.adjugate i j) = 0 := by
    intro j
    funext i
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hMadj i) j
  obtain ⟨i0, j0, hij⟩ : ∃ i j, M.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hadj (Matrix.ext h)
  set u : Fin n → ℂ := fun i => M.adjugate i j0 with hu
  have hu0 : u ≠ 0 := fun h => hij (congrFun h i0)
  have hMu : M *ᵥ u = 0 := hcol j0
  obtain ⟨g, hg⟩ := finrank_le_one_iff.mp (ker_finrank_le_one M hadj)
  have hmem : ∀ j, (fun i => M.adjugate i j) ∈ LinearMap.ker M.mulVecLin := by
    intro j; simpa using hcol j
  obtain ⟨a, ha⟩ := hg ⟨u, hmem j0⟩
  have ha' : a • (g : Fin n → ℂ) = u := congrArg Subtype.val ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← ha', zero_smul])
  choose b hb using fun j => hg ⟨_, hmem j⟩
  have hb' : ∀ j, b j • (g : Fin n → ℂ) = fun i => M.adjugate i j :=
    fun j => congrArg Subtype.val (hb j)
  set v : Fin n → ℂ := fun j => b j / a with hv
  have hEq : M.adjugate = Matrix.vecMulVec u v := by
    ext i j
    have := congrFun (hb' j) i
    rw [vecMulVec_apply, ← this, ← ha', hv]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hv0 : v ≠ 0 := by
    rintro h
    apply hadj
    rw [hEq, h]
    ext i j
    simp [vecMulVec_apply]
  refine ⟨u, v, hu0, hv0, hMu, ?_, hEq⟩
  have h2 : Matrix.vecMulVec u (v ᵥ* M) = 0 := by
    rw [← vecMulVec_mul, ← hEq, hadjM]
  funext j
  have := congrFun (congrFun h2 i0) j
  rw [vecMulVec_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hij

/-- The corank-one reduction: at a zero of `det A` where some partial derivative of `det A` is
nonzero, the kernels of `A(x)` are spanned by nonzero `u` and `v`, and the gradient of `det A`
there is `k ↦ v ⬝ᵥ (∂_k A)(x) *ᵥ u`. -/
theorem nondeg_zero_corank_one {n d : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ))
    (x : Fin d → ℂ) (h0 : MvPolynomial.eval x A.det = 0)
    (h1 : ∃ k, MvPolynomial.eval x (MvPolynomial.pderiv k A.det) ≠ 0) :
    ∃ u v : Fin n → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ (A.map (MvPolynomial.eval x)) *ᵥ u = 0 ∧
      v ᵥ* (A.map (MvPolynomial.eval x)) = 0 ∧
      ∀ k, MvPolynomial.eval x (MvPolynomial.pderiv k A.det) =
        v ⬝ᵥ (((A.map (MvPolynomial.pderiv k)).map (MvPolynomial.eval x)) *ᵥ u) := by
  have hdet : (A.map (MvPolynomial.eval x)).det = 0 := by
    rw [← h0, RingHom.map_det]; rfl
  have hadj : (A.map (MvPolynomial.eval x)).adjugate ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := h1
    apply hk
    rw [eval_pderiv_det, h, Matrix.zero_mul, Matrix.trace_zero]
  obtain ⟨u, v, hu, hv, hMu, hvM, hEq⟩ := adjugate_rank_one_of_det_zero _ hdet hadj
  refine ⟨u, v, hu, hv, hMu, hvM, fun k => ?_⟩
  rw [eval_pderiv_det, hEq, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]

end PEqualNP.Gct.Helpers
