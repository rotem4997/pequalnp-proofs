import PEqualNP.Defs

/-! Helpers for L-gct-044 (ceiling of the subspace method): row linearity of the permanent,
row scaling, and subspaces of matrices cut out row by row. -/

namespace PEqualNP.Gct.MethodCeiling

open Finset

variable {m : ℕ}

/-- The permanent as an expansion along row `r`. -/
theorem perm_updateRow_eq (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) (v : Fin m → ℂ) :
    (M.updateRow r v).permanent =
      ∑ σ : Equiv.Perm (Fin m), v (σ.symm r) * ∏ i ∈ univ.erase (σ.symm r), M (σ i) i := by
  unfold Matrix.permanent
  refine sum_congr rfl fun σ _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ (σ.symm r))]
  simp only [Equiv.apply_symm_apply, Matrix.updateRow_self]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  have hne : σ i ≠ r := by
    intro h
    exact (mem_erase.1 hi).1 (by rw [← h, Equiv.symm_apply_apply])
  rw [Matrix.updateRow_ne hne]

/-- The linear functional `v ↦ perm (M with row r replaced by v)`. -/
noncomputable def rowFun (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) : (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun v := (M.updateRow r v).permanent
  map_add' u v := by
    simp only [perm_updateRow_eq, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c v := by
    simp only [perm_updateRow_eq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum,
      mul_assoc]

theorem rowFun_apply (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) (v : Fin m → ℂ) :
    rowFun M r v = (M.updateRow r v).permanent := rfl

/-- A matrix with a zero row has zero permanent. -/
theorem perm_eq_zero_of_row (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) (h : ∀ j, M r j = 0) :
    M.permanent = 0 := by
  unfold Matrix.permanent
  refine sum_eq_zero fun σ _ => prod_eq_zero (mem_univ (σ.symm r)) ?_
  simp [h]

/-- Scaling the rows by `d` multiplies the permanent by `∏ d`. -/
theorem perm_rowScale (M : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) :
    (Matrix.of fun i j => d i * M i j).permanent = (∏ i, d i) * M.permanent := by
  unfold Matrix.permanent
  rw [mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp σ d

theorem eval_permPoly (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- The embedding of a family of row spaces into matrices. -/
noncomputable def rowEmb (S : Fin m → Submodule ℂ (Fin m → ℂ)) :
    (∀ i, S i) →ₗ[ℂ] (Fin m × Fin m → ℂ) :=
  LinearMap.pi fun p => LinearMap.proj p.2 ∘ₗ (S p.1).subtype ∘ₗ LinearMap.proj p.1

theorem rowEmb_apply (S : Fin m → Submodule ℂ (Fin m → ℂ)) (x : ∀ i, S i) (i j : Fin m) :
    rowEmb S x (i, j) = (x i : Fin m → ℂ) j := rfl

theorem rowEmb_injective (S : Fin m → Submodule ℂ (Fin m → ℂ)) :
    Function.Injective (rowEmb S) := by
  intro a b h
  funext i
  apply Subtype.ext
  funext j
  exact congrFun h (i, j)

theorem finrank_range_rowEmb (S : Fin m → Submodule ℂ (Fin m → ℂ)) :
    Module.finrank ℂ (LinearMap.range (rowEmb S)) = ∑ i, Module.finrank ℂ (S i) := by
  rw [LinearMap.finrank_range_of_inj (rowEmb_injective S), Module.finrank_pi_fintype]

theorem sum_lower (f : Fin m → ℕ) (r : Fin m) (a b : ℕ) (ha : ∀ i, i ≠ r → a ≤ f i)
    (hb : b ≤ f r) : (m - 1) * a + b ≤ ∑ i, f i := by
  rw [← add_sum_erase univ f (mem_univ r)]
  have h := card_nsmul_le_sum (univ.erase r) f a fun i hi => ha i (mem_erase.1 hi).1
  rw [card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin, smul_eq_mul] at h
  have h' : (m - 1) * a ≤ ∑ x ∈ univ.erase r, f x := h
  omega

end PEqualNP.Gct.MethodCeiling
