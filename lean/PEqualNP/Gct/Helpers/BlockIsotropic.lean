import PEqualNP.Defs
import PEqualNP.Gct.Helpers.MethodCeiling

/-! Helper module for L-gct-055, proofs only. A linear space of `3 × 3` matrices on which the
permanent stays constant along the all ones matrix is totally isotropic for the polar form of
the quadratic part of the permanent at that point; the form is nondegenerate on the full
nine-dimensional space, so the space has dimension at most four. -/

namespace PEqualNP.Gct.Helpers.BlockIso

open Finset

/-- The permanent of a `3 × 3` matrix, written out. -/
theorem permanent_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0 := by
  have hu : (univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [Fin.prod_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.Perm.one_apply]
  simp
  ring

/-- The matrix of the polar form: the sum of the entries of `t` in a different row and a
different column, as a linear map. -/
noncomputable def cross : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun t := fun p => (∑ q, t q) - (∑ l, t (p.1, l)) - (∑ k, t (k, p.2)) + t p
  map_add' t u := by
    ext p
    simp only [Pi.add_apply, sum_add_distrib]
    ring
  map_smul' c t := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, RingHom.id_apply]
    ring

theorem cross_apply (t : Fin 3 × Fin 3 → ℂ) (p : Fin 3 × Fin 3) :
    cross t p = (∑ q, t q) - (∑ l, t (p.1, l)) - (∑ k, t (k, p.2)) + t p := rfl

/-- The polar form is nondegenerate on the whole space: `cross` is injective. -/
theorem cross_injective : Function.Injective cross := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h : ∀ p, cross t p = 0 := fun p => by rw [ht]; rfl
  have e := fun i j => h (i, j)
  simp only [cross_apply, Fintype.sum_prod_type, Fin.sum_univ_three] at e
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  ext ⟨i, j⟩
  simp only [Pi.zero_apply]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e00 + e01 + e02) / 2 - (e00 + e10 + e20) / 2 + e00
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e00 + e01 + e02) / 2 - (e01 + e11 + e21) / 2 + e01
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e00 + e01 + e02) / 2 - (e02 + e12 + e22) / 2 + e02
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e10 + e11 + e12) / 2 - (e00 + e10 + e20) / 2 + e10
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e10 + e11 + e12) / 2 - (e01 + e11 + e21) / 2 + e11
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e10 + e11 + e12) / 2 - (e02 + e12 + e22) / 2 + e12
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e20 + e21 + e22) / 2 - (e00 + e10 + e20) / 2 + e20
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e20 + e21 + e22) / 2 - (e01 + e11 + e21) / 2 + e21
  · linear_combination (e00 + e01 + e02 + e10 + e11 + e12 + e20 + e21 + e22) / 4 -
      (e20 + e21 + e22) / 2 - (e02 + e12 + e22) / 2 + e22

/-- A space on which the permanent stays `6` along the all ones matrix is totally isotropic for
the polar form. -/
theorem isotropic (W : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (h : ∀ t ∈ W, MvPolynomial.eval ((fun _ => (1 : ℂ)) + t) (PEqualNP.Gct.permPoly ℂ 3) = 6)
    (t u : Fin 3 × Fin 3 → ℂ) (ht : t ∈ W) (hu : u ∈ W) : ∑ p, cross t p * u p = 0 := by
  have h1 := h _ (W.add_mem ht hu)
  have h2 := h _ (W.neg_mem (W.add_mem ht hu))
  have h3 := h _ (W.sub_mem ht hu)
  have h4 := h _ (W.neg_mem (W.sub_mem ht hu))
  simp only [PEqualNP.Gct.MethodCeiling.eval_permPoly, permanent_three, Matrix.of_apply,
    Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h1 h2 h3 h4
  simp only [cross_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  linear_combination (h1 + h2 - h3 - h4) / 4

/-- The polar form as a map into the dual space: `t ↦ (u ↦ ∑ p, cross t p * u p)`. -/
noncomputable def polar : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 3 × Fin 3 → ℂ) :=
  LinearMap.mk₂ ℂ (fun t u => ∑ p, cross t p * u p)
    (fun t t' u => by simp only [map_add, Pi.add_apply, add_mul, sum_add_distrib])
    (fun c t u => by simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc])
    (fun t u u' => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c t u => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun p _ => by ring)

theorem polar_apply (t u : Fin 3 × Fin 3 → ℂ) : polar t u = ∑ p, cross t p * u p := rfl

theorem polar_injective : Function.Injective polar := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  apply cross_injective
  rw [map_zero]
  ext p
  have h : polar t (Pi.single p 1) = 0 := by rw [ht]; rfl
  rw [polar_apply] at h
  simpa [Pi.single_apply] using h

/-- A totally isotropic subspace for the polar form has dimension at most four. -/
theorem finrank_le_four (W : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (h : ∀ t ∈ W, ∀ u ∈ W, ∑ p, cross t p * u p = 0) : Module.finrank ℂ W ≤ 4 := by
  have hr : ∀ t : W, polar.domRestrict W t ∈ W.dualAnnihilator := fun t =>
    (Submodule.mem_dualAnnihilator _).2 fun u hu => h t t.2 u hu
  have hinj : Function.Injective ((polar.domRestrict W).codRestrict W.dualAnnihilator hr) :=
    fun a b hab => Subtype.ext (polar_injective (congrArg Subtype.val hab))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have h3 : Module.finrank ℂ (Fin 3 × Fin 3 → ℂ) = 9 := by
    rw [Module.finrank_fintype_fun_eq_card]; rfl
  omega

end PEqualNP.Gct.Helpers.BlockIso
