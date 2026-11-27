import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_189_aux

open Finset

private def rowPart (x : Fin 3 → ℂ) : Fin 4 → ℂ :=
  Fin.lastCases (-∑ j, x j) x

private lemma rowPart_last (x : Fin 3 → ℂ) : rowPart x (Fin.last 3) = -∑ j, x j :=
  Fin.lastCases_last

private lemma rowPart_castSucc (x : Fin 3 → ℂ) (j : Fin 3) : rowPart x j.castSucc = x j := by
  simp [rowPart]

private lemma sum_rowPart (x : Fin 3 → ℂ) : ∑ j : Fin 4, rowPart x j = 0 := by
  rw [Fin.sum_univ_castSucc, rowPart_last]
  simp only [rowPart_castSucc, add_neg_cancel]

private def pt (x : Fin 3 → ℂ) (y : Fin 4 → ℂ) : Fin 5 × Fin 5 → ℂ :=
  fun p => Fin.cases (Fin.cases (-∑ i, y i) (rowPart x) p.2)
    (fun i => Fin.cases (y i) (fun _ => 0) p.2) p.1

private lemma pt_zero_zero (x : Fin 3 → ℂ) (y : Fin 4 → ℂ) :
    pt x y (0, 0) = -∑ i, y i := rfl

private lemma pt_zero_succ (x : Fin 3 → ℂ) (y : Fin 4 → ℂ) (j : Fin 4) :
    pt x y (0, j.succ) = rowPart x j := rfl

private lemma pt_succ_zero (x : Fin 3 → ℂ) (y : Fin 4 → ℂ) (i : Fin 4) :
    pt x y (i.succ, 0) = y i := rfl

private lemma pt_succ_succ (x : Fin 3 → ℂ) (y : Fin 4 → ℂ) (i j : Fin 4) :
    pt x y (i.succ, j.succ) = 0 := rfl

private def ptLin : ((Fin 3 → ℂ) × (Fin 4 → ℂ)) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ) where
  toFun v := pt v.1 v.2
  map_add' v w := by
    funext ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp [pt_zero_zero, sum_add_distrib]; ring
      · intro j
        simp only [Pi.add_apply, Prod.fst_add, pt_zero_succ]
        refine Fin.lastCases ?_ ?_ j
        · simp only [rowPart_last, Pi.add_apply, sum_add_distrib]; ring
        · intro j; simp only [rowPart_castSucc, Pi.add_apply]
    · intro i
      refine Fin.cases ?_ ?_ j
      · simp [pt_succ_zero]
      · intro j; simp [pt_succ_succ]
  map_smul' c v := by
    funext ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp [pt_zero_zero, mul_sum]
      · intro j
        simp only [Pi.smul_apply, Prod.smul_fst, smul_eq_mul, pt_zero_succ]
        refine Fin.lastCases ?_ ?_ j
        · simp only [rowPart_last, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [← mul_sum]; ring
        · intro j; simp only [rowPart_castSucc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · intro i
      refine Fin.cases ?_ ?_ j
      · simp [pt_succ_zero]
      · intro j; simp [pt_succ_succ]

private lemma ptLin_injective : Function.Injective ptLin := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' : pt x y = pt x' y' := h
  have hx : x = x' := by
    funext j
    have := congrFun h' (0, j.castSucc.succ)
    simpa only [pt_zero_succ, rowPart_castSucc] using this
  have hy : y = y' := by
    funext i
    have := congrFun h' (i.succ, 0)
    simpa [pt_succ_zero] using this
  rw [hx, hy]

private noncomputable def embEquivPerm : (Fin 5 ↪ Fin 5) ≃ Equiv.Perm (Fin 5) where
  toFun f := Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective)
  invFun σ := σ.toEmbedding
  left_inv f := by ext i; rfl
  right_inv σ := by ext i; rfl

private lemma sum_perm4_eval (g : Fin 4 → ℂ) (j : Fin 4) :
    (∑ τ : Equiv.Perm (Fin 4), g (τ.symm j)) = 6 * ∑ i : Fin 4, g i := by
  have h1 : (∑ τ : Equiv.Perm (Fin 4), g (τ.symm j)) =
      ∑ σ : Equiv.Perm (Fin 4), g (σ j) :=
    Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin 4))) (fun σ => g (σ j))
  have h2 : (∑ σ : Equiv.Perm (Fin 4), g (σ j)) =
      ∑ σ : Equiv.Perm (Fin 4), g (σ 0) := by
    refine (Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin 4) j))
      (fun σ => g (σ j))).symm.trans ?_
    refine sum_congr rfl fun σ _ => ?_
    simp
  rw [h1, h2, ← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, sum_const, card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_sum]
  norm_num

private lemma eval_emb_pt (x : Fin 3 → ℂ) (y : Fin 4 → ℂ) :
    (∑ f : Fin 5 ↪ Fin 5, ∏ i : Fin 5, (1 + pt x y (i, f i))) = 120 := by
  rw [← Equiv.sum_comp embEquivPerm.symm]
  change (∑ σ : Equiv.Perm (Fin 5), ∏ i : Fin 5, (1 + pt x y (i, σ i))) = 120
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have h0 : (∑ τ : Equiv.Perm (Fin 4),
      ∏ i : Fin 5, (1 + pt x y (i, Equiv.Perm.decomposeFin.symm (0, τ) i))) =
      24 * (1 - ∑ i : Fin 4, y i) := by
    have hterm : ∀ τ : Equiv.Perm (Fin 4),
        (∏ i : Fin 5, (1 + pt x y (i, Equiv.Perm.decomposeFin.symm (0, τ) i))) =
          1 - ∑ i : Fin 4, y i := by
      intro τ
      rw [Fin.prod_univ_succ]
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
        pt_zero_zero, pt_succ_succ, add_zero, prod_const_one, mul_one]
      ring
    simp_rw [hterm]
    simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hsucc : ∀ j : Fin 4,
      (∑ τ : Equiv.Perm (Fin 4),
        ∏ i : Fin 5, (1 + pt x y (i, Equiv.Perm.decomposeFin.symm (j.succ, τ) i))) =
        (1 + rowPart x j) * (6 * (4 + ∑ i : Fin 4, y i)) := by
    intro j
    have hterm : ∀ τ : Equiv.Perm (Fin 4),
        (∏ i : Fin 5, (1 + pt x y (i, Equiv.Perm.decomposeFin.symm (j.succ, τ) i))) =
          (1 + rowPart x j) * (1 + y (τ.symm j)) := by
      intro τ
      rw [Fin.prod_univ_succ]
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ, pt_zero_succ]
      congr 1
      rw [prod_eq_single (τ.symm j)]
      · simp [pt_succ_zero]
      · intro i _ hi
        have hne : τ i ≠ j := fun h => hi (by rw [← h]; simp)
        have h1 : (τ i).succ ≠ 0 := Fin.succ_ne_zero _
        have h2 : (τ i).succ ≠ j.succ := fun h => hne (Fin.succ_injective _ h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, pt_succ_succ, add_zero]
      · intro h
        exact absurd (mem_univ _) h
    simp_rw [hterm, ← mul_sum, sum_perm4_eval (fun i => 1 + y i) j, sum_add_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  rw [h0]
  simp_rw [hsucc, ← sum_mul, sum_add_distrib, sum_rowPart]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, add_zero]
  norm_num
  ring

theorem witness :
    ∃ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) ∧
      Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range ptLin, ?_, ?_⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact eval_emb_pt x y
  · rw [LinearMap.finrank_range_of_inj ptLin_injective, Module.finrank_prod,
      Module.finrank_fin_fun, Module.finrank_fin_fun]

end PEqualNP.Outside.L_gct_189_aux

theorem PEqualNP.Outside.L_gct_189 : ∃ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) ∧ Module.finrank ℂ L = 7 :=
  PEqualNP.Outside.L_gct_189_aux.witness
