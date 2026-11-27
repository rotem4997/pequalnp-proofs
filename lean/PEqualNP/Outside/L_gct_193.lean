import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_193 :
    ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  have sumPerm4 : ∀ (f : Equiv.Perm (Fin 4) → ℂ), ∑ σ, f σ =
      ∑ a : Fin 4, ∑ b : Fin 3, ∑ c : Fin 2, ∑ d : Fin 1,
        f (Equiv.Perm.decomposeFin.symm (a, Equiv.Perm.decomposeFin.symm (b,
          Equiv.Perm.decomposeFin.symm (c, Equiv.Perm.decomposeFin.symm (d, 1))))) := by
    intro f
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fintype.sum_unique]
    rfl
  have key : ∀ F : ℕ → ℕ → ℕ → ℕ → ℂ,
      ∑ σ : Equiv.Perm (Fin 4), F (σ 0).val (σ 1).val (σ 2).val (σ 3).val =
      (((F 0 1 2 3 + F 0 1 3 2) + ((F 0 2 1 3 + F 0 2 3 1) + (F 0 3 2 1 + F 0 3 1 2))) + (((F 1 0 2 3 + F 1 0 3 2) + ((F 1 2 0 3 + F 1 2 3 0) + (F 1 3 2 0 + F 1 3 0 2))) + (((F 2 1 0 3 + F 2 1 3 0) + ((F 2 0 1 3 + F 2 0 3 1) + (F 2 3 0 1 + F 2 3 1 0))) + ((F 3 1 2 0 + F 3 1 0 2) + ((F 3 2 1 0 + F 3 2 0 1) + (F 3 0 2 1 + F 3 0 1 2)))))) := by
    intro F
    rw [sumPerm4]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  intro c
  let T : Fin 4 → ℕ → ℂ := fun i s =>
    1 + c * (if s = i.val then (1 : ℂ) else if s = (i.val + 1) % 4 then Complex.I
      else if s = (i.val + 2) % 4 then -Complex.I else -1)
  show ∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, T i (σ i).val = 24
  simp only [Fin.prod_univ_four]
  rw [key (fun a b d e => T 0 a * T 1 b * T 2 d * T 3 e)]
  have t00 : T 0 0 = 1 + c * (1) := by simp only [T]; norm_num
  have t01 : T 0 1 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t02 : T 0 2 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t03 : T 0 3 = 1 + c * (-1) := by simp only [T]; norm_num
  have t10 : T 1 0 = 1 + c * (-1) := by simp only [T]; norm_num
  have t11 : T 1 1 = 1 + c * (1) := by simp only [T]; norm_num
  have t12 : T 1 2 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t13 : T 1 3 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t20 : T 2 0 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t21 : T 2 1 = 1 + c * (-1) := by simp only [T]; norm_num
  have t22 : T 2 2 = 1 + c * (1) := by simp only [T]; norm_num
  have t23 : T 2 3 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t30 : T 3 0 = 1 + c * (Complex.I) := by simp only [T]; norm_num
  have t31 : T 3 1 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t32 : T 3 2 = 1 + c * (-1) := by simp only [T]; norm_num
  have t33 : T 3 3 = 1 + c * (1) := by simp only [T]; norm_num
  simp only [t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33]
  linear_combination (2*c^4*Complex.I^2 - 8*c^4*Complex.I + 2*c^4 + 8*c^2) * Complex.I_sq
