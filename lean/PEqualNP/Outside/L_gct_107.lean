import Mathlib
import PEqualNP.Defs

open scoped BigOperators

theorem PEqualNP.Outside.L_gct_107 : ∀ (p q : ℕ) (u u' : Fin p → ℂ) (w w' : Fin q → ℂ), (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else (u i * w j) * (u' k * w' l)) = ((∑ i, u i) * (∑ i, u' i) - ∑ i, u i * u' i) * ((∑ j, w j) * (∑ j, w' j) - ∑ j, w j * w' j) := by
  intro p q u u' w w'
  classical
  have offDiagonal {n : ℕ} (f g : Fin n → ℂ) :
      (∑ i, ∑ k, if i = k then 0 else f i * g k) =
        (∑ i, f i) * (∑ i, g i) - ∑ i, f i * g i := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    have split (k : Fin n) :
        (if i = k then 0 else f i * g k) =
          f i * g k - (if i = k then f i * g k else 0) := by
      by_cases h : i = k <;> simp [h]
    simp only [split, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← offDiagonal u u', ← offDiagonal w w']
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]
  ring
