import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_106_aux

open Finset

/-- Three-index inclusion-exclusion for the sum over pairwise distinct indices. -/
lemma key {ι : Type*} [Fintype ι] [DecidableEq ι] (x y z : ι → ℂ) :
    ∑ a, ∑ b, ∑ c, (if a = b ∨ a = c ∨ b = c then (0:ℂ) else 1) * (x a * y b * z c) =
      (∑ a, x a) * (∑ b, y b) * (∑ c, z c) - (∑ a, x a * y a) * (∑ c, z c)
        - (∑ a, x a * z a) * (∑ b, y b) - (∑ b, y b * z b) * (∑ a, x a)
        + 2 * ∑ a, x a * y a * z a := by
  have e : ∀ a b c, (if a = b ∨ a = c ∨ b = c then (0:ℂ) else 1) * (x a * y b * z c) =
      x a * y b * z c - (if a = b then x a * y a * z c else 0)
        - (if a = c then x a * y b * z a else 0) - (if b = c then x a * y b * z b else 0)
        + (if a = b then (if a = c then 2 * (x a * y a * z a) else 0) else 0) := by
    intro a b c
    by_cases h1 : a = b <;> by_cases h2 : a = c <;> by_cases h3 : b = c <;> subst_vars <;>
      simp_all <;> ring
  simp only [e, sum_add_distrib, sum_sub_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq,
    mem_univ, ite_true]
  have h0 : ∑ a, ∑ b, ∑ c, x a * y b * z c = (∑ a, x a) * (∑ b, y b) * (∑ c, z c) := by
    rw [sum_mul_sum, sum_mul_sum]
    simp only [sum_mul]
    exact sum_congr rfl fun a _ => sum_comm
  have h1 : ∑ a, ∑ c, x a * y a * z c = (∑ a, x a * y a) * (∑ c, z c) := by
    rw [sum_mul_sum]
  have h2 : ∑ a, ∑ b, x a * y b * z a = (∑ a, x a * z a) * (∑ b, y b) := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have h3 : ∑ a, ∑ b, x a * y b * z b = (∑ b, y b * z b) * (∑ a, x a) := by
    rw [sum_mul_sum]
    symm
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [h0, h1, h2, h3, ← mul_sum]

end PEqualNP.Outside.L_gct_106_aux

open Finset in
theorem PEqualNP.Outside.L_gct_106 : ∀ (p q : ℕ) (t : Fin p → Fin q → ℂ), (∀ i, ∑ j, t i j = 0) → (∀ j, ∑ i, t i j = 0) → (∑ i, ∑ k, ∑ m, ∑ j, ∑ l, ∑ n, if i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n then 0 else t i j * t k l * t m n) = 4 * ∑ i, ∑ j, t i j ^ 3 := by
  intro p q t hrow hcol
  have hsplit : ∀ i k m j l n,
      (if i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n then (0:ℂ) else t i j * t k l * t m n)
        = (if i = k ∨ i = m ∨ k = m then (0:ℂ) else 1) *
          ((if j = l ∨ j = n ∨ l = n then (0:ℂ) else 1) * (t i j * t k l * t m n)) := by
    intro i k m j l n
    by_cases hA : (i = k ∨ i = m ∨ k = m)
    · have h : (i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n) := by tauto
      rw [if_pos h, if_pos hA, zero_mul]
    · by_cases hB : (j = l ∨ j = n ∨ l = n)
      · have h : (i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n) := by tauto
        rw [if_pos h, if_neg hA, if_pos hB, zero_mul, mul_zero]
      · have h : ¬(i = k ∨ i = m ∨ k = m ∨ j = l ∨ j = n ∨ l = n) := by tauto
        rw [if_neg h, if_neg hA, if_neg hB, one_mul, one_mul]
  have inner : ∀ i k m, (∑ j, ∑ l, ∑ n,
      (if j = l ∨ j = n ∨ l = n then (0:ℂ) else 1) * (t i j * t k l * t m n))
        = 2 * ∑ j, t i j * t k j * t m j := by
    intro i k m
    rw [PEqualNP.Outside.L_gct_106_aux.key (t i) (t k) (t m)]
    simp [hrow]
  have outer : ∀ j, (∑ i, ∑ k, ∑ m,
      (if i = k ∨ i = m ∨ k = m then (0:ℂ) else 1) * (t i j * t k j * t m j))
        = 2 * ∑ i, t i j ^ 3 := by
    intro j
    rw [PEqualNP.Outside.L_gct_106_aux.key (fun i => t i j) (fun i => t i j) (fun i => t i j)]
    simp only [hcol j, mul_zero, sub_zero, zero_add]
    congr 1
    exact sum_congr rfl fun i _ => by ring
  simp only [hsplit, ← mul_sum, inner]
  calc (∑ i, ∑ k, ∑ m, (if i = k ∨ i = m ∨ k = m then (0:ℂ) else 1) *
          (2 * ∑ j, t i j * t k j * t m j))
      = ∑ i, ∑ k, ∑ m, ∑ j, 2 * ((if i = k ∨ i = m ∨ k = m then (0:ℂ) else 1) *
          (t i j * t k j * t m j)) := by
        simp only [mul_sum]
        exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => sum_congr rfl fun m _ =>
          sum_congr rfl fun j _ => by ring
    _ = ∑ j, ∑ i, ∑ k, ∑ m, 2 * ((if i = k ∨ i = m ∨ k = m then (0:ℂ) else 1) *
          (t i j * t k j * t m j)) := by
        conv_lhs => enter [2, i, 2, k]; rw [sum_comm]
        conv_lhs => enter [2, i]; rw [sum_comm]
        rw [sum_comm]
    _ = ∑ j, 2 * (2 * ∑ i, t i j ^ 3) := by
        simp only [← mul_sum, outer]
    _ = 4 * ∑ i, ∑ j, t i j ^ 3 := by
        rw [sum_comm (f := fun i j => t i j ^ 3), mul_sum]
        exact sum_congr rfl fun j _ => by ring
