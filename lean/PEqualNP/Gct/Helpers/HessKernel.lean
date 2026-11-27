import Mathlib

/-! The linear algebra behind L-gct-013: the Hessian of the permanent at the point of
Mignon and Ressayre has trivial kernel. Stated on an arbitrary array `V`. -/

namespace PEqualNP.Gct.Helpers

open Finset

theorem sum_sum_ite_fst {N : ℕ} (f : Fin N → Fin N → ℂ) (i : Fin N) :
    (∑ x, ∑ y, if x = i then f x y else 0) = ∑ y, f i y := by
  rw [sum_comm]; simp

theorem sum_sum_ite_both {N : ℕ} (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    (∑ x, ∑ y, if x = i then (if y = j then f x y else 0) else 0) = f i j := by
  rw [sum_comm]; simp

theorem sum_sum_ne_ne {N : ℕ} (V : Fin N → Fin N → ℂ) (i j : Fin N) :
    (∑ k, ∑ l, if k ≠ i ∧ l ≠ j then V k l else 0) =
      (∑ k, ∑ l, V k l) - ∑ l, V i l - ∑ k, V k j + V i j := by
  have : ∀ k l, (if k ≠ i ∧ l ≠ j then V k l else 0) =
      V k l - (if k = i then V k l else 0) - (if l = j then V k l else 0) +
        (if k = i then (if l = j then V k l else 0) else 0) := by
    intro k l
    by_cases hk : k = i <;> by_cases hl : l = j <;> simp [hk, hl]
  simp only [this, sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]
  simp only [sum_sum_ite_fst, sum_sum_ite_both, sum_ite_eq', mem_univ, if_true]

theorem sum_sum_ne4 {N : ℕ} (V : Fin (N + 1) → Fin (N + 1) → ℂ) (i j : Fin (N + 1))
    (hi : i ≠ 0) (hj : j ≠ 0) :
    (∑ k, ∑ l, if k ≠ i ∧ k ≠ 0 ∧ l ≠ j ∧ l ≠ 0 then V k l else 0) =
      (∑ k, ∑ l, V k l) - ∑ l, V i l - ∑ l, V 0 l - ∑ k, V k j - ∑ k, V k 0 +
        V i j + V i 0 + V 0 j + V 0 0 := by
  have : ∀ k l, (if k ≠ i ∧ k ≠ 0 ∧ l ≠ j ∧ l ≠ 0 then V k l else 0) =
      V k l - (if k = i then V k l else 0) - (if k = 0 then V k l else 0)
        - (if l = j then V k l else 0) - (if l = 0 then V k l else 0)
        + (if k = i then (if l = j then V k l else 0) else 0)
        + (if k = i then (if l = 0 then V k l else 0) else 0)
        + (if k = 0 then (if l = j then V k l else 0) else 0)
        + (if k = 0 then (if l = 0 then V k l else 0) else 0) := by
    intro k l
    by_cases hk : k = i <;> by_cases hk0 : k = 0 <;> by_cases hl : l = j <;>
      by_cases hl0 : l = 0 <;> simp_all
  simp only [this, sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]
  simp only [sum_sum_ite_fst, sum_sum_ite_both, sum_ite_eq', mem_univ, if_true]

theorem sum_erase_zero {N : ℕ} (f : Fin (N + 1) → ℂ) :
    ∑ j ∈ univ.erase 0, f j = ∑ j, f j - f 0 :=
  sum_erase_eq_sub (mem_univ 0)

theorem hess_kernel (n : ℕ) (α β : ℂ) (hα : α ≠ 0) (hαβ : α ≠ β)
    (V : Fin (n + 2) → Fin (n + 2) → ℂ)
    (h : ∀ i j, α * (∑ k, ∑ l, if k ≠ i ∧ l ≠ j then V k l else 0) -
      (if i ≠ 0 ∧ j ≠ 0 then
        β * (∑ k, ∑ l, if k ≠ i ∧ k ≠ 0 ∧ l ≠ j ∧ l ≠ 0 then V k l else 0) else 0) = 0) :
    ∀ i j, V i j = 0 := by
  set S := ∑ k, ∑ l, V k l with hS
  set R : Fin (n + 2) → ℂ := fun k => ∑ l, V k l with hR
  set C : Fin (n + 2) → ℂ := fun l => ∑ k, V k l with hC
  have hSR : ∑ k, R k = S := rfl
  have hSC : ∑ l, C l = S := by simp only [hC, hS]; exact sum_comm
  have hN : ((n + 2 : ℕ) : ℂ) - 1 ≠ 0 := by
    push_cast; intro e; have : (n : ℂ) + 1 = 0 := by linear_combination e
    exact absurd this (by exact_mod_cast Nat.succ_ne_zero n)
  -- equations on the borders
  have E : ∀ i j, (i = 0 ∨ j = 0) → S - R i - C j + V i j = 0 := by
    intro i j hij
    have := h i j
    rw [if_neg (by tauto), sum_sum_ne_ne, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hα
  have hR0 : R 0 = S := by
    have hsum : ∑ j, (S - R 0 - C j + V 0 j) = 0 := sum_eq_zero fun j _ => E 0 j (Or.inl rfl)
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, hSC] at hsum
    have : (((n + 2 : ℕ) : ℂ) - 1) * (S - R 0) = 0 := by
      have hr : ∑ j, V 0 j = R 0 := rfl
      rw [hr] at hsum; push_cast at hsum ⊢; linear_combination hsum
    have := (mul_eq_zero.mp this).resolve_left hN
    linear_combination -this
  have hC0 : C 0 = S := by
    have hsum : ∑ i, (S - R i - C 0 + V i 0) = 0 := sum_eq_zero fun i _ => E i 0 (Or.inr rfl)
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, hSR] at hsum
    have : (((n + 2 : ℕ) : ℂ) - 1) * (S - C 0) = 0 := by
      have hc : ∑ i, V i 0 = C 0 := rfl
      rw [hc] at hsum; push_cast at hsum ⊢; linear_combination hsum
    have := (mul_eq_zero.mp this).resolve_left hN
    linear_combination -this
  have hcard : #(univ.erase (0 : Fin (n + 2))) = n + 1 := by simp
  have hV0j : ∀ j, V 0 j = C j := fun j => by
    linear_combination E 0 j (Or.inl rfl) + hR0
  have hVi0 : ∀ i, V i 0 = R i := fun i => by
    linear_combination E i 0 (Or.inr rfl) + hC0
  -- interior equations
  have I : ∀ i j, i ≠ 0 → j ≠ 0 → α * (S - R i - C j + V i j) - β * V i j = 0 := by
    intro i j hi hj
    have := h i j
    rw [if_pos ⟨hi, hj⟩, sum_sum_ne_ne, sum_sum_ne4 V i j hi hj] at this
    have e1 := hV0j j; have e2 := hVi0 i; have e3 := hV0j 0
    simp only [← hR, ← hC] at this ⊢
    change α * (S - R i - C j + V i j) - β * (S - R i - R 0 - C j - C 0 + V i j + V i 0 +
      V 0 j + V 0 0) = 0 at this
    rw [e1, e2, e3, hR0, hC0] at this
    linear_combination this
  have hRi : ∀ i, R i = S := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hR0]
    have hsum : ∑ j ∈ univ.erase 0, (α * (S - R i - C j + V i j) - β * V i j) = 0 :=
      sum_eq_zero fun j hj => I i j hi (ne_of_mem_erase hj)
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_erase_zero, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, hSC, hC0, hVi0, hcard] at hsum
    have hr : ∑ j, V i j = R i := rfl
    rw [hr] at hsum
    have : (α * (((n + 2 : ℕ) : ℂ) - 1)) * (S - R i) = 0 := by
      push_cast at hsum ⊢; linear_combination hsum
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero hα hN)
    linear_combination -this
  have hCj : ∀ j, C j = S := by
    intro j
    by_cases hj : j = 0
    · rw [hj, hC0]
    have hsum : ∑ i ∈ univ.erase 0, (α * (S - R i - C j + V i j) - β * V i j) = 0 :=
      sum_eq_zero fun i hi => I i j (ne_of_mem_erase hi) hj
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_erase_zero, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, hSR, hR0, hV0j, hcard] at hsum
    have hc : ∑ i, V i j = C j := rfl
    rw [hc] at hsum
    have : (α * (((n + 2 : ℕ) : ℂ) - 1)) * (S - C j) = 0 := by
      push_cast at hsum ⊢; linear_combination hsum
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero hα hN)
    linear_combination -this
  have hS0 : S = 0 := by
    have : ∑ k, R k = ∑ _k : Fin (n + 2), S := sum_congr rfl fun k _ => hRi k
    rw [hSR, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have h2 : (((n + 2 : ℕ) : ℂ) - 1) * S = 0 := by linear_combination -this
    exact (mul_eq_zero.mp h2).resolve_left hN
  intro i j
  by_cases hi : i = 0
  · rw [hi, hV0j, hCj, hS0]
  by_cases hj : j = 0
  · rw [hj, hVi0, hRi, hS0]
  have := I i j hi hj
  rw [hRi, hCj, hS0] at this
  have : (α - β) * V i j = 0 := by linear_combination this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hαβ)

end PEqualNP.Gct.Helpers
