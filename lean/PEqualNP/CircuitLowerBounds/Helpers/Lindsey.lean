import Mathlib

/-!
Helpers for L-clb-016 (Lindsey's lemma): the sign matrix of inner product modulo two on
`n + n` bits has orthogonal rows, so its sum over any rectangle `A × B` is at most
`sqrt (|A| |B| 2 ^ n)` in absolute value.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

/-- The sign of inner product modulo two: `-1` to the number of common true positions. -/
def ipSign (n : ℕ) (x y : Fin n → Bool) : ℤ :=
  (-1) ^ (univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card

theorem ipSign_eq_prod (n : ℕ) (x y : Fin n → Bool) :
    ipSign n x y = ∏ i : Fin n, (if x i = true ∧ y i = true then (-1 : ℤ) else 1) := by
  unfold ipSign
  rw [Finset.prod_ite]
  simp

theorem ipSign_sq (n : ℕ) (x y : Fin n → Bool) : ipSign n x y * ipSign n x y = 1 := by
  unfold ipSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem ipSign_orth (n : ℕ) (y y' : Fin n → Bool) :
    ∑ x : Fin n → Bool, ipSign n x y * ipSign n x y' = if y = y' then (2 : ℤ) ^ n else 0 := by
  have h1 : ∀ x : Fin n → Bool, ipSign n x y * ipSign n x y' =
      ∏ i : Fin n, ((if x i = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if x i = true ∧ y' i = true then (-1 : ℤ) else 1)) := by
    intro x
    rw [ipSign_eq_prod, ipSign_eq_prod, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool))
    (fun (i : Fin n) (b : Bool) => (if b = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if b = true ∧ y' i = true then (-1 : ℤ) else 1))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∀ i : Fin n, (∑ b : Bool, (if b = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if b = true ∧ y' i = true then (-1 : ℤ) else 1)) = if y i = y' i then 2 else 0 := by
    intro i
    cases y i <;> cases y' i <;> simp
  simp_rw [h3]
  rw [Finset.prod_ite_zero]
  by_cases h : y = y'
  · subst h; simp
  · have : ¬ ∀ i ∈ (univ : Finset (Fin n)), y i = y' i :=
      fun hh => h (funext fun i => hh i (mem_univ i))
    rw [if_neg this, if_neg h]

/-- Lindsey's lemma. -/
theorem lindsey (n : ℕ) (A B : Finset (Fin n → Bool)) :
    (∑ x ∈ A, ∑ y ∈ B, ipSign n x y) ^ 2 ≤ (A.card : ℤ) * (B.card : ℤ) * 2 ^ n := by
  have h1 : (∑ x ∈ A, ∑ y ∈ B, ipSign n x y) ^ 2 ≤
      (A.card : ℤ) * ∑ x ∈ A, (∑ y ∈ B, ipSign n x y) ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ x ∈ A, (∑ y ∈ B, ipSign n x y) ^ 2 ≤
      ∑ x : Fin n → Bool, (∑ y ∈ B, ipSign n x y) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun _ _ _ => sq_nonneg _)
  have h3 : ∑ x : Fin n → Bool, (∑ y ∈ B, ipSign n x y) ^ 2 = (B.card : ℤ) * 2 ^ n := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ y ∈ B, ∑ x : Fin n → Bool, ∑ y' ∈ B, ipSign n x y * ipSign n x y' = 2 ^ n := by
      intro y hy
      rw [Finset.sum_comm]
      simp_rw [ipSign_orth]
      simp [hy]
    rw [Finset.sum_congr rfl this]
    simp
  calc (∑ x ∈ A, ∑ y ∈ B, ipSign n x y) ^ 2
      ≤ (A.card : ℤ) * ∑ x ∈ A, (∑ y ∈ B, ipSign n x y) ^ 2 := h1
    _ ≤ (A.card : ℤ) * ((B.card : ℤ) * 2 ^ n) := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3.le) (by positivity)
    _ = (A.card : ℤ) * (B.card : ℤ) * 2 ^ n := by ring

end PEqualNP.CircuitLowerBounds.Helpers
