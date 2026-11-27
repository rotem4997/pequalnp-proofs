import Mathlib

/-! Helper for L-gct-062: sums over pairwise distinct indices, and the second and third order
distinct sums of a matrix whose row and column sums all vanish. -/

namespace PEqualNP.Gct.SigmaRed

open Finset

theorem sum_ne_pair {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ℂ) :
    ∑ x, ∑ y, (if x ≠ y then f x * g y else 0) = (∑ x, f x) * (∑ y, g y) - ∑ x, f x * g x := by
  have key : ∀ x y, (if x ≠ y then f x * g y else 0)
      = f x * g y - (if x = y then f x * g y else 0) := by
    intro x y; by_cases h : x = y <;> simp [h]
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_mul_sum]
  simp

theorem sum_ne_triple {ι : Type} [Fintype ι] [DecidableEq ι] (f g h : ι → ℂ) :
    ∑ x, ∑ y, ∑ z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then f x * g y * h z else 0) =
      (∑ x, f x) * (∑ x, g x) * (∑ x, h x) - (∑ x, f x * g x) * (∑ x, h x)
        - (∑ x, f x * h x) * (∑ x, g x) - (∑ x, g x * h x) * (∑ x, f x)
        + 2 * ∑ x, f x * g x * h x := by
  have key : ∀ x y z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then f x * g y * h z else 0)
      = f x * g y * h z - (if x = y then f x * g y else 0) * h z
        - (if x = z then f x * h z else 0) * g y - (if y = z then g y * h z else 0) * f x
        + 2 * (if x = y then (if x = z then f x * g y * h z else 0) else 0) := by
    intro x y z
    by_cases hxy : x = y <;> by_cases hxz : x = z <;> by_cases hyz : y = z <;>
      simp_all <;> ring
  simp_rw [key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : ∑ x, ∑ y, ∑ z, f x * g y * h z = (∑ x, f x) * (∑ x, g x) * (∑ x, h x) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hB : ∑ x, ∑ y, ∑ z, (if x = y then f x * g y else 0) * h z
      = (∑ x, f x * g x) * (∑ x, h x) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    simp
  have hC : ∑ x, ∑ y, ∑ z, (if x = z then f x * h z else 0) * g y
      = (∑ x, f x * h x) * (∑ x, g x) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    simp
  have hD : ∑ x, ∑ y, ∑ z, (if y = z then g y * h z else 0) * f x
      = (∑ x, g x * h x) * (∑ x, f x) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    simp
  have hE : ∑ x, ∑ y, ∑ z, 2 * (if x = y then (if x = z then f x * g y * h z else 0) else 0)
      = 2 * ∑ x, f x * g x * h x := by
    simp only [← Finset.mul_sum]
    simp
  rw [hA, hB, hC, hD, hE]

theorem rot3 {ι : Type} [Fintype ι] (F : ι → ι → ι → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc _ = ∑ a, ∑ c, ∑ b, F a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem rot4 {ι : Type} [Fintype ι] (F : ι → ι → ι → ι → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := by
  calc _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := Finset.sum_congr rfl fun a _ => rot3 (F a)
    _ = _ := Finset.sum_comm

theorem perm5 {ι : Type} [Fintype ι] (F : ι → ι → ι → ι → ι → ℂ) :
    ∑ j1, ∑ i2, ∑ j2, ∑ i3, ∑ j3, F j1 i2 j2 i3 j3
      = ∑ i2, ∑ i3, ∑ j1, ∑ j2, ∑ j3, F j1 i2 j2 i3 j3 := by
  calc _ = ∑ i2, ∑ j1, ∑ j2, ∑ i3, ∑ j3, F j1 i2 j2 i3 j3 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i2 _ =>
      rot3 (fun j1 j2 i3 => ∑ j3, F j1 i2 j2 i3 j3)

theorem centred_two {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι × ι → ℂ)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    ∑ a, ∑ b, (if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then t a * t b else 0) = ∑ a, t a ^ 2 := by
  have step1 : ∑ a : ι × ι, ∑ b : ι × ι, (if a.1 ≠ b.1 ∧ a.2 ≠ b.2 then t a * t b else 0)
      = ∑ i1, ∑ i2, if i1 ≠ i2 then
          ∑ j1, ∑ j2, (if j1 ≠ j2 then t (i1, j1) * t (i2, j2) else 0) else 0 := by
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i2 _ => ?_
    by_cases h : i1 = i2 <;> simp [h]
  have step2 : ∀ i1 i2, ∑ j1, ∑ j2, (if j1 ≠ j2 then t (i1, j1) * t (i2, j2) else 0)
      = -∑ j, t (i1, j) * t (i2, j) := by
    intro i1 i2
    rw [sum_ne_pair]
    simp [hr]
  have step3 : ∀ i1 i2 : ι, (if i1 ≠ i2 then -∑ j, t (i1, j) * t (i2, j) else 0)
      = -∑ j, (if i1 ≠ i2 then t (i1, j) * t (i2, j) else 0) := by
    intro i1 i2; by_cases h : i1 = i2 <;> simp [h]
  rw [step1]
  simp_rw [step2, step3, Finset.sum_neg_distrib]
  have swap : ∑ i1 : ι, ∑ i2 : ι, ∑ j : ι, (if i1 ≠ i2 then t (i1, j) * t (i2, j) else 0)
      = ∑ j, ∑ i1, ∑ i2, (if i1 ≠ i2 then t (i1, j) * t (i2, j) else 0) := by
    exact rot3 (fun i1 i2 j => if i1 ≠ i2 then t (i1, j) * t (i2, j) else 0)
  rw [swap]
  simp_rw [sum_ne_pair, hc]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [pow_two]

theorem centred_three {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι × ι → ℂ)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    ∑ a, ∑ b, ∑ c, (if (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1) ∧ (a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2)
      then t a * t b * t c else 0) = 4 * ∑ a, t a ^ 3 := by
  have step1 : ∑ a : ι × ι, ∑ b : ι × ι, ∑ c : ι × ι,
      (if (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1) ∧ (a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2)
        then t a * t b * t c else 0)
      = ∑ i1, ∑ i2, ∑ i3, if i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
          ∑ j1, ∑ j2, ∑ j3, (if j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
            t (i1, j1) * t (i2, j2) * t (i3, j3) else 0) else 0 := by
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i1 _ => ?_
    rw [perm5]
    refine Finset.sum_congr rfl fun i2 _ => ?_
    refine Finset.sum_congr rfl fun i3 _ => ?_
    by_cases h12 : i1 = i2 <;> by_cases h13 : i1 = i3 <;> by_cases h23 : i2 = i3 <;>
      simp [h12, h13, h23]
  have step2 : ∀ i1 i2 i3, ∑ j1, ∑ j2, ∑ j3, (if j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
            t (i1, j1) * t (i2, j2) * t (i3, j3) else 0)
      = 2 * ∑ j, t (i1, j) * t (i2, j) * t (i3, j) := by
    intro i1 i2 i3
    rw [sum_ne_triple]
    simp [hr]
  have step3 : ∀ i1 i2 i3 : ι, (if i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
        2 * ∑ j, t (i1, j) * t (i2, j) * t (i3, j) else 0)
      = 2 * ∑ j, (if i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
        t (i1, j) * t (i2, j) * t (i3, j) else 0) := by
    intro i1 i2 i3; split_ifs <;> simp
  rw [step1]
  simp_rw [step2, step3, ← Finset.mul_sum]
  have swap : ∑ i1 : ι, ∑ i2 : ι, ∑ i3 : ι, ∑ j : ι, (if i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
        t (i1, j) * t (i2, j) * t (i3, j) else 0)
      = ∑ j, ∑ i1, ∑ i2, ∑ i3, (if i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
        t (i1, j) * t (i2, j) * t (i3, j) else 0) := by
    exact rot4 (fun i1 i2 i3 j => if i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
        t (i1, j) * t (i2, j) * t (i3, j) else 0)
  rw [swap]
  simp_rw [sum_ne_triple, hc]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [mul_zero, sub_zero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PEqualNP.Gct.SigmaRed
